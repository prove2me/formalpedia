-- Prove2me | solution 1 for ChenStein.Process.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T00:07:20.3581+00:00
-- url     : https://prove2.me/submissions/21926f3e-d5bf-4653-b5b5-92334ee3e038

-- Complete checked reconstruction of the native countable Chen–Stein process total-variation theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_ChenStein_Process_Setting
import Definitions.Def_TotalVariationDist
import Mathlib


-- Begin Canonical

-- End Canonical

-- Begin EventDistance

open MeasureTheory
open scoped ENNReal

namespace ChenStein.Process.Proof

lemma event_distance_le {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → E) (A : Set E) (D : Set Ω)
    (heq : ∀ ω, ω ∉ D → f ω = g ω) :
    ENNReal.ofReal |μ.real (f ⁻¹' A) - μ.real (g ⁻¹' A)| ≤ μ D := by
  classical
  have hfg : f ⁻¹' A ⊆ (g ⁻¹' A) ∪ D := by
    intro ω hω
    by_cases hd : ω ∈ D
    · exact Or.inr hd
    · exact Or.inl (by simpa only [Set.mem_preimage, ← heq ω hd] using hω)
  have hgf : g ⁻¹' A ⊆ (f ⁻¹' A) ∪ D := by
    intro ω hω
    by_cases hd : ω ∈ D
    · exact Or.inr hd
    · exact Or.inl (by simpa only [Set.mem_preimage, heq ω hd] using hω)
  have h1 := (measureReal_mono (μ := μ) hfg).trans (measureReal_union_le _ _)
  have h2 := (measureReal_mono (μ := μ) hgf).trans (measureReal_union_le _ _)
  calc
    _ ≤ ENNReal.ofReal (μ.real D) := ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith, by linarith⟩)
    _ = μ D := ofReal_measureReal

lemma ofReal_abs_sub_triangle (a b c d : ℝ) :
    ENNReal.ofReal |a - d| ≤
      ENNReal.ofReal |a - b| + ENNReal.ofReal |b - c| + ENNReal.ofReal |c - d| := by
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((abs_sub_le a c d).trans (by linarith [abs_sub_le a b c]))

end ChenStein.Process.Proof
-- End EventDistance

-- Begin ZeroPadding

open MeasureTheory
open scoped ENNReal

namespace ChenStein.Process.Proof

noncomputable def zeroPad {I : Type*} (F : Finset I) (z : F → ℕ) : I → ℕ := by
  classical
  exact fun i => if h : i ∈ F then z ⟨i, h⟩ else 0

lemma measurable_zeroPad {I : Type*} (F : Finset I) : Measurable (zeroPad F) := by
  classical
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ F
  · simpa only [zeroPad, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : F))
  · simpa only [zeroPad, dif_neg hi] using (measurable_const : Measurable (fun _ : F → ℕ => (0 : ℕ)))

lemma zeroPad_restrict_eq {I : Type*} (F : Finset I) (z : I → ℕ)
    (hz : ∀ i, i ∉ F → z i = 0) : zeroPad F (fun i => z i) = z := by
  classical
  funext i
  by_cases hi : i ∈ F
  · simp [zeroPad, hi]
  · simp [zeroPad, hi, hz i hi]

lemma zeroPad_event_distance {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℕ)
    (F : Finset I) (A : Set (I → ℕ)) :
    ENNReal.ofReal |μ.real ((Xproc X) ⁻¹' A) -
      μ.real ((fun ω => zeroPad F (fun i => X i ω)) ⁻¹' A)| ≤
      ∑' i : {i // i ∉ F}, μ {ω | X i ω ≠ 0} := by
  classical
  let D : Set Ω := ⋃ i : {i // i ∉ F}, {ω | X i ω ≠ 0}
  apply (event_distance_le μ (Xproc X) (fun ω => zeroPad F (fun i => X i ω)) A D ?_).trans
    (measure_iUnion_le _)
  intro ω hω
  apply Eq.symm
  apply zeroPad_restrict_eq F (fun i => X i ω)
  intro i hi
  by_contra hn
  exact hω (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hn⟩)

end ChenStein.Process.Proof
-- End ZeroPadding

-- Begin TailMass

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ChenStein.Process.Proof

noncomputable def tailMass {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : I → Ω → ℕ) (F : Finset I) : ℝ≥0∞ :=
  ∑' i : {i // i ∉ F}, ENNReal.ofReal (p P X i)

lemma tailMass_tendsto_zero {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : I → Ω → ℕ) {lam : ℝ} (hlam : HasSum (p P X) lam) :
    Tendsto (tailMass P X) atTop (𝓝 0) := by
  have hn : ∀ i, 0 ≤ p P X i := fun _ => measureReal_nonneg
  have ht : (∑' i, ENNReal.ofReal (p P X i)) = ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hlam.summable, hlam.tsum_eq]
  exact ENNReal.tendsto_tsum_compl_atTop_zero (ht ▸ ENNReal.ofReal_ne_top)

lemma bernoulli_nonzero_measure {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℕ)
    (hX01 : ∀ i ω, X i ω ≤ 1) (i : I) :
    P {ω | X i ω ≠ 0} = ENNReal.ofReal (p P X i) := by
  have he : {ω | X i ω ≠ 0} = {ω | X i ω = 1} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    have hx := hX01 i ω
    omega
  rw [he]
  exact (ofReal_measureReal (μ := P) (s := {ω | X i ω = 1})).symm

lemma poisson_nonzero_measure_le (r : ℝ≥0) :
    poissonMeasure r {n | n ≠ 0} ≤ ENNReal.ofReal (r : ℝ) := by
  have he : {n : ℕ | n ≠ 0} = ({0} : Set ℕ)ᶜ := by ext n; simp
  have hr : (poissonMeasure r).real {n | n ≠ 0} = 1 - Real.exp (-(r : ℝ)) := by
    rw [he, probReal_compl_eq_one_sub (measurableSet_singleton 0), poissonMeasure_real_singleton]
    simp
  rw [← ofReal_measureReal (μ := poissonMeasure r) (s := {n | n ≠ 0}), hr]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.add_one_le_exp (-(r : ℝ))]

lemma bernoulli_zeroPad_distance {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℕ)
    (hX01 : ∀ i ω, X i ω ≤ 1) (F : Finset I) (A : Set (I → ℕ)) :
    ENNReal.ofReal |P.real ((Xproc X) ⁻¹' A) -
      P.real ((fun ω => zeroPad F (fun i => X i ω)) ⁻¹' A)| ≤ tailMass P X F := by
  apply (zeroPad_event_distance P X F A).trans
  exact ENNReal.tsum_le_tsum (fun i => (bernoulli_nonzero_measure P X hX01 i).le)

lemma poisson_zeroPad_distance {Ω Ω' I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Countable I] (P : Measure Ω) (X : I → Ω → ℕ)
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : I → Ω' → ℕ)
    (hYm : ∀ i, Measurable (Y i))
    (hYlaw : ∀ i, P'.map (Y i) = poissonMeasure (p P X i).toNNReal)
    (F : Finset I) (A : Set (I → ℕ)) :
    ENNReal.ofReal |P'.real ((Xproc Y) ⁻¹' A) -
      P'.real ((fun ω => zeroPad F (fun i => Y i ω)) ⁻¹' A)| ≤ tailMass P X F := by
  apply (zeroPad_event_distance P' Y F A).trans
  apply ENNReal.tsum_le_tsum
  intro i
  have hm : MeasurableSet {n : ℕ | n ≠ 0} := by measurability
  have he := congrArg (fun μ : Measure ℕ => μ {n | n ≠ 0}) (hYlaw i)
  rw [Measure.map_apply (hYm i) hm] at he
  change P' {ω | Y i ω ≠ 0} = _ at he
  rw [he]
  have hpn : 0 ≤ p P X i := measureReal_nonneg
  simpa only [Real.coe_toNNReal _ hpn] using
    poisson_nonzero_measure_le (p P X i).toNNReal

end ChenStein.Process.Proof
-- End TailMass

-- Begin TVSupremum

open MeasureTheory
open scoped ENNReal

namespace ChenStein.Process.Proof

lemma ofReal_tv_le {E : Type*} [MeasurableSpace E] (μ ν : Measure E) {R : ℝ≥0∞}
    (h : ∀ A : Set E, MeasurableSet A → ENNReal.ofReal |(μ A).toReal - (ν A).toReal| ≤ R) :
    ENNReal.ofReal (MarkovChainCLT.tvDist μ ν) ≤ R := by
  by_cases hR : R = ⊤
  · simp [hR]
  apply (ENNReal.ofReal_le_iff_le_toReal hR).mpr
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro r ⟨A, hA, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hR).mp (h A hA)

lemma ofReal_twice_tv_le {E : Type*} [MeasurableSpace E] (μ ν : Measure E) {R : ℝ≥0∞}
    (h : ∀ A : Set E, MeasurableSet A → ENNReal.ofReal |(μ A).toReal - (ν A).toReal| ≤ R) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist μ ν) ≤ 2 * R := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  gcongr
  exact ofReal_tv_le μ ν h

end ChenStein.Process.Proof
-- End TVSupremum

-- Begin CountableTransfer

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ChenStein.Process.Proof

noncomputable def eventTest {E : Type*} (A : Set E) : E → ℝ :=
  A.indicator (fun _ => 1)

lemma eventTest_nonneg {E : Type*} (A : Set E) (x : E) : 0 ≤ eventTest A x := by
  classical
  by_cases hx : x ∈ A <;> simp [eventTest, hx]

lemma eventTest_le_one {E : Type*} (A : Set E) (x : E) : eventTest A x ≤ 1 := by
  classical
  by_cases hx : x ∈ A <;> simp [eventTest, hx]

lemma integral_eventTest {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (g : Ω → E) (hg : Measurable g) (A : Set E) (hA : MeasurableSet A) :
    (∫ ω, eventTest A (g ω) ∂μ) = μ.real (g ⁻¹' A) := by
  have he : (fun ω => eventTest A (g ω)) = (g ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    classical
    by_cases hω : g ω ∈ A <;> simp [eventTest, hω]
  rw [he, integral_indicator (hg hA)]
  simp [Measure.real]

lemma countable_process_bound_of_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [Countable I] (X : I → Ω → ℕ)
    (hXm : ∀ i, Measurable (X i)) (hX01 : ∀ i ω, X i ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (B : I → Set I)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ i, Measurable (Y i))
    (hYlaw : ∀ i, P'.map (Y i) = poissonMeasure (p P X i).toNNReal)
    (hfinite : ∀ (F : Finset I) (h : (F → ℕ) → ℝ),
      (∀ z, 0 ≤ h z) → (∀ z, h z ≤ 1) →
      ENNReal.ofReal |(∫ ω, h (fun i => X i ω) ∂P) -
        (∫ ω, h (fun i => Y i ω) ∂P')| ≤ 2 * b1 P X B + 2 * b2 P X B + b3 P X B) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (Xproc X)) (P'.map (Xproc Y))) ≤
      2 * (2 * b1 P X B + 2 * b2 P X B + b3 P X B) := by
  apply ofReal_twice_tv_le
  intro A hA
  have hmX : Measurable (Xproc X) := measurable_pi_lambda _ hXm
  have hmY : Measurable (Xproc Y) := measurable_pi_lambda _ hYm
  change ENNReal.ofReal |(P.map (Xproc X)).real A - (P'.map (Xproc Y)).real A| ≤ _
  rw [map_measureReal_apply hmX hA, map_measureReal_apply hmY hA]
  let R := 2 * b1 P X B + 2 * b2 P X B + b3 P X B
  have hlim : Tendsto (fun F : Finset I => tailMass P X F + R + tailMass P X F) atTop (𝓝 R) := by
    simpa using ((tailMass_tendsto_zero P X hlam).add_const R).add (tailMass_tendsto_zero P X hlam)
  apply ge_of_tendsto hlim
  filter_upwards [] with F
  have hx := bernoulli_zeroPad_distance P X hX01 F A
  have hy := poisson_zeroPad_distance P X P' Y hYm hYlaw F A
  have hm := hfinite F (fun z => eventTest A (zeroPad F z))
    (fun z => eventTest_nonneg A _) (fun z => eventTest_le_one A _)
  have hpx : Measurable (fun ω => zeroPad F (fun i => X i ω)) :=
    (measurable_zeroPad F).comp (measurable_pi_lambda _ (fun i => hXm i))
  have hpy : Measurable (fun ω => zeroPad F (fun i => Y i ω)) :=
    (measurable_zeroPad F).comp (measurable_pi_lambda _ (fun i => hYm i))
  rw [integral_eventTest P _ hpx A hA, integral_eventTest P' _ hpy A hA] at hm
  have ht := ofReal_abs_sub_triangle (P.real ((Xproc X) ⁻¹' A))
    (P.real ((fun ω => zeroPad F (fun i => X i ω)) ⁻¹' A))
    (P'.real ((fun ω => zeroPad F (fun i => Y i ω)) ⁻¹' A)) (P'.real ((Xproc Y) ⁻¹' A))
  rw [abs_sub_comm (P'.real ((fun ω => zeroPad F (fun i => Y i ω)) ⁻¹' A))] at ht
  exact ht.trans (add_le_add (add_le_add hx hm) hy)

end ChenStein.Process.Proof
-- End CountableTransfer

-- Begin IndicatorBasic
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : I → Ω → ℕ}
omit [MeasurableSpace Ω] in
lemma indicator_cast_eq (hX : ∀ α ω, X α ω ≤ 1) (α : I) :
    (fun ω => (X α ω : ℝ)) = Set.indicator {ω | X α ω = 1} (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases h : X α ω = 1
  · simp [h]
  · have hz : X α ω = 0 := by have := hX α ω; omega
    simp [hz]
lemma indicator_integrable (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) (α : I) :
    Integrable (fun ω => (X α ω : ℝ)) P := by
  rw [indicator_cast_eq hX α]
  exact (integrable_const (1 : ℝ)).indicator ((hm α) (measurableSet_singleton 1))
omit [IsProbabilityMeasure P] in
lemma integral_indicator_cast (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) (α : I) :
    (∫ ω, (X α ω : ℝ) ∂P) = p P X α := by
  rw [indicator_cast_eq hX α]
  have hs : MeasurableSet {ω | X α ω = 1} := (hm α) (measurableSet_singleton 1)
  rw [MeasureTheory.integral_indicator hs]
  simp [p]
omit [IsProbabilityMeasure P] in
lemma p_nonneg (α : I) : 0 ≤ p P X α := measureReal_nonneg
lemma p_le_one (α : I) : p P X α ≤ 1 := by
  exact measureReal_le_one
end ChenStein.Process.Proof
-- End IndicatorBasic

-- Begin ConditionalBound
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
lemma conditional_bounded_integral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {u v : Ω → ℝ} (hu : Integrable u P)
    (hv : StronglyMeasurable[m] v) {C : ℝ} (hb : ∀ ω, |v ω| ≤ C) :
    ENNReal.ofReal |∫ ω, u ω * v ω ∂P| ≤
      ENNReal.ofReal C * ∫⁻ ω, ‖P[u | m] ω‖ₑ ∂P := by
  have hvm := hv.mono hm
  have huv := hu.mul_bdd hvm.aestronglyMeasurable (ae_of_all _ fun ω => by simpa using hb ω)
  have hpull := condExp_mul_of_stronglyMeasurable_right hv huv hu
  have hid : (∫ ω, u ω * v ω ∂P) = ∫ ω, P[u | m] ω * v ω ∂P := by
    exact (integral_condExp (μ := P) hm (f := u * v)).symm.trans (integral_congr_ae hpull)
  rw [hid]
  calc
    _ ≤ ∫⁻ ω, ‖P[u | m] ω * v ω‖ₑ ∂P := by
      simpa only [Real.enorm_eq_ofReal_abs] using enorm_integral_le_lintegral_enorm (μ := P) (fun ω => P[u | m] ω * v ω)
    _ ≤ ∫⁻ ω, ENNReal.ofReal C * ‖P[u | m] ω‖ₑ ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      simp only [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
      rw [mul_comm (ENNReal.ofReal C)]
      gcongr
      exact hb ω
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end ChenStein.Process.Proof
-- End ConditionalBound

-- Begin ProfileBasic
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {Ω I K : Type*} [MeasurableSpace Ω] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K] in
lemma profile_measurable (X : I → Ω → ℕ) (hm : ∀ i, Measurable (X i)) (e : K → I) :
    Measurable (fun ω k => X (e k) ω) := measurable_pi_lambda _ (fun k => hm (e k))
omit [DecidableEq K] in
lemma finite_profile_measurable (h : (K → ℕ) → ℝ) : Measurable h :=
  measurable_of_countable h
lemma bounded_integrable {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hm : Measurable f) {C : ℝ} (hb : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω => by simpa using hb ω)
lemma farSigma_le (X : I → Ω → ℕ) (hm : ∀ i, Measurable (X i)) (B : I → Set I) (α : I) :
    farSigma X B α ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup_le fun β => iSup_le fun _ => (hm β).comap_le
noncomputable def eraseNear (X : I → Ω → ℕ) (B : I → Set I) (e : K → I) (i : K)
    (ω : Ω) : K → ℕ := by
  classical
  exact fun j => if e j ∈ B (e i) then 0 else X (e j) ω
omit [MeasurableSpace Ω] [Fintype K] [DecidableEq K] in
lemma eraseNear_far (X : I → Ω → ℕ) (B : I → Set I) (e : K → I) (i : K) :
    @Measurable Ω (K → ℕ) (farSigma X B (e i)) inferInstance (eraseNear X B e i) := by
  classical
  let : MeasurableSpace Ω := farSigma X B (e i)
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : e j ∈ B (e i)
  · simp [eraseNear, h]
  · simp only [eraseNear, h, ↓reduceIte]
    exact measurable_iff_comap_le.mpr (le_iSup_of_le (e j) (le_iSup_of_le h le_rfl))
lemma removed_bound (f : (K → ℕ) → ℝ) (hf : ∀ z, |f z| ≤ 1)
    (z v : K → ℕ) (S : Finset K) (hagree : ∀ j, j ∉ S → z j = v j)
    (hzero : ∀ j ∈ S, z j = 0 → v j = 0) :
    |f z - f v| ≤ 2 * ∑ j ∈ S, (z j : ℝ) := by
  by_cases hz : ∀ j ∈ S, z j = 0
  · have he : z = v := by
      funext j
      by_cases hj : j ∈ S
      · rw [hz j hj, hzero j hj (hz j hj)]
      · exact hagree j hj
    rw [he, sub_self, abs_zero]
    positivity
  · push Not at hz
    obtain ⟨j, hj, hjz⟩ := hz
    have hzj : (1 : ℝ) ≤ z j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hjz
    have hs : (z j : ℝ) ≤ ∑ k ∈ S, (z k : ℝ) := Finset.single_le_sum (fun k _ => Nat.cast_nonneg _) hj
    calc
      |f z - f v| ≤ |f z| + |f v| := abs_sub _ _
      _ ≤ 2 * ∑ k ∈ S, (z k : ℝ) := by linarith [hf z, hf v]
end ChenStein.Process.Proof
-- End ProfileBasic

-- Begin FiniteAverage
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def coordinateAverage (μ : K → Measure ℕ) (i : K) (h : (K → ℕ) → ℝ)
    (z : K → ℕ) : ℝ := ∫ k, h (Function.update z i k) ∂μ i
noncomputable def averaged (μ : K → Measure ℕ) (s : Finset K) (h : (K → ℕ) → ℝ)
    (z : K → ℕ) : ℝ := (lmarginal μ s (fun z => ENNReal.ofReal (h z)) z).toReal
omit [Fintype K] in
lemma lmarginal_unit (μ : K → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset K) (h : (K → ℕ) → ℝ) (h1 : ∀ z, h z ≤ 1) (z : K → ℕ) :
    lmarginal μ s (fun z => ENNReal.ofReal (h z)) z ≤ 1 := by
  unfold lmarginal
  calc
    _ ≤ ∫⁻ _ : s → ℕ, (1 : ℝ≥0∞) ∂Measure.pi (fun i : s => μ i) := by
      apply lintegral_mono; intro x
      exact (ENNReal.ofReal_le_ofReal (h1 _)).trans_eq (by norm_num)
    _ = 1 := by simp
omit [Fintype K] in
lemma averaged_bounds (μ : K → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset K) (h : (K → ℕ) → ℝ) (h1 : ∀ z, h z ≤ 1) :
    (∀ z, 0 ≤ averaged μ s h z) ∧ ∀ z, averaged μ s h z ≤ 1 := by
  constructor
  · intro z; exact ENNReal.toReal_nonneg
  · intro z
    exact (ENNReal.toReal_mono (by simp) (lmarginal_unit μ s h h1 z)).trans_eq (by simp)
omit [Fintype K] in
lemma averaged_empty (μ : K → Measure ℕ) (h : (K → ℕ) → ℝ) (h0 : ∀ z, 0 ≤ h z) :
    averaged μ ∅ h = h := by
  funext z
  simp [averaged, h0 z]
lemma averaged_insert (μ : K → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset K) (i : K) (hi : i ∉ s) (h : (K → ℕ) → ℝ) (h1 : ∀ z, h z ≤ 1) :
    averaged μ (insert i s) h = coordinateAverage μ i (averaged μ s h) := by
  funext z
  unfold averaged coordinateAverage
  rw [lmarginal_insert _ (measurable_of_countable _) hi]
  symm
  exact integral_toReal (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun k => (lmarginal_unit μ s h h1 _).trans_lt (by simp))
lemma averaged_univ (μ : K → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : (K → ℕ) → ℝ) (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) (z : K → ℕ) :
    averaged μ Finset.univ h z = ∫ x, h x ∂Measure.pi μ := by
  unfold averaged
  rw [lmarginal_univ]
  have hi : Integrable h (Measure.pi μ) := bounded_integrable (measurable_of_countable _)
    (fun x => by rw [abs_of_nonneg (h0 x)]; exact h1 x)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)]
  exact ENNReal.toReal_ofReal (integral_nonneg h0)
omit [Fintype K] in
lemma coordinateAverage_bounds (μ : K → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (i : K) (h : (K → ℕ) → ℝ) (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) :
    (∀ z, 0 ≤ coordinateAverage μ i h z) ∧ ∀ z, coordinateAverage μ i h z ≤ 1 := by
  constructor
  · intro z; exact integral_nonneg (fun k => h0 _)
  · intro z
    have hi : Integrable (fun k => h (Function.update z i k)) (μ i) :=
      bounded_integrable (measurable_of_countable _) (fun k => by rw [abs_of_nonneg (h0 _)]; exact h1 _)
    exact (integral_mono hi (integrable_const (1 : ℝ)) (fun k => h1 _)).trans_eq (by simp)
end ChenStein.Process.Proof
-- End FiniteAverage

-- Begin AverageTelescope
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {Ω K : Type*} [MeasurableSpace Ω] [Fintype K] [DecidableEq K]
lemma average_telescope (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → K → ℕ) (μ : K → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]
    (R : K → ℝ≥0∞)
    (hstep : ∀ (g : (K → ℕ) → ℝ), (∀ z, 0 ≤ g z) → (∀ z, g z ≤ 1) → ∀ i,
      ENNReal.ofReal |(∫ ω, g (Z ω) ∂P)-(∫ ω, coordinateAverage μ i g (Z ω) ∂P)| ≤ R i)
    (h : (K → ℕ) → ℝ) (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) :
    ENNReal.ofReal |(∫ ω, h (Z ω) ∂P)-(∫ z, h z ∂Measure.pi μ)| ≤ ∑ i, R i := by
  have aux : ∀ s : Finset K,
      ENNReal.ofReal |(∫ ω, h (Z ω) ∂P)-(∫ ω, averaged μ s h (Z ω) ∂P)| ≤ ∑ i ∈ s, R i := by
    intro s
    induction s using Finset.induction with
    | empty => simp [averaged_empty μ h h0]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, averaged_insert μ s i hi h h1]
      have hs := hstep (averaged μ s h) (averaged_bounds μ s h h1).1
        (averaged_bounds μ s h h1).2 i
      have habs := abs_sub_le (∫ ω, h (Z ω) ∂P) (∫ ω, averaged μ s h (Z ω) ∂P)
        (∫ ω, coordinateAverage μ i (averaged μ s h) (Z ω) ∂P)
      calc
        _ ≤ ENNReal.ofReal (|(∫ ω, h (Z ω) ∂P)-(∫ ω, averaged μ s h (Z ω) ∂P)| +
          |(∫ ω, averaged μ s h (Z ω) ∂P)-(∫ ω, coordinateAverage μ i (averaged μ s h) (Z ω) ∂P)|) :=
          ENNReal.ofReal_le_ofReal habs
        _ = _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ (∑ j ∈ s, R j)+R i := add_le_add ih hs
        _ = _ := add_comm _ _
  simpa only [averaged_univ μ h h0 h1, integral_const, probReal_univ, smul_eq_mul, one_mul] using aux Finset.univ
omit [DecidableEq K] in
lemma independent_profile_integral {Ω' I : Type*} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : I → Ω' → ℕ)
    (hm : ∀ α, Measurable (Y α)) (hi : iIndepFun Y P') (e : K ↪ I)
    (h : (K → ℕ) → ℝ) :
    (∫ ω, h (fun j => Y (e j) ω) ∂P') =
      ∫ z, h z ∂Measure.pi (fun j => P'.map (Y (e j))) := by
  have hind := hi.precomp e.injective
  have heq := iIndepFun.map_fun_eq_pi_map (fun j => (hm (e j)).aemeasurable) hind
  rw [← heq]
  exact (integral_map (profile_measurable Y hm e).aemeasurable
    (measurable_of_countable h).aestronglyMeasurable).symm
end ChenStein.Process.Proof
-- End AverageTelescope

-- Begin ScalarBasic

namespace ChenStein.Process.Scalar

noncomputable def T (lam : ℝ) (f : ℕ → ℝ) (w : ℕ) : ℝ :=
  (w : ℝ) * f w - lam * f (w + 1)

def Δ (h : ℕ → ℝ) (w : ℕ) : ℝ := h (w + 1) - h w

end ChenStein.Process.Scalar
-- End ScalarBasic

-- Begin PoissonSeries

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators NNReal

namespace ChenStein.Process.Scalar

def BoundedSeq (h : ℕ → ℝ) : Prop := ∃ M : ℝ, 0 ≤ M ∧ ∀ n, |h n| ≤ M

lemma boundedSeq_shift {h : ℕ → ℝ} (hh : BoundedSeq h) :
    BoundedSeq (fun n => h (n+1)) := by
  obtain ⟨M,hM,hh⟩ := hh
  exact ⟨M,hM,fun n => hh (n+1)⟩

lemma boundedSeq_delta {h : ℕ → ℝ} (hh : BoundedSeq h) : BoundedSeq (Δ h) := by
  obtain ⟨M,hM,hh⟩ := hh
  refine ⟨2*M,by positivity,fun n => ?_⟩
  have ha := abs_sub_le (h (n+1)) 0 (h n)
  dsimp [Δ]
  simpa [two_mul] using ha.trans (by simpa using add_le_add (hh (n+1)) (hh n))

noncomputable def powerMean (h : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, t^n / (n.factorial : ℝ) * h n

noncomputable def poissonAverage (h : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * powerMean h t

lemma powerMean_summable {h : ℕ → ℝ} (hh : BoundedSeq h) (t : ℝ) :
    Summable (fun n : ℕ => t^n / (n.factorial : ℝ) * h n) := by
  obtain ⟨M,hM,hh⟩ := hh
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial |t|).mul_right M)
  intro n
  simpa [Real.norm_eq_abs, abs_mul, abs_div, abs_pow] using
    mul_le_mul_of_nonneg_left (hh n) (by positivity : 0 ≤ |t|^n / (n.factorial:ℝ))

lemma powerMean_sub {h g : ℕ → ℝ} (hh : BoundedSeq h) (hg : BoundedSeq g) (t : ℝ) :
    powerMean (fun n => h n - g n) t = powerMean h t - powerMean g t := by
  simp only [powerMean, mul_sub]
  exact (powerMean_summable hh t).tsum_sub (powerMean_summable hg t)

lemma poissonAverage_sub {h g : ℕ → ℝ} (hh : BoundedSeq h) (hg : BoundedSeq g) (t : ℝ) :
    poissonAverage (fun n => h n - g n) t = poissonAverage h t - poissonAverage g t := by
  simp [poissonAverage, powerMean_sub hh hg, mul_sub]

lemma poissonAverage_eq_integral {h : ℕ → ℝ} (t : ℝ≥0) :
    poissonAverage h t = ∫ n, h n ∂poissonMeasure t := by
  rw [integral_poissonMeasure]
  simp only [poissonAverage, powerMean, ← tsum_mul_left, smul_eq_mul]
  congr 1
  funext n
  ring

lemma poissonAverage_zero (h : ℕ → ℝ) : poissonAverage h 0 = h 0 := by
  simp only [poissonAverage, neg_zero, Real.exp_zero, one_mul, powerMean]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

end ChenStein.Process.Scalar
-- End PoissonSeries

-- Begin PoissonWeights

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

noncomputable def poissonWeight (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t)*t^n/(n.factorial:ℝ)

lemma poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight t n := by
  unfold poissonWeight
  positivity

lemma poissonWeight_pos {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 < poissonWeight t n := by
  unfold poissonWeight
  positivity

lemma poissonWeight_succ (t : ℝ) (n : ℕ) :
    (n+1:ℕ)*poissonWeight t (n+1) = t*poissonWeight t n := by
  simp only [poissonWeight,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

lemma poissonWeight_sum (t : ℝ) : HasSum (poissonWeight t) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp t).mul_left (Real.exp (-t)) using 1
  · funext n
    simp [poissonWeight,mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ,← Real.exp_add]

end ChenStein.Process.Scalar
-- End PoissonWeights

-- Begin PoissonMoments

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

lemma poissonWeight_first (t : ℝ) : HasSum (fun n : ℕ => (n:ℝ)*poissonWeight t n) t := by
  have hs : HasSum (fun n : ℕ => ((n+1:ℕ):ℝ)*poissonWeight t (n+1)) t := by
    simpa only [poissonWeight_succ,mul_one] using (poissonWeight_sum t).mul_left t
  simpa using (hs.zero_add (f := fun n : ℕ => (n:ℝ)*poissonWeight t n))

lemma poissonWeight_second (t : ℝ) : HasSum (fun n : ℕ => (n:ℝ)^2*poissonWeight t n) (t^2+t) := by
  have hs : HasSum (fun n : ℕ => ((n+1:ℕ):ℝ)^2*poissonWeight t (n+1)) (t^2+t) := by
    convert! ((poissonWeight_first t).mul_left t).add ((poissonWeight_sum t).mul_left t) using 1
    · funext n
      calc
        ((n+1:ℕ):ℝ)^2*poissonWeight t (n+1) = (n+1:ℕ)*((n+1:ℕ)*poissonWeight t (n+1)) := by ring
        _ = (n+1:ℕ)*(t*poissonWeight t n) := by rw [poissonWeight_succ]
        _ = t*((n:ℝ)*poissonWeight t n)+t*poissonWeight t n := by push_cast; ring
    · ring
  simpa using (hs.zero_add (f := fun n : ℕ => (n:ℝ)^2*poissonWeight t n))

lemma poissonWeight_score (t : ℝ) (ht : t ≠ 0) :
    HasSum (fun n : ℕ => poissonWeight t n * ((n:ℝ)/t-1)) 0 := by
  convert! ((poissonWeight_first t).div_const t).sub (poissonWeight_sum t) using 1
  · funext n
    ring
  · field_simp
    norm_num

lemma poissonWeight_score_sq (t : ℝ) (ht : t ≠ 0) :
    HasSum (fun n : ℕ => poissonWeight t n * ((n:ℝ)/t-1)^2) (1/t) := by
  convert! (((poissonWeight_second t).div_const (t^2)).sub
    (((poissonWeight_first t).div_const t).mul_left 2)).add (poissonWeight_sum t) using 1
  · funext n
    ring
  · field_simp
    ring

lemma poissonWeight_mul_summable {h : ℕ → ℝ} (hh : BoundedSeq h) (t : ℝ) :
    Summable (fun n => poissonWeight t n*h n) := by
  convert! (powerMean_summable hh t).mul_left (Real.exp (-t)) using 1
  funext n
  simp [poissonWeight,mul_div_assoc,mul_assoc]

lemma poissonAverage_eq_tsum (h : ℕ → ℝ) (t : ℝ) :
    poissonAverage h t = ∑' n,poissonWeight t n*h n := by
  simp only [poissonAverage,powerMean,←tsum_mul_left]
  congr 1
  funext n
  simp [poissonWeight,mul_div_assoc,mul_assoc]

end ChenStein.Process.Scalar
-- End PoissonMoments

-- Begin WeightedCauchy

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

lemma weighted_abs_sum_le_sqrt {p z : ℕ → ℝ} {v : ℝ}
    (hp : ∀ n, 0 ≤ p n) (h1 : HasSum p 1)
    (h2 : HasSum (fun n => p n*(z n)^2) v)
    (ha : Summable (fun n => p n*|z n|)) :
    (∑' n,p n*|z n|) ≤ Real.sqrt v := by
  have hv : 0 ≤ v := h2.tsum_eq ▸ tsum_nonneg (fun n => mul_nonneg (hp n) (sq_nonneg _))
  apply le_of_tendsto ha.hasSum
  filter_upwards [] with F
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun n => Real.sqrt (p n)) (fun n => Real.sqrt (p n)*|z n|)
  have hleft : (∑ n ∈ F,Real.sqrt (p n)*(Real.sqrt (p n)*|z n|)) = ∑ n ∈ F,p n*|z n| := by
    apply Finset.sum_congr rfl
    intro n _
    rw [←mul_assoc,Real.mul_self_sqrt (hp n)]
  have hr : (∑ n ∈ F,(Real.sqrt (p n)*|z n|)^2) = ∑ n ∈ F,p n*(z n)^2 := by
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_pow,Real.sq_sqrt (hp n),sq_abs]
  have hl : (∑ n ∈ F,(Real.sqrt (p n))^2) = ∑ n ∈ F,p n := by
    exact Finset.sum_congr rfl (fun n _ => Real.sq_sqrt (hp n))
  rw [hleft,hl,hr] at hcs
  have hF1 : (∑ n ∈ F,p n) ≤ 1 := h1.tsum_eq ▸ h1.summable.sum_le_tsum F (fun n _ => hp n)
  have hF2 : (∑ n ∈ F,p n*(z n)^2) ≤ v :=
    h2.tsum_eq ▸ h2.summable.sum_le_tsum F (fun n _ => mul_nonneg (hp n) (sq_nonneg _))
  apply Real.le_sqrt_of_sq_le
  exact hcs.trans ((mul_le_mul hF1 hF2 (Finset.sum_nonneg (fun n _ => mul_nonneg (hp n) (sq_nonneg _))) (by norm_num)).trans_eq (one_mul v))

end ChenStein.Process.Scalar
-- End WeightedCauchy

-- Begin PoissonScore

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

lemma poissonScore_abs_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => poissonWeight t n*|((n:ℝ)/t-1)|) := by
  apply Summable.of_norm_bounded (((poissonWeight_first t).summable.div_const t).add (poissonWeight_sum t).summable)
  intro n
  have hn : 0 ≤ (n:ℝ)/t := by positivity
  have h := abs_sub_le (n/t:ℝ) 0 1
  simp only [sub_zero,zero_sub,abs_neg,abs_one,abs_of_nonneg hn] at h
  simp only [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (poissonWeight_nonneg ht.le n)]
  calc
    _ ≤ poissonWeight t n * ((n:ℝ)/t+1) := mul_le_mul_of_nonneg_left h (poissonWeight_nonneg ht.le n)
    _ = _ := by ring


lemma poissonScore_abs_bound {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ,poissonWeight t n*|((n:ℝ)/t-1)|) ≤ Real.sqrt (1/t) :=
  weighted_abs_sum_le_sqrt (poissonWeight_nonneg ht.le) (poissonWeight_sum t)
    (poissonWeight_score_sq t ht.ne') (poissonScore_abs_summable ht)

lemma poissonScore_mul_hasSum {h : ℕ → ℝ} (hh : BoundedSeq h) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => poissonWeight t n*((n:ℝ)/t-1)*h n) (poissonAverage (Δ h) t) := by
  have hs0 : HasSum (fun n => poissonWeight t n*h (n+1)) (poissonAverage (fun n => h (n+1)) t) := by
    rw [poissonAverage_eq_tsum]
    exact (poissonWeight_mul_summable (boundedSeq_shift hh) t).hasSum
  have hs1 : HasSum (fun n : ℕ => poissonWeight t (n+1)*((n+1:ℕ)/t)*h (n+1))
      (poissonAverage (fun n => h (n+1)) t) := by
    convert! hs0 using 1
    funext n
    have hw := poissonWeight_succ t n
    field_simp
    linear_combination h (n+1) * hw
  have hs2 : HasSum (fun n : ℕ => poissonWeight t n*((n:ℝ)/t)*h n)
      (poissonWeight t 0*((0:ℝ)/t)*h 0+poissonAverage (fun n => h (n+1)) t) := by
    simpa only [Nat.cast_zero] using hs1.zero_add (f := fun n : ℕ => poissonWeight t n*((n:ℝ)/t)*h n)
  have hs3 : HasSum (fun n => poissonWeight t n*h n) (poissonAverage h t) := by
    rw [poissonAverage_eq_tsum]
    exact (poissonWeight_mul_summable hh t).hasSum
  convert! hs2.sub hs3 using 1
  · funext n
    ring
  · simp only [zero_div,mul_zero,zero_mul,zero_add]
    exact poissonAverage_sub (boundedSeq_shift hh) hh t

lemma poissonScore_centered_hasSum {h : ℕ → ℝ} (hh : BoundedSeq h) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => poissonWeight t n*((n:ℝ)/t-1)*(h n-1/2)) (poissonAverage (Δ h) t) := by
  convert! (poissonScore_mul_hasSum hh ht).sub ((poissonWeight_score t ht.ne').mul_right (1/2)) using 1
  · funext n
    ring
  · simp

lemma poissonAverage_delta_score_bound {h : ℕ → ℝ} (hh0 : ∀ n, 0 ≤ h n) (hh1 : ∀ n,h n ≤ 1)
    {t : ℝ} (ht : 0 < t) : |poissonAverage (Δ h) t| ≤ 1/(2*Real.sqrt t) := by
  have hh : BoundedSeq h := ⟨1,by norm_num,fun n => by rw [abs_of_nonneg (hh0 n)]; exact hh1 n⟩
  have hs := poissonScore_centered_hasSum hh ht
  have ha : Summable (fun n : ℕ => poissonWeight t n*|((n:ℝ)/t-1)| *(1/2)) :=
    (poissonScore_abs_summable ht).mul_right (1/2)
  have hb : ∀ n : ℕ, ‖poissonWeight t n*((n:ℝ)/t-1)*(h n-1/2)‖ ≤
      poissonWeight t n*|((n:ℝ)/t-1)| *(1/2) := by
    intro n
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (poissonWeight_nonneg ht.le n)]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hh0 n],by linarith [hh1 n]⟩) (mul_nonneg (poissonWeight_nonneg ht.le n) (abs_nonneg _))
  calc
    |poissonAverage (Δ h) t| = ‖∑' n : ℕ,poissonWeight t n*((n:ℝ)/t-1)*(h n-1/2)‖ := by rw [hs.tsum_eq,Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ,poissonWeight t n*|((n:ℝ)/t-1)| *(1/2) := tsum_of_norm_bounded ha.hasSum hb
    _ = (∑' n : ℕ,poissonWeight t n*|((n:ℝ)/t-1)|)*(1/2) := tsum_mul_right
    _ ≤ Real.sqrt (1/t)*(1/2) := mul_le_mul_of_nonneg_right (poissonScore_abs_bound ht) (by norm_num)
    _ = 1/(2*Real.sqrt t) := by rw [Real.sqrt_div (by norm_num),Real.sqrt_one]; ring

end ChenStein.Process.Scalar
-- End PoissonScore

-- Begin PoissonDerivative

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

noncomputable def powerDeriv (h : ℕ → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => t^n / (n.factorial : ℝ) * h (n+1)

lemma powerTerm_hasDerivAt (h : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s^n / (n.factorial:ℝ) * h n) (powerDeriv h t n) t := by
  cases n with
  | zero => simpa [powerDeriv] using (hasDerivAt_const t (h 0))
  | succ n =>
    convert! (((hasDerivAt_id t).pow (n+1)).div_const (n+1).factorial).mul_const (h (n+1)) using 1
    simp only [powerDeriv, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, id_eq, mul_one]
    field_simp

lemma powerMean_hasDerivAt {h : ℕ → ℝ} (hh : BoundedSeq h) (t : ℝ) :
    HasDerivAt (powerMean h) (powerMean (fun n => h (n+1)) t) t := by
  obtain ⟨M,hM,hbound⟩ := hh
  let R := |t|+1
  let u : ℕ → ℝ := fun n => match n with
    | 0 => 0
    | k+1 => R^k / (k.factorial:ℝ) * M
  have hu : Summable u := by
    exact (summable_nat_add_iff 1).mp ((Real.summable_pow_div_factorial R).mul_right M)
  have hder := hasDerivAt_tsum_of_isPreconnected hu (isOpen_Ioo) (convex_Ioo (-R) R).isPreconnected
    (fun n y _ => powerTerm_hasDerivAt h n y) (y₀ := (0:ℝ)) (y := t)
  have hb : ∀ n y, y ∈ Set.Ioo (-R) R → ‖powerDeriv h y n‖ ≤ u n := by
    intro n y hy
    cases n with
    | zero => simp [powerDeriv,u]
    | succ n =>
      have hyR : |y| ≤ R := (abs_lt.mpr hy).le
      calc
        ‖powerDeriv h y (n+1)‖ = |y|^n / (n.factorial:ℝ) * |h (n+1)| := by
          simp [powerDeriv, Real.norm_eq_abs]
        _ ≤ R^n / (n.factorial:ℝ) * M := by
          exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hyR _) (by positivity))
            (hbound _) (abs_nonneg _) (by positivity)
        _ = u (n+1) := rfl
  have h0 : (0:ℝ) ∈ Set.Ioo (-R) R := by dsimp [R]; constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Set.Ioo (-R) R := by dsimp [R]; constructor <;> linarith [le_abs_self t,neg_abs_le t]
  have hd := hder hb h0 (powerMean_summable ⟨M,hM,hbound⟩ 0) ht
  have hs : HasSum (powerDeriv h t) (0 + powerMean (fun n => h (n+1)) t) :=
    (powerMean_summable (boundedSeq_shift ⟨M,hM,hbound⟩) t).hasSum.zero_add
  convert! hd using 1
  simpa using hs.tsum_eq.symm

lemma poissonAverage_hasDerivAt {h : ℕ → ℝ} (hh : BoundedSeq h) (t : ℝ) :
    HasDerivAt (poissonAverage h) (poissonAverage (Δ h) t) t := by
  convert! ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul (powerMean_hasDerivAt hh t) using 1
  rw [show Δ h = (fun n => h (n+1)-h n) from rfl, poissonAverage_sub (boundedSeq_shift hh) hh]
  simp only [poissonAverage, Function.comp_apply]
  ring

end ChenStein.Process.Scalar
-- End PoissonDerivative

-- Begin BernoulliSmoothing

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

lemma boundedSeq_translate {h : ℕ → ℝ} (hh : BoundedSeq h) (j : ℕ) :
    BoundedSeq (fun k => h (j+k)) := by
  obtain ⟨M,hM,hh⟩ := hh
  exact ⟨M,hM,fun k => hh (j+k)⟩

noncomputable def smooth (lam : ℝ) (h : ℕ → ℝ) : ℕ → ℝ → ℕ → ℝ
  | 0,s,j => poissonAverage (fun k => h (j+k)) (lam*(1-s))
  | n+1,s,j => (1-s)*smooth lam h n s j+s*smooth lam h n s (j+1)

lemma smooth_delta (lam : ℝ) {h : ℕ → ℝ} (hh : BoundedSeq h) (n : ℕ) (s : ℝ) (j : ℕ) :
    smooth lam h n s (j+1)-smooth lam h n s j = smooth lam (Δ h) n s j := by
  induction n generalizing j with
  | zero =>
    simp only [smooth]
    rw [← poissonAverage_sub (boundedSeq_translate hh (j+1)) (boundedSeq_translate hh j)]
    congr 1
    funext k
    simp [Δ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | succ n ih =>
    simp only [smooth]
    rw [show (1-s)*smooth lam h n s (j+1)+s*smooth lam h n s (j+1+1)-
      ((1-s)*smooth lam h n s j+s*smooth lam h n s (j+1)) =
      (1-s)*(smooth lam h n s (j+1)-smooth lam h n s j)+
      s*(smooth lam h n s (j+1+1)-smooth lam h n s (j+1)) by ring,ih,ih]

noncomputable def smoothDeriv (lam : ℝ) (h : ℕ → ℝ) : ℕ → ℝ → ℕ → ℝ
  | 0,s,j => -lam*smooth lam (Δ h) 0 s j
  | n+1,s,j => (n+1:ℕ)*smooth lam (Δ h) n s j-lam*smooth lam (Δ h) (n+1) s j

lemma smooth_hasDerivAt (lam : ℝ) {h : ℕ → ℝ} (hh : BoundedSeq h) (n : ℕ) (s : ℝ) (j : ℕ) :
    HasDerivAt (fun t => smooth lam h n t j) (smoothDeriv lam h n s j) s := by
  induction n generalizing j with
  | zero =>
    have hd := (poissonAverage_hasDerivAt (boundedSeq_translate hh j) (lam*(1-s))).comp s
      (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).const_mul lam)
    convert! hd using 1
    simp only [smoothDeriv,smooth,zero_sub,mul_neg,mul_one]
    have he : Δ (fun k => h (j+k)) = fun k => Δ h (j+k) := by
      funext k
      simp [Δ,Nat.add_assoc]
    rw [he]
    ring
  | succ n ih =>
    have hd := (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).mul (ih j)).add
      ((hasDerivAt_id s).mul (ih (j+1)))
    convert! hd using 1
    have he := smooth_delta lam hh n s j
    cases n with
    | zero =>
      simp only [smoothDeriv,smooth,Nat.cast_add,Nat.cast_zero,Nat.cast_one,Pi.sub_apply,id_eq] at he ⊢
      nlinarith
    | succ n =>
      simp only [smoothDeriv,Nat.cast_add,Nat.cast_one]
      simp only [smooth,Pi.sub_apply,id_eq] at he ⊢
      nlinarith

lemma smooth_at_zero (lam : ℝ) (h : ℕ → ℝ) (n j : ℕ) :
    smooth lam h n 0 j = poissonAverage (fun k => h (j+k)) lam := by
  induction n with
  | zero => simp [smooth]
  | succ n ih => simpa [smooth] using ih

lemma smooth_at_one (lam : ℝ) (h : ℕ → ℝ) (n j : ℕ) :
    smooth lam h n 1 j = h (j+n) := by
  induction n generalizing j with
  | zero => simp [smooth,poissonAverage_zero]
  | succ n ih => simpa [smooth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (j+1)

lemma smooth_abs_bound (lam : ℝ) (h : ℕ → ℝ) (n : ℕ) (s : ℝ) (hs : s ∈ Set.Icc 0 1)
    (C : ℝ) (hC : ∀ j, |poissonAverage (fun k => h (j+k)) (lam*(1-s))| ≤ C) (j : ℕ) :
    |smooth lam h n s j| ≤ C := by
  induction n generalizing j with
  | zero => exact hC j
  | succ n ih =>
    calc
      |smooth lam h (n+1) s j| ≤ |(1-s)*smooth lam h n s j|+|s*smooth lam h n s (j+1)| := abs_add_le _ _
      _ = (1-s)*|smooth lam h n s j|+s*|smooth lam h n s (j+1)| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1]
      _ ≤ (1-s)*C+s*C := add_le_add (mul_le_mul_of_nonneg_left (ih j) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (ih (j+1)) hs.1)
      _ = C := by ring

end ChenStein.Process.Scalar
-- End BernoulliSmoothing

-- Begin PoissonBound

open Filter Topology
open scoped BigOperators

namespace ChenStein.Process.Scalar

lemma poissonAverage_abs_le {h : ℕ → ℝ} {t C : ℝ} (ht : 0 ≤ t)
    (hh : ∀ n, |h n| ≤ C) : |poissonAverage h t| ≤ C := by
  rw [poissonAverage_eq_tsum]
  have hb : ∀ n, ‖poissonWeight t n*h n‖ ≤ poissonWeight t n*C := by
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (poissonWeight_nonneg ht n)]
    exact mul_le_mul_of_nonneg_left (hh n) (poissonWeight_nonneg ht n)
  simpa only [Real.norm_eq_abs,one_mul] using
    tsum_of_norm_bounded ((poissonWeight_sum t).mul_right C) hb


lemma smooth_delta_abs_le_one {lam : ℝ} (hl : 0 ≤ lam) {h : ℕ → ℝ}
    (h0 : ∀ n,0 ≤ h n) (h1 : ∀ n,h n ≤ 1) (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc 0 1) (j : ℕ) :
    |smooth lam (Δ h) n s j| ≤ 1 := by
  apply smooth_abs_bound lam (Δ h) n s hs 1 _ j
  intro k
  apply poissonAverage_abs_le (mul_nonneg hl (sub_nonneg.mpr hs.2))
  intro i
  exact abs_le.mpr ⟨by dsimp [Δ]; linarith [h0 (k+i+1),h1 (k+i)],
    by dsimp [Δ]; linarith [h1 (k+i+1),h0 (k+i)]⟩

lemma smooth_delta_abs_le_score {lam : ℝ} (hl : 0 < lam) {h : ℕ → ℝ}
    (h0 : ∀ n,0 ≤ h n) (h1 : ∀ n,h n ≤ 1) (n : ℕ) {s : ℝ} (hs : s ∈ Set.Ico 0 1) (j : ℕ) :
    |smooth lam (Δ h) n s j| ≤ 1/(2*Real.sqrt (lam*(1-s))) := by
  apply smooth_abs_bound lam (Δ h) n s ⟨hs.1,hs.2.le⟩ _ _ j
  intro k
  have he : (fun i => Δ h (k+i)) = Δ (fun i => h (k+i)) := by
    funext i
    simp [Δ,Nat.add_assoc]
  rw [he]
  exact poissonAverage_delta_score_bound (fun i => h0 (k+i)) (fun i => h1 (k+i))
    (mul_pos hl (sub_pos.mpr hs.2))

end ChenStein.Process.Scalar
-- End PoissonBound

-- Begin SteinIntegral

open Filter Topology MeasureTheory
open scoped BigOperators

namespace ChenStein.Process.Scalar

lemma smooth_continuous (lam : ℝ) {h : ℕ → ℝ} (hh : BoundedSeq h) (n j : ℕ) :
    Continuous (fun s => smooth lam h n s j) :=
  continuous_iff_continuousAt.mpr (fun s => (smooth_hasDerivAt lam hh n s j).continuousAt)

lemma smoothDeriv_continuous (lam : ℝ) {h : ℕ → ℝ} (hh : BoundedSeq h) (n j : ℕ) :
    Continuous (fun s => smoothDeriv lam h n s j) := by
  cases n with
  | zero => exact (smooth_continuous lam (boundedSeq_delta hh) 0 j).const_mul (-lam)
  | succ n =>
    exact ((smooth_continuous lam (boundedSeq_delta hh) n j).const_mul (n+1:ℕ)).sub
      ((smooth_continuous lam (boundedSeq_delta hh) (n+1) j).const_mul lam)

noncomputable def steinSmooth (lam : ℝ) (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => ∫ s in (0:ℝ)..1, smooth lam (Δ h) n s 0

lemma steinSmooth_zero (lam : ℝ) (h : ℕ → ℝ) : steinSmooth lam h 0 = 0 := rfl

lemma steinSmooth_equation (lam : ℝ) {h : ℕ → ℝ} (hh : BoundedSeq h) (w : ℕ) :
    T lam (steinSmooth lam h) w = h w-poissonAverage h lam := by
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun s _ => smooth_hasDerivAt lam hh w s 0)
    ((smoothDeriv_continuous lam hh w 0).intervalIntegrable 0 1)
  rw [smooth_at_one,smooth_at_zero] at hft
  simp only [Nat.zero_add] at hft
  cases w with
  | zero =>
    simp only [smoothDeriv,intervalIntegral.integral_const_mul] at hft
    simpa only [T,steinSmooth,Nat.cast_zero,zero_mul,zero_sub,neg_mul] using hft
  | succ n =>
    have hi := (smooth_continuous lam (boundedSeq_delta hh) n 0).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 1)
    have hj := (smooth_continuous lam (boundedSeq_delta hh) (n+1) 0).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 1)
    simpa only [T,steinSmooth,smoothDeriv,intervalIntegral.integral_sub (hi.const_mul _) (hj.const_mul _),
      intervalIntegral.integral_const_mul] using hft

lemma steinSmooth_abs_le_one {lam : ℝ} (hl : 0 ≤ lam) {h : ℕ → ℝ}
    (h0 : ∀ n,0 ≤ h n) (h1 : ∀ n,h n ≤ 1) (w : ℕ) : |steinSmooth lam h w| ≤ 1 := by
  cases w with
  | zero => simp [steinSmooth]
  | succ n =>
    have hb : ∀ s ∈ Set.uIoc (0:ℝ) 1, ‖smooth lam (Δ h) n s 0‖ ≤ 1 := by
      intro s hs
      rw [Set.uIoc_of_le (by norm_num)] at hs
      rw [Real.norm_eq_abs]
      exact smooth_delta_abs_le_one hl h0 h1 n ⟨hs.1.le,hs.2⟩ 0
    simpa [steinSmooth,Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const hb

end ChenStein.Process.Scalar
-- End SteinIntegral

-- Begin ScalarEndpoint

open MeasureTheory ProbabilityTheory

namespace ChenStein.Process.Proof

noncomputable def scalarSolve (lam : ℝ) (h : ℕ → ℝ) : ℕ → ℝ :=
  Scalar.steinSmooth lam h

lemma scalarSolve_bound {lam : ℝ} (hl : 0 ≤ lam) {h : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ h n) (h1 : ∀ n, h n ≤ 1) (n : ℕ) :
    |scalarSolve lam h n| ≤ 1 := Scalar.steinSmooth_abs_le_one hl h0 h1 n

lemma scalarSolve_equation {lam : ℝ} (hl : 0 ≤ lam) {h : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ h n) (h1 : ∀ n, h n ≤ 1) (n : ℕ) :
    (n : ℝ) * scalarSolve lam h n - lam * scalarSolve lam h (n + 1) =
      h n - ∫ k, h k ∂poissonMeasure lam.toNNReal := by
  have hb : Scalar.BoundedSeq h :=
    ⟨1, by norm_num, fun k => by rw [abs_of_nonneg (h0 k)]; exact h1 k⟩
  have he := Scalar.steinSmooth_equation lam hb n
  have hi := Scalar.poissonAverage_eq_integral (h := h) lam.toNNReal
  rw [Real.coe_toNNReal _ hl] at hi
  rw [hi] at he
  exact he

end ChenStein.Process.Proof
-- End ScalarEndpoint

-- Begin ProfileStein
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def profileSolve (p : ℝ) (i : K) (h : (K → ℕ) → ℝ)
    (z : K → ℕ) : ℝ := scalarSolve p (fun k => h (Function.update z i k)) (z i)
omit [Fintype K] in
lemma profileSolve_bound {p : ℝ} (hp : 0 ≤ p) (i : K) (h : (K → ℕ) → ℝ)
    (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) (z : K → ℕ) :
    |profileSolve p i h z| ≤ 1 := scalarSolve_bound hp (fun _ => h0 _) (fun _ => h1 _) _
omit [Fintype K] in
lemma profileSolve_equation {p : ℝ} (hp : 0 ≤ p) (i : K) (h : (K → ℕ) → ℝ)
    (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) (z : K → ℕ) :
    (z i : ℝ)*profileSolve p i h z - p*profileSolve p i h (Function.update z i (z i+1)) =
      h z - ∫ k, h (Function.update z i k) ∂poissonMeasure p.toNNReal := by
  have heq := scalarSolve_equation hp (fun k => h0 (Function.update z i k))
    (fun k => h1 (Function.update z i k)) (z i)
  simpa [profileSolve, Function.update_idem, Function.update_eq_self] using heq
end ChenStein.Process.Proof
-- End ProfileStein

-- Begin LocalAlgebra
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace ChenStein.Process.Proof
variable {K : Type*} [Fintype K] [DecidableEq K]
omit [Fintype K] in
lemma bernoulli_local_identity (z : K → ℕ) (i : K) (hz : z i ≤ 1)
    (p : ℝ) (f : (K → ℕ) → ℝ) (v : K → ℕ) :
    (z i : ℝ) * f z - p * f (Function.update z i (z i + 1)) =
      p * (z i : ℝ) * (f (Function.update z i 1) - f (Function.update z i 2)) +
      ((z i : ℝ) - p) * (f (Function.update z i 1) - f v) +
      ((z i : ℝ) - p) * f v := by
  have h : z i = 0 ∨ z i = 1 := by omega
  rcases h with h | h
  · simp only [h, Nat.cast_zero, mul_zero, zero_mul, Nat.zero_add, zero_sub]
    ring
  · have he : Function.update z i 1 = z := by simp [← h]
    simp only [h, Nat.cast_one, mul_one, one_mul, he]
    norm_num only
    ring
lemma near_difference_bound {Ω I : Type*} [MeasurableSpace Ω]
    (X : I → Ω → ℕ) (B : I → Set I) (e : K ↪ I) (i : K)
    (f : (K → ℕ) → ℝ) (hf : ∀ z, |f z| ≤ 1) (ω : Ω) :
    |f (Function.update (fun j => X (e j) ω) i 1) -
      f (Function.update (eraseNear X B e i ω) i 1)| ≤
      2 * ∑ j ∈ Finset.univ.filter (fun j => e j ∈ B (e i) ∧ j ≠ i), (X (e j) ω : ℝ) := by
  classical
  let S := Finset.univ.filter (fun j => e j ∈ B (e i) ∧ j ≠ i)
  have h := removed_bound f hf (Function.update (fun j => X (e j) ω) i 1)
    (Function.update (eraseNear X B e i ω) i 1) S ?_ ?_
  · have heq : (∑ j ∈ S, (Function.update (fun j => X (e j) ω) i 1 j : ℝ)) = ∑ j ∈ S, (X (e j) ω : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji := (Finset.mem_filter.mp hj).2.2
      simp [Function.update_of_ne hji]
    rw [heq] at h
    exact h
  · intro j hj
    by_cases hji : j = i
    · subst j; simp
    · have hn : e j ∉ B (e i) := by simpa [S, hji] using hj
      simp [Function.update_of_ne hji, eraseNear, hn]
  · intro j hj _hz
    have hh := (Finset.mem_filter.mp hj).2
    simp [Function.update_of_ne hh.2, eraseNear, hh.1]
omit [Fintype K] in
lemma local_near_bound (z : K → ℕ) (i : K) (p : ℝ) (hp : 0 ≤ p)
    (f : (K → ℕ) → ℝ) (hf : ∀ z, |f z| ≤ 1) (v : K → ℕ)
    (r : ℝ) (_hr : 0 ≤ r)
    (hd : |f (Function.update z i 1) - f v| ≤ 2*r) :
    |p * (z i : ℝ) * (f (Function.update z i 1) - f (Function.update z i 2)) +
      ((z i : ℝ) - p) * (f (Function.update z i 1) - f v)| ≤
      2*p*(z i : ℝ) + 2*((z i : ℝ)+p)*r := by
  have hd2 : |f (Function.update z i 1) - f (Function.update z i 2)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hf (Function.update z i 1), hf (Function.update z i 2)])
  have hzp : |(z i : ℝ)-p| ≤ (z i : ℝ)+p := by
    simpa [abs_of_nonneg hp] using abs_sub (z i : ℝ) p
  calc
    _ ≤ |p*(z i : ℝ)| * |f (Function.update z i 1)-f (Function.update z i 2)| +
        |(z i : ℝ)-p| * |f (Function.update z i 1)-f v| := by
      simpa only [abs_mul] using abs_add_le (p*(z i : ℝ)*(f (Function.update z i 1)-f (Function.update z i 2)))
        (((z i : ℝ)-p)*(f (Function.update z i 1)-f v))
    _ ≤ p*(z i : ℝ)*2 + ((z i : ℝ)+p)*(2*r) := by
      rw [abs_of_nonneg (mul_nonneg hp (Nat.cast_nonneg _))]
      gcongr
    _ = _ := by ring
end ChenStein.Process.Proof
-- End LocalAlgebra

-- Begin ExpectationBasic
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
lemma abs_integral_le_majorant {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (h : ∀ ω, |f ω| ≤ g ω) : |∫ ω, f ω ∂P| ≤ ∫ ω, g ω ∂P :=
  (abs_integral_le_integral_abs).trans (integral_mono hf.abs hg h)
lemma indicator_product_integrable {X : I → Ω → ℕ} (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) (α β : I) :
    Integrable (fun ω => (X α ω : ℝ)*(X β ω : ℝ)) P := by
  apply bounded_integrable (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hm α)).mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hm β)))
  intro ω
  change |(X α ω : ℝ)*(X β ω : ℝ)| ≤ 1
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  exact mul_le_one₀ (by exact_mod_cast hX α ω) (Nat.cast_nonneg _) (by exact_mod_cast hX β ω)
lemma expectation_near_majorant {K : Type*} [Fintype K] (e : K → I) (α : I) (S : Finset K)
    {X : I → Ω → ℕ} (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1) :
    (∫ ω, 2*p P X α*(X α ω : ℝ) +
      2*((X α ω : ℝ)+p P X α)*(∑ j ∈ S, (X (e j) ω : ℝ)) ∂P) =
      2*(p P X α)^2 + 2*∑ j ∈ S, (pab P X α (e j)+p P X α*p P X (e j)) := by
  have hfun : (fun ω => 2*p P X α*(X α ω : ℝ) +
      2*((X α ω : ℝ)+p P X α)*(∑ j ∈ S, (X (e j) ω : ℝ))) =
      fun ω => 2*p P X α*(X α ω : ℝ) +
        2*∑ j ∈ S, ((X α ω : ℝ)*(X (e j) ω : ℝ)+p P X α*(X (e j) ω : ℝ)) := by
    funext ω
    rw [Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi : ∀ j, Integrable (fun ω => (X α ω : ℝ)*(X (e j) ω : ℝ)+p P X α*(X (e j) ω : ℝ)) P :=
    fun j => (indicator_product_integrable hm hX α (e j)).add ((indicator_integrable hm hX (e j)).const_mul _)
  have his : Integrable (fun ω => ∑ j ∈ S, ((X α ω : ℝ)*(X (e j) ω : ℝ)+p P X α*(X (e j) ω : ℝ))) P := by
    simpa only [Finset.sum_apply] using integrable_finsetSum S (fun j _ => hi j)
  rw [hfun, integral_add ((indicator_integrable hm hX α).const_mul _) (his.const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum S (fun j _ => hi j),
    integral_indicator_cast hm hX]
  congr 1
  · ring
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_add (indicator_product_integrable hm hX α (e j))
      ((indicator_integrable hm hX (e j)).const_mul _), integral_const_mul,
      integral_indicator_cast hm hX]
    rfl
end ChenStein.Process.Proof
-- End ExpectationBasic

-- Begin LocalError
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace ChenStein.Process.Proof
variable {Ω I K : Type*} [MeasurableSpace Ω] [Fintype K] [DecidableEq K]
variable {P : Measure Ω} [IsProbabilityMeasure P]
lemma local_profile_error (X : I → Ω → ℕ) (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) (B : I → Set I) (e : K ↪ I) (i : K)
    (f : (K → ℕ) → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    ENNReal.ofReal |∫ ω, (X (e i) ω : ℝ)*f (fun j => X (e j) ω) -
      p P X (e i)*f (Function.update (fun j => X (e j) ω) i (X (e i) ω+1)) ∂P| ≤
      ENNReal.ofReal (2*(p P X (e i))^2 +
        2*∑ j ∈ Finset.univ.filter (fun j => e j ∈ B (e i) ∧ j ≠ i),
          (pab P X (e i) (e j)+p P X (e i)*p P X (e j))) + s P X B (e i) := by
  classical
  let z : Ω → K → ℕ := fun ω j => X (e j) ω
  let v : Ω → K → ℕ := fun ω => Function.update (eraseNear X B e i ω) i 1
  let S := Finset.univ.filter (fun j => e j ∈ B (e i) ∧ j ≠ i)
  let r : Ω → ℝ := fun ω => ∑ j ∈ S, (X (e j) ω : ℝ)
  let q := p P X (e i)
  let a : Ω → ℝ := fun ω => q*(X (e i) ω : ℝ)*
      (f (Function.update (z ω) i 1)-f (Function.update (z ω) i 2)) +
      ((X (e i) ω : ℝ)-q)*(f (Function.update (z ω) i 1)-f (v ω))
  let b : Ω → ℝ := fun ω => ((X (e i) ω : ℝ)-q)*f (v ω)
  have hfm := finite_profile_measurable f
  have hzm := profile_measurable X hm e
  have hvmfar : @Measurable Ω (K → ℕ) (farSigma X B (e i)) _ v := by
    let : MeasurableSpace Ω := farSigma X B (e i)
    apply measurable_pi_iff.mpr
    intro j
    by_cases hji : j = i
    · subst j; simpa only [v, Function.update_self] using (measurable_const : Measurable (fun _ : Ω => (1:ℕ)))
    · simpa only [v, Function.update_of_ne hji, Function.comp_def] using (measurable_pi_apply j).comp (eraseNear_far X B e i)
  have hvm := hvmfar.mono (farSigma_le X hm B (e i)) le_rfl
  have ha1 := hfm.comp ((measurable_update_left (a := i) (x := (1:ℕ))).comp hzm)
  have ha2 := hfm.comp ((measurable_update_left (a := i) (x := (2:ℕ))).comp hzm)
  have hav := hfm.comp hvm
  have hxi := indicator_integrable (P := P) hm hX (e i)
  have hdiff : ∀ u v, ‖f u-f v‖ ≤ 2 := by
    intro u v
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hf u, hf v])
  have ha : Integrable a P := by
    apply Integrable.add
    · exact (hxi.const_mul q).mul_bdd (ha1.sub ha2).aestronglyMeasurable
        (ae_of_all _ fun ω => hdiff (Function.update (z ω) i 1) (Function.update (z ω) i 2))
    · exact (hxi.sub (integrable_const q)).mul_bdd (ha1.sub hav).aestronglyMeasurable
        (ae_of_all _ fun ω => hdiff (Function.update (z ω) i 1) (v ω))
  have hb : Integrable b P := (hxi.sub (integrable_const q)).mul_bdd hav.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa using hf (v ω))
  have hr : Integrable r P := by
    simpa only [Finset.sum_apply] using integrable_finsetSum S (fun j _ => indicator_integrable (P := P) hm hX (e j))
  have hprod : Integrable (fun ω => ((X (e i) ω : ℝ)+q)*r ω) P := by
    have hbnd : ∀ ω, ‖(X (e i) ω : ℝ)+q‖ ≤ 2 := by
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (p_nonneg _))]
      have hx : (X (e i) ω : ℝ) ≤ 1 := by exact_mod_cast hX (e i) ω
      linarith [p_le_one (P := P) (X := X) (e i)]
    simpa only [Function.comp_apply, Pi.add_apply, mul_comm] using hr.mul_bdd (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hm (e i))).add measurable_const).aestronglyMeasurable (ae_of_all _ hbnd)
  have hmajor : Integrable (fun ω => 2*q*(X (e i) ω : ℝ)+2*((X (e i) ω : ℝ)+q)*r ω) P := by
    simpa only [Pi.add_def, mul_assoc] using ((hxi.const_mul (2*q)).add (hprod.const_mul 2))
  have hanear : |∫ ω, a ω ∂P| ≤ 2*q^2 +
      2*∑ j ∈ S, (pab P X (e i) (e j)+q*p P X (e j)) := by
    calc
      _ ≤ ∫ ω, 2*q*(X (e i) ω : ℝ)+2*((X (e i) ω : ℝ)+q)*r ω ∂P := by
        apply abs_integral_le_majorant ha hmajor
        intro ω
        exact local_near_bound (z ω) i q (p_nonneg _) f hf (v ω) (r ω)
          (Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _))
          (near_difference_bound X B e i f hf ω)
      _ = _ := expectation_near_majorant e (e i) S hm hX
  have hbfar : ENNReal.ofReal |∫ ω, b ω ∂P| ≤ s P X B (e i) := by
    have hh := conditional_bounded_integral (farSigma_le X hm B (e i))
      (hxi.sub (integrable_const q)) (hfm.comp hvmfar).stronglyMeasurable (fun ω => hf (v ω))
    simpa only [b, q, s, Pi.sub_def, Function.comp_def, ENNReal.ofReal_one, one_mul] using hh
  have hid : (fun ω => (X (e i) ω : ℝ)*f (fun j => X (e j) ω) -
      p P X (e i)*f (Function.update (fun j => X (e j) ω) i (X (e i) ω+1))) =
      fun ω => a ω+b ω := by
    funext ω
    exact bernoulli_local_identity (z ω) i (hX (e i) ω) q f (v ω)
  rw [hid, integral_add ha hb]
  calc
    _ ≤ ENNReal.ofReal (|∫ ω, a ω ∂P|+|∫ ω, b ω ∂P|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |∫ ω, a ω ∂P|+ENNReal.ofReal |∫ ω, b ω ∂P| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal hanear) hbfar
end ChenStein.Process.Proof
-- End LocalError

-- Begin FiniteRows
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace ChenStein.Process.Proof
variable {Ω I K : Type*} [MeasurableSpace Ω] [Fintype K] [DecidableEq K]
variable {P : Measure Ω} [IsProbabilityMeasure P]
omit [DecidableEq K] [Fintype K] in
lemma finite_subtype_sum_le {J : Type*} (S : Finset K) (e : {k // k ∈ S} ↪ J)
    (g : J → ℝ≥0∞) : (∑ k : {k // k ∈ S}, g (e k)) ≤ ∑' j, g j := by
  simpa only [tsum_fintype] using ENNReal.tsum_comp_le_tsum_of_injective e.injective g
noncomputable def rowBound (P : Measure Ω) (X : I → Ω → ℕ) (B : I → Set I) (α : I) : ℝ≥0∞ :=
  2*(∑' β : B α, ENNReal.ofReal (p P X α*p P X β)) +
  2*(∑' β : {β // β ∈ B α ∧ β ≠ α}, ENNReal.ofReal (pab P X α β)) + s P X B α
omit [IsProbabilityMeasure P] in
lemma finite_row_bound (X : I → Ω → ℕ)
    (B : I → Set I) (hB : ∀ α, α ∈ B α) (e : K ↪ I) (i : K) :
    ENNReal.ofReal (2*(p P X (e i))^2 +
      2*∑ j ∈ Finset.univ.filter (fun j => e j ∈ B (e i) ∧ j ≠ i),
        (pab P X (e i) (e j)+p P X (e i)*p P X (e j))) + s P X B (e i) ≤
      rowBound P X B (e i) := by
  classical
  let S := Finset.univ.filter (fun j => e j ∈ B (e i) ∧ j ≠ i)
  let T := Finset.univ.filter (fun j => e j ∈ B (e i))
  have hTi : i ∈ T := by simp [T, hB]
  have hST : S = T.erase i := by ext j; simp [S,T,and_comm]
  have hpn : ∀ j, 0 ≤ p P X (e i)*p P X (e j) := fun j => mul_nonneg (p_nonneg _) (p_nonneg _)
  have habn : ∀ j, 0 ≤ pab P X (e i) (e j) := fun j => integral_nonneg (fun ω => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hpp : ENNReal.ofReal ((p P X (e i))^2) +
      ∑ j ∈ S, ENNReal.ofReal (p P X (e i)*p P X (e j)) ≤
      ∑' β : B (e i), ENNReal.ofReal (p P X (e i)*p P X β) := by
    let ee : {j // j ∈ T} ↪ B (e i) :=
      ⟨fun j => ⟨e j, (Finset.mem_filter.mp j.2).2⟩, fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab))⟩
    have hh := finite_subtype_sum_le T ee (fun β => ENNReal.ofReal (p P X (e i)*p P X β))
    change (∑ j : {j // j ∈ T}, ENNReal.ofReal (p P X (e i)*p P X (e j))) ≤ _ at hh
    rw [Finset.sum_coe_sort T (fun j => ENNReal.ofReal (p P X (e i)*p P X (e j)))] at hh
    rw [hST]
    have heq := Finset.sum_erase_add T (fun j => ENNReal.ofReal (p P X (e i)*p P X (e j))) hTi
    simpa only [ee, Function.Embedding.coeFn_mk, pow_two, add_comm] using heq.le.trans hh
  have hab : (∑ j ∈ S, ENNReal.ofReal (pab P X (e i) (e j))) ≤
      ∑' β : {β // β ∈ B (e i) ∧ β ≠ e i}, ENNReal.ofReal (pab P X (e i) β) := by
    let ee : {j // j ∈ S} ↪ {β // β ∈ B (e i) ∧ β ≠ e i} :=
      ⟨fun j => ⟨e j, (Finset.mem_filter.mp j.2).2.1,
        fun hh => (Finset.mem_filter.mp j.2).2.2 (e.injective hh)⟩,
        fun a b hh => Subtype.ext (e.injective (congrArg Subtype.val hh))⟩
    have hh := finite_subtype_sum_le S ee (fun β => ENNReal.ofReal (pab P X (e i) β))
    change (∑ j : {j // j ∈ S}, ENNReal.ofReal (pab P X (e i) (e j))) ≤ _ at hh
    rw [Finset.sum_coe_sort S (fun j => ENNReal.ofReal (pab P X (e i) (e j)))] at hh
    exact hh
  have heq : ENNReal.ofReal (2*(p P X (e i))^2 +
      2*∑ j ∈ S, (pab P X (e i) (e j)+p P X (e i)*p P X (e j))) =
      2*(ENNReal.ofReal ((p P X (e i))^2)+∑ j ∈ S, ENNReal.ofReal (p P X (e i)*p P X (e j))) +
      2*∑ j ∈ S, ENNReal.ofReal (pab P X (e i) (e j)) := by
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => add_nonneg (habn j) (hpn j)))), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (habn j) (hpn j))]
    simp_rw [ENNReal.ofReal_add (habn _) (hpn _)]
    rw [Finset.sum_add_distrib]
    norm_num only [ENNReal.ofReal_ofNat]
    ring
  rw [heq]
  unfold rowBound
  gcongr
omit [DecidableEq K] [IsProbabilityMeasure P] in
lemma sum_rowBound_le (X : I → Ω → ℕ) (B : I → Set I) (e : K ↪ I) :
    (∑ i, rowBound P X B (e i)) ≤ 2*b1 P X B+2*b2 P X B+b3 P X B := by
  have hh := ENNReal.tsum_comp_le_tsum_of_injective e.injective (rowBound P X B)
  simpa only [tsum_fintype, rowBound, ENNReal.tsum_add, ENNReal.tsum_mul_left, b1,b2,b3] using hh
end ChenStein.Process.Proof
-- End FiniteRows

-- Begin FiniteTest
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.Process.Proof
variable {Ω I : Type*} [MeasurableSpace Ω]
lemma finite_embedded_test_bound {K : Type*} [Fintype K] [DecidableEq K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ α, Measurable (Y α)) (hYind : iIndepFun Y P')
    (hYlaw : ∀ α, P'.map (Y α) = poissonMeasure (p P X α).toNNReal)
    (e : K ↪ I) (h : (K → ℕ) → ℝ) (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) :
    ENNReal.ofReal |(∫ ω, h (fun j => X (e j) ω) ∂P)-(∫ ω, h (fun j => Y (e j) ω) ∂P')| ≤
      2*b1 P X B+2*b2 P X B+b3 P X B := by
  classical
  let μ : K → Measure ℕ := fun j => poissonMeasure (p P X (e j)).toNNReal
  have hstep : ∀ (g : (K → ℕ) → ℝ), (∀ z, 0 ≤ g z) → (∀ z, g z ≤ 1) → ∀ i,
      ENNReal.ofReal |(∫ ω, g (fun j => X (e j) ω) ∂P)-
        (∫ ω, coordinateAverage μ i g (fun j => X (e j) ω) ∂P)| ≤ rowBound P X B (e i) := by
    intro g g0 g1 i
    let f := profileSolve (p P X (e i)) i g
    have hf : ∀ z, |f z| ≤ 1 := profileSolve_bound (p_nonneg _) i g g0 g1
    have hg : Integrable (fun ω => g (fun j => X (e j) ω)) P :=
      bounded_integrable ((finite_profile_measurable g).comp (profile_measurable X hXm e))
        (fun ω => by rw [abs_of_nonneg (g0 (fun j => X (e j) ω))]; exact g1 _)
    have ha : Integrable (fun ω => coordinateAverage μ i g (fun j => X (e j) ω)) P :=
      bounded_integrable ((finite_profile_measurable (coordinateAverage μ i g)).comp (profile_measurable X hXm e))
        (fun ω => by rw [abs_of_nonneg ((coordinateAverage_bounds μ i g g0 g1).1 (fun j => X (e j) ω))];
                     exact (coordinateAverage_bounds μ i g g0 g1).2 _)
    rw [← integral_sub hg ha]
    have heq : (fun ω => g (fun j => X (e j) ω)-coordinateAverage μ i g (fun j => X (e j) ω)) =
      fun ω => (X (e i) ω : ℝ)*f (fun j => X (e j) ω)-
        p P X (e i)*f (Function.update (fun j => X (e j) ω) i (X (e i) ω+1)) := by
      funext ω
      exact (profileSolve_equation (p_nonneg _) i g g0 g1 _).symm
    rw [heq]
    exact (local_profile_error X hXm hX01 B e i f hf).trans (finite_row_bound X B hB e i)
  have hb := average_telescope P (fun ω j => X (e j) ω) μ (fun i => rowBound P X B (e i)) hstep h h0 h1
  have hy := independent_profile_integral P' Y hYm hYind e h
  simp_rw [hYlaw] at hy
  rw [hy]
  exact hb.trans (sum_rowBound_le X B e)
lemma finite_process_test_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ α, Measurable (Y α)) (hYind : iIndepFun Y P')
    (hYlaw : ∀ α, P'.map (Y α) = poissonMeasure (p P X α).toNNReal)
    (F : Finset I) (h : (F → ℕ) → ℝ) (h0 : ∀ z, 0 ≤ h z) (h1 : ∀ z, h z ≤ 1) :
    ENNReal.ofReal |(∫ ω, h (fun j => X j ω) ∂P)-(∫ ω, h (fun j => Y j ω) ∂P')| ≤
      2*b1 P X B+2*b2 P X B+b3 P X B := by
  classical
  exact finite_embedded_test_bound P X hXm hX01 B hB P' Y hYm hYind hYlaw
    ⟨Subtype.val, Subtype.val_injective⟩ h h0 h1
end ChenStein.Process.Proof
-- End FiniteTest

-- Begin RootAssembly

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem theorem_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [Countable I]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ α, Measurable (Y α)) (hYind : iIndepFun Y P')
    (hYlaw : ∀ α, P'.map (Y α) = poissonMeasure (p P X α).toNNReal) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (Xproc X)) (P'.map (Xproc Y)))
      ≤ 2 * (2 * b1 P X B + 2 * b2 P X B + b3 P X B) := by
  have _hlam0 := hlam0
  have _hp := hp
  exact Proof.countable_process_bound_of_finite P X hXm hX01 hlam B P' Y hYm hYlaw
    (fun F h h0 h1 => Proof.finite_process_test_bound P X hXm hX01 B hB P' Y hYm hYind hYlaw F h h0 h1)

end ChenStein.Process
-- End RootAssembly

-- Begin Solution

open ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [Countable I]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ α, Measurable (Y α)) (hYind : iIndepFun Y P')
    (hYlaw : ∀ α, P'.map (Y α) = poissonMeasure (p P X α).toNNReal) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (Xproc X)) (P'.map (Xproc Y)))
      ≤ 2 * (2 * b1 P X B + 2 * b2 P X B + b3 P X B) := by
  exact ChenStein.Process.theorem_2 P X hXm hX01 hp lam hlam hlam0 B hB P' Y hYm hYind hYlaw

-- End Solution
