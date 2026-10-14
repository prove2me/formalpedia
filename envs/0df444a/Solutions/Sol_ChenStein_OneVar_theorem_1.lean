-- Prove2me | solution 1 for ChenStein.OneVar.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T04:01:37.135355+00:00
-- url     : https://prove2.me/submissions/b3779841-73ba-4674-ae68-cbb4c85dc975

-- Complete checked reconstruction of the native countable Chen–Stein total-variation and zero-count theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_ChenStein_OneVar_Setting
import Definitions.Def_TotalVariationDist
import Mathlib


-- Begin Canonical

-- End Canonical

-- Begin IndicatorBasic
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
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
lemma measurable_W [Countable I] (hm : ∀ α, Measurable (X α)) : Measurable (W X) := by
  exact Measurable.tsum hm
lemma measurable_V [Countable I] (hm : ∀ α, Measurable (X α))
    (B : I → Set I) (α : I) : Measurable (V X B α) := by
  exact Measurable.tsum (fun β => hm β)
end ChenStein.OneVar.Proof
-- End IndicatorBasic

-- Begin FiniteSupport
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ChenStein.OneVar.Proof
lemma finite_support_of_summable_cast {I : Type*} {a : I → ℕ}
    (ha : Summable (fun i => (a i : ℝ))) : (Function.support a).Finite := by
  have he : ∀ᶠ i in cofinite, (a i : ℝ) < 1 :=
    ha.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hz : ∀ᶠ i in cofinite, a i = 0 := he.mono fun i hi => by
    have : a i < 1 := by exact_mod_cast hi
    omega
  simpa only [Filter.eventually_cofinite, Function.support, Set.compl_ofPred, ne_eq] using hz
lemma cast_tsum_of_finite_support {I : Type*} {a : I → ℕ}
    (ha : (Function.support a).Finite) : (∑' i, a i : ℕ) = ∑ i ∈ ha.toFinset, a i := by
  apply tsum_eq_sum
  intro i hi
  simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hi

lemma real_tsum_of_finite_support {I : Type*} {a : I → ℕ}
    (ha : (Function.support a).Finite) : (∑' i, (a i : ℝ)) = (∑' i, a i : ℕ) := by
  rw [cast_tsum_of_finite_support ha, Nat.cast_sum]
  apply tsum_eq_sum
  intro i hi
  have : a i = 0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hi
  simp [this]
end ChenStein.OneVar.Proof
-- End FiniteSupport

-- Begin CountableIndicators
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
omit [Countable I] in
lemma lintegral_indicator_cast (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) (α : I) :
    (∫⁻ ω, ENNReal.ofReal (X α ω : ℝ) ∂P) = ENNReal.ofReal (p P X α) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (indicator_integrable hm hX α)
    (ae_of_all _ fun _ => Nat.cast_nonneg _), integral_indicator_cast hm hX α]
lemma lintegral_sum_indicators (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) {lam : ℝ} (hlam : HasSum (p P X) lam) :
    (∫⁻ ω, ∑' α, ENNReal.ofReal (X α ω : ℝ) ∂P) = ENNReal.ofReal lam := by
  rw [lintegral_tsum (f := fun α ω => ENNReal.ofReal (X α ω : ℝ)) (fun α => (measurable_from_nat.comp (hm α) : Measurable (fun ω => (X α ω : ℝ))).ennreal_ofReal.aemeasurable)]
  simp_rw [lintegral_indicator_cast hm hX]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => p_nonneg α) hlam.summable, hlam.tsum_eq]
lemma ae_finite_indicator_support (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) {lam : ℝ} (hlam : HasSum (p P X) lam) :
    ∀ᵐ ω ∂P, (Function.support (fun α => X α ω)).Finite := by
  have hmeas : AEMeasurable (fun ω => ∑' α, ENNReal.ofReal (X α ω : ℝ)) P :=
    AEMeasurable.tsum fun α => (measurable_from_nat.comp (hm α) : Measurable (fun ω => (X α ω : ℝ))).ennreal_ofReal.aemeasurable
  have hfin : (∫⁻ ω, ∑' α, ENNReal.ofReal (X α ω : ℝ) ∂P) ≠ ⊤ := by
    rw [lintegral_sum_indicators hm hX hlam]; exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' hmeas hfin] with ω hω
  apply finite_support_of_summable_cast
  simpa only [ENNReal.toReal_ofReal (Nat.cast_nonneg _)] using ENNReal.summable_toReal hω.ne
end ChenStein.OneVar.Proof
-- End CountableIndicators

-- Begin CountMoments
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma ae_real_W (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) :
    (fun ω => (W X ω : ℝ)) =ᵐ[P] (fun ω => ∑' α, (X α ω : ℝ)) := by
  filter_upwards [ae_finite_indicator_support hm hX hlam] with ω hω
  exact (real_tsum_of_finite_support hω).symm
lemma lintegral_W (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) :
    (∫⁻ ω, ENNReal.ofReal (W X ω : ℝ) ∂P) = ENNReal.ofReal lam := by
  rw [← lintegral_sum_indicators hm hX hlam]
  apply lintegral_congr_ae
  filter_upwards [ae_finite_indicator_support hm hX hlam] with ω hω
  change ENNReal.ofReal ((∑' α, X α ω : ℕ) : ℝ) = _
  rw [← real_tsum_of_finite_support hω]
  apply ENNReal.ofReal_tsum_of_nonneg (fun α => Nat.cast_nonneg _)
  exact summable_of_hasFiniteSupport (hω.subset (by intro α; simp))
lemma W_integrable (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) :
    Integrable (fun ω => (W X ω : ℝ)) P := by
  refine ⟨(measurable_from_nat.comp (measurable_W hm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal (Nat.cast_nonneg _)]
  rw [lintegral_W hm hX hlam]
  exact ENNReal.ofReal_lt_top
lemma integral_W (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) :
    (∫ ω, (W X ω : ℝ) ∂P) = lam := by
  rw [integral_congr_ae (ae_real_W hm hX hlam), ← integral_tsum_of_summable_integral_norm
    (fun α => indicator_integrable hm hX α)]
  · simp_rw [integral_indicator_cast hm hX]
    exact hlam.tsum_eq
  · have he : (fun α => ∫ ω, ‖(X α ω : ℝ)‖ ∂P) = p P X := by
      funext α
      simp only [Real.norm_natCast, integral_indicator_cast hm hX]
    rw [he]
    exact hlam.summable
end ChenStein.OneVar.Proof
-- End CountMoments

-- Begin CountPartition
open MeasureTheory
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
noncomputable def nearCount {Ω I : Type*} (X : I → Ω → ℕ) (B : I → Set I)
    (α : I) (ω : Ω) : ℕ := ∑' β : {β : I | β ∈ B α ∧ β ≠ α}, X β ω
lemma finite_support_subtype {I : Type*} {a : I → ℕ} (ha : (Function.support a).Finite)
    (S : Set I) : (Function.support (fun i : S => a i)).Finite := by
  exact ha.preimage Subtype.val_injective.injOn
lemma count_partition {Ω I : Type*} {X : I → Ω → ℕ} (B : I → Set I)
    (α : I) (hα : α ∈ B α) (ω : Ω) (hω : (Function.support (fun β => X β ω)).Finite) :
    W X ω = X α ω + nearCount X B α ω + V X B α ω := by
  classical
  let a := fun β => X β ω
  have hnear : Summable (fun β => if β ∈ B α ∧ β ≠ α then a β else 0) :=
    summable_of_hasFiniteSupport (hω.subset (by intro β; simp only [Function.mem_support]; split_ifs <;> simp_all [a]))
  have hfar : Summable (fun β => if β ∉ B α then a β else 0) :=
    summable_of_hasFiniteSupport (hω.subset (by intro β; simp only [Function.mem_support]; split_ifs <;> simp_all [a]))
  have he : a = fun β => (if β = α then a α else 0) +
      (if β ∈ B α ∧ β ≠ α then a β else 0) + (if β ∉ B α then a β else 0) := by
    funext β
    by_cases he : β = α
    · subst β; simp [hα]
    · by_cases hb : β ∈ B α <;> simp [he, hb]
  change (∑' β, a β) = _
  have hsingle : Summable (fun β => if β = α then a α else 0) := by
    apply summable_of_ne_finset_zero (s := {α})
    intro β hb
    have hn : β ≠ α := by simpa only [Finset.mem_singleton] using hb
    exact if_neg hn
  conv_lhs => rw [he]
  rw [(hsingle.add hnear).tsum_add hfar, hsingle.tsum_add hnear]
  simp only [tsum_ite_eq]
  congr 1
  · congr 1
    simpa only [Set.indicator, Set.mem_ofPred_eq, nearCount, a] using
      (tsum_subtype {β : I | β ∈ B α ∧ β ≠ α} a).symm
  · simpa only [Set.indicator, Set.mem_compl_iff, V, a] using
      (tsum_subtype (B α)ᶜ a).symm
end ChenStein.OneVar.Proof
-- End CountPartition

-- Begin FarSigma
open MeasureTheory
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] {X : I → Ω → ℕ}
lemma farSigma_le (hm : ∀ α, Measurable (X α)) (B : I → Set I) (α : I) :
    farSigma X B α ≤ (inferInstance : MeasurableSpace Ω) := by
  exact iSup_le fun β => iSup_le fun _ => (hm β).comap_le
lemma measurable_V_far [Countable I] (B : I → Set I) (α : I) :
    @Measurable Ω ℕ (farSigma X B α) inferInstance (V X B α) := by
  let : MeasurableSpace Ω := farSigma X B α
  change Measurable (fun ω => ∑' β : ((B α)ᶜ : Set I), X β ω)
  apply Measurable.tsum
  intro β
  exact measurable_iff_comap_le.mpr (le_iSup_of_le β.1 (le_iSup_of_le β.2 le_rfl))
lemma V_comap_le_far [Countable I] (B : I → Set I) (α : I) :
    MeasurableSpace.comap (V X B α) inferInstance ≤ farSigma X B α :=
  (measurable_V_far B α).comap_le
end ChenStein.OneVar.Proof
-- End FarSigma

-- Begin Dependence
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma s'_le_s (hm : ∀ α, Measurable (X α)) (B : I → Set I) (α : I) :
    s' P X B α ≤ s P X B α := by
  have ht := condExp_condExp_of_le (μ := P) (f := fun ω => (X α ω : ℝ) - p P X α)
    (V_comap_le_far B α) (farSigma_le hm B α)
  unfold s' s
  calc
    _ = ∫⁻ ω, ‖P[P[fun ω => (X α ω : ℝ) - p P X α | farSigma X B α] |
      MeasurableSpace.comap (V X B α) inferInstance] ω‖ₑ ∂P :=
      lintegral_congr_ae (ht.symm.fun_comp enorm)
    _ ≤ _ := by
      simpa only [← eLpNorm_one_eq_lintegral_enorm] using
        eLpNorm_condExp_le_eLpNorm (μ := P)
          (m := MeasurableSpace.comap (V X B α) inferInstance)
          (P[fun ω => (X α ω : ℝ) - p P X α | farSigma X B α]) (le_refl (1 : ℝ≥0∞))
lemma b3'_le_b3 (hm : ∀ α, Measurable (X α)) (B : I → Set I) :
    b3' P X B ≤ b3 P X B := ENNReal.tsum_le_tsum fun α => s'_le_s hm B α
end ChenStein.OneVar.Proof
-- End Dependence

-- Begin ConditionalBound
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
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
end ChenStein.OneVar.Proof
-- End ConditionalBound

-- Begin Telescope
namespace ChenStein.OneVar.Proof
lemma abs_sub_le_mul_nat (f : ℕ → ℝ) {D : ℝ}
    (hf : ∀ n, |f (n + 1) - f n| ≤ D) (a k : ℕ) :
    |f (a + k) - f a| ≤ D * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      |f (a + (k + 1)) - f a| ≤ |f (a + k + 1) - f (a + k)| + |f (a + k) - f a| := by
        simpa only [Nat.add_assoc] using abs_sub_le (f (a + k + 1)) (f (a + k)) (f a)
      _ ≤ D + D * k := add_le_add (hf _) ih
      _ = D * (k + 1 : ℕ) := by push_cast; ring
lemma local_error_bound (f : ℕ → ℝ) {D p : ℝ} (hp : 0 ≤ p)
    (hf : ∀ n, |f (n + 1) - f n| ≤ D) (x u v : ℕ) (hx : x ≤ 1) :
    |(x : ℝ) * (f (x + u + v) - f (v + 1)) -
      p * (f (x + u + v + 1) - f (v + 1))| ≤ D * (((x : ℝ) + p) * u + p * x) := by
  have hfirst : |(x : ℝ) * (f (x + u + v) - f (v + 1))| ≤ D * x * u := by
    have hx' : x = 0 ∨ x = 1 := by omega
    rcases hx' with rfl | rfl
    · simp
    · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using abs_sub_le_mul_nat f hf (v + 1) u
  have hsecond : |p * (f (x + u + v + 1) - f (v + 1))| ≤ p * (D * (x + u)) := by
    rw [abs_mul, abs_of_nonneg hp]
    apply mul_le_mul_of_nonneg_left _ hp
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using abs_sub_le_mul_nat f hf (v + 1) (x + u)
  calc
    _ ≤ |(x : ℝ) * (f (x + u + v) - f (v + 1))| +
        |p * (f (x + u + v + 1) - f (v + 1))| := abs_sub _ _
    _ ≤ D * x * u + p * (D * (x + u)) := add_le_add hfirst hsecond
    _ = _ := by ring
end ChenStein.OneVar.Proof
-- End Telescope

-- Begin LocalTerms
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
noncomputable def localTerm {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : I → Ω → ℕ) (f : ℕ → ℝ) (α : I) (ω : Ω) : ℝ :=
  (X α ω : ℝ) * f (W X ω) - p P X α * f (W X ω + 1)
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma bounded_count_measurable (hm : ∀ α, Measurable (X α)) (f : ℕ → ℝ) :
    Measurable (fun ω => f (W X ω)) := measurable_from_nat.comp (measurable_W hm)
lemma localTerm_integrable (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (α : I) :
    Integrable (localTerm P X f α) P := by
  apply Integrable.sub
  · exact (indicator_integrable hm hX α).mul_bdd (bounded_count_measurable hm f).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hf (W X ω))
  · apply (integrable_const (p P X α)).mul_bdd
      (bounded_count_measurable hm (fun n => f (n + 1))).aestronglyMeasurable
    exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hf (W X ω + 1)
lemma far_term_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    (B : I → Set I) {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (α : I) :
    ENNReal.ofReal |∫ ω, ((X α ω : ℝ) - p P X α) * f (V X B α ω + 1) ∂P| ≤
      ENNReal.ofReal C * s' P X B α := by
  apply conditional_bounded_integral
    ((measurable_V hm B α).comap_le)
    ((indicator_integrable hm hX α).sub (integrable_const _))
  · have hmV : @Measurable Ω ℕ (MeasurableSpace.comap (V X B α) inferInstance)
        inferInstance (V X B α) := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_from_nat : Measurable (fun n : ℕ => f (n + 1))).comp hmV).stronglyMeasurable
  · intro ω; exact hf _
end ChenStein.OneVar.Proof
-- End LocalTerms

-- Begin SteinExpectation
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
omit [Countable I] [IsProbabilityMeasure P] in
lemma localTerm_norm_bound {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (α : I) (ω : Ω) :
    ‖localTerm P X f α ω‖ ≤ C * ((X α ω : ℝ) + p P X α) := by
  unfold localTerm
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |(X α ω : ℝ) * f (W X ω)| + |p P X α * f (W X ω + 1)| := abs_sub _ _
    _ ≤ (X α ω : ℝ) * C + p P X α * C := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (X α ω) : (0 : ℝ) ≤ _), abs_of_nonneg (p_nonneg α)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hf _) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (hf _) (p_nonneg α))
    _ = _ := by ring
lemma localTerm_norm_integral_bound (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) {f : ℕ → ℝ} {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) (α : I) :
    (∫ ω, ‖localTerm P X f α ω‖ ∂P) ≤ (2 * C) * p P X α := by
  calc
    _ ≤ ∫ ω, C * ((X α ω : ℝ) + p P X α) ∂P :=
      integral_mono (localTerm_integrable hm hX hf α).norm
        (((indicator_integrable hm hX α).add (integrable_const _)).const_mul C)
        (localTerm_norm_bound hf α)
    _ = _ := by
      rw [integral_const_mul, integral_add (indicator_integrable hm hX α) (integrable_const _),
        integral_indicator_cast hm hX α]
      simp only [integral_const, probReal_univ, one_smul]
      ring
lemma localTerm_summable_integrals (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) {lam : ℝ} (hlam : HasSum (p P X) lam)
    {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    Summable (fun α => ∫ ω, ‖localTerm P X f α ω‖ ∂P) := by
  apply Summable.of_nonneg_of_le (fun α => integral_nonneg fun _ => norm_nonneg _)
    (localTerm_norm_integral_bound hm hX hC hf)
  exact hlam.summable.mul_left (2 * C)
lemma ae_T_eq_tsum (hm : ∀ α, Measurable (X α))
    (hX : ∀ α ω, X α ω ≤ 1) {lam : ℝ} (hlam : HasSum (p P X) lam)
    (f : ℕ → ℝ) :
    (fun ω => T lam f (W X ω)) =ᵐ[P] (fun ω => ∑' α, localTerm P X f α ω) := by
  filter_upwards [ae_finite_indicator_support hm hX hlam] with ω hω
  have hs : Summable (fun α => (X α ω : ℝ)) :=
    summable_of_hasFiniteSupport (hω.subset (by intro α; simp))
  simp only [localTerm]
  rw [(hs.mul_right _).tsum_sub (hlam.summable.mul_right _), tsum_mul_right, tsum_mul_right,
    hlam.tsum_eq, real_tsum_of_finite_support hω]
  rfl
end ChenStein.OneVar.Proof
-- End SteinExpectation

-- Begin PairMoments
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma pair_integrable (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1) (α β : I) :
    Integrable (fun ω => (X α ω : ℝ) * (X β ω : ℝ)) P := by
  apply (indicator_integrable hm hX α).mul_bdd (c := 1)
    (measurable_from_nat.comp (hm β)).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖(X β ω : ℝ)‖ ≤ 1
    simpa only [Real.norm_natCast, Nat.cast_le_one] using hX β ω
lemma lintegral_pair (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1) (α β : I) :
    (∫⁻ ω, ENNReal.ofReal ((X α ω : ℝ) * (X β ω : ℝ)) ∂P) = ENNReal.ofReal (pab P X α β) := by
  exact (ofReal_integral_eq_lintegral_ofReal (pair_integrable hm hX α β)
    (ae_of_all _ fun ω => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm
lemma lintegral_product_marginal (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1) (α β : I) :
    (∫⁻ ω, ENNReal.ofReal (p P X α * (X β ω : ℝ)) ∂P) =
      ENNReal.ofReal (p P X α * p P X β) := by
  simp_rw [ENNReal.ofReal_mul (p_nonneg α)]
  rw [lintegral_const_mul (f := fun ω => ENNReal.ofReal (X β ω : ℝ)) _ ((measurable_from_nat.comp (hm β)).ennreal_ofReal),
    lintegral_indicator_cast hm hX β]
omit [IsProbabilityMeasure P] in
lemma pab_nonneg (α β : I) : 0 ≤ pab P X α β := integral_nonneg fun _ => by positivity
end ChenStein.OneVar.Proof
-- End PairMoments

-- Begin NeighborhoodSum
open scoped ENNReal
namespace ChenStein.OneVar.Proof
lemma neighborhood_sum_split {I : Type*} (g : I → ℝ≥0∞) (B : Set I) (α : I) (hα : α ∈ B) :
    (∑' β : B, g β) = g α + ∑' β : {β : I | β ∈ B ∧ β ≠ α}, g β := by
  classical
  rw [tsum_subtype B g, ENNReal.tsum_eq_add_tsum_ite α]
  simp only [Set.indicator_of_mem hα]
  congr 1
  rw [tsum_subtype {β : I | β ∈ B ∧ β ≠ α} g]
  apply tsum_congr
  intro β
  by_cases he : β = α
  · subst β; simp
  · by_cases hb : β ∈ B <;> simp [he, hb]
end ChenStein.OneVar.Proof
-- End NeighborhoodSum

-- Begin NearEnergy
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
noncomputable def nearEnergy {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : I → Ω → ℕ) (B : I → Set I) (α : I) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (p P X α * (X α ω : ℝ)) +
    ∑' β : {β : I | β ∈ B α ∧ β ≠ α},
      (ENNReal.ofReal ((X α ω : ℝ) * (X β ω : ℝ)) +
        ENNReal.ofReal (p P X α * (X β ω : ℝ)))
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
omit [IsProbabilityMeasure P] in
lemma nearEnergy_measurable (hm : ∀ α, Measurable (X α)) (B : I → Set I) (α : I) :
    Measurable (nearEnergy P X B α) := by
  unfold nearEnergy
  have hreal (β : I) : Measurable (fun ω => (X β ω : ℝ)) := measurable_from_nat.comp (hm β)
  exact (measurable_const.mul (hreal α)).ennreal_ofReal.add
    (Measurable.tsum fun β => ((hreal α).mul (hreal β)).ennreal_ofReal.add
      (measurable_const.mul (hreal β)).ennreal_ofReal)
lemma lintegral_nearEnergy (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    (B : I → Set I) (α : I) (hα : α ∈ B α) :
    (∫⁻ ω, nearEnergy P X B α ω ∂P) =
      (∑' β : B α, ENNReal.ofReal (p P X α * p P X β)) +
        ∑' β : {β : I | β ∈ B α ∧ β ≠ α}, ENNReal.ofReal (pab P X α β) := by
  have hreal (β : I) : Measurable (fun ω => (X β ω : ℝ)) := measurable_from_nat.comp (hm β)
  have ht (β : I) :
      (∫⁻ ω, ENNReal.ofReal ((X α ω : ℝ) * (X β ω : ℝ)) +
        ENNReal.ofReal (p P X α * (X β ω : ℝ)) ∂P) =
        ENNReal.ofReal (pab P X α β) + ENNReal.ofReal (p P X α * p P X β) := by
    rw [lintegral_add_left (f := fun ω => ENNReal.ofReal ((X α ω : ℝ) * (X β ω : ℝ)))
      ((hreal α).mul (hreal β)).ennreal_ofReal,
      lintegral_pair hm hX, lintegral_product_marginal hm hX]
  unfold nearEnergy
  rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (p P X α * (X α ω : ℝ)))
    (measurable_const.mul (hreal α)).ennreal_ofReal,
    lintegral_product_marginal hm hX]
  rw [lintegral_tsum (f := fun (β : {β : I | β ∈ B α ∧ β ≠ α}) ω =>
    ENNReal.ofReal ((X α ω : ℝ) * (X β ω : ℝ)) + ENNReal.ofReal (p P X α * (X β ω : ℝ)))
    (fun β => (((hreal α).mul (hreal β)).ennreal_ofReal.add
      (measurable_const.mul (hreal β)).ennreal_ofReal).aemeasurable)]
  simp_rw [ht]
  rw [ENNReal.tsum_add, neighborhood_sum_split (fun β => ENNReal.ofReal (p P X α * p P X β)) (B α) α hα]
  ac_rfl
omit [Countable I] [IsProbabilityMeasure P] in
lemma nearEnergy_eq (B : I → Set I) (α : I) (ω : Ω)
    (hω : (Function.support (fun β => X β ω)).Finite) :
    nearEnergy P X B α ω = ENNReal.ofReal
      ((((X α ω : ℝ) + p P X α) * (nearCount X B α ω : ℝ)) + p P X α * X α ω) := by
  have hs := finite_support_subtype hω {β : I | β ∈ B α ∧ β ≠ α}
  have hr : Summable (fun β : {β : I | β ∈ B α ∧ β ≠ α} => (X β ω : ℝ)) :=
    summable_of_hasFiniteSupport (hs.subset (by intro β; simp))
  unfold nearEnergy
  simp_rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (mul_nonneg (p_nonneg α) (Nat.cast_nonneg _)), ← add_mul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun β => mul_nonneg (add_nonneg (Nat.cast_nonneg _) (p_nonneg α)) (Nat.cast_nonneg _))
    (hr.mul_left _), tsum_mul_left, real_tsum_of_finite_support hs,
    ← ENNReal.ofReal_add (mul_nonneg (p_nonneg α) (Nat.cast_nonneg _))
      (mul_nonneg (add_nonneg (Nat.cast_nonneg _) (p_nonneg α)) (Nat.cast_nonneg _))]
  congr 1
  change p P X α * (X α ω : ℝ) + ((X α ω : ℝ) + p P X α) * (nearCount X B α ω : ℝ) = _
  ring
end ChenStein.OneVar.Proof
-- End NearEnergy

-- Begin LocalError
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
omit [Countable I] [IsProbabilityMeasure P] in
lemma local_error_enorm (hX : ∀ α ω, X α ω ≤ 1) (B : I → Set I)
    (α : I) (hα : α ∈ B α) {f : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ n, |f (n + 1) - f n| ≤ D) (ω : Ω)
    (hω : (Function.support (fun β => X β ω)).Finite) :
    ‖localTerm P X f α ω - ((X α ω : ℝ) - p P X α) * f (V X B α ω + 1)‖ₑ ≤
      ENNReal.ofReal D * nearEnergy P X B α ω := by
  rw [nearEnergy_eq B α ω hω, ← ENNReal.ofReal_mul hD, Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  have he : localTerm P X f α ω - ((X α ω : ℝ) - p P X α) * f (V X B α ω + 1) =
      (X α ω : ℝ) * (f (W X ω) - f (V X B α ω + 1)) -
        p P X α * (f (W X ω + 1) - f (V X B α ω + 1)) := by unfold localTerm; ring
  rw [he, count_partition B α hα ω hω]
  exact local_error_bound f (p_nonneg α) hf _ _ _ (hX α ω)
lemma far_term_integrable (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    (B : I → Set I) {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (α : I) :
    Integrable (fun ω => ((X α ω : ℝ) - p P X α) * f (V X B α ω + 1)) P := by
  apply ((indicator_integrable hm hX α).sub (integrable_const (p P X α))).mul_bdd (c := C)
    ((measurable_from_nat : Measurable (fun n : ℕ => f (n + 1))).comp (measurable_V hm B α)).aestronglyMeasurable
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hf (V X B α ω + 1)
lemma local_integral_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (B : I → Set I)
    (α : I) (hα : α ∈ B α) {f : ℕ → ℝ} {D C : ℝ} (hD : 0 ≤ D)
    (hdf : ∀ n, |f (n + 1) - f n| ≤ D) (hf : ∀ n, |f n| ≤ C) :
    ‖∫ ω, localTerm P X f α ω ∂P‖ₑ ≤
      ENNReal.ofReal D * ((∑' β : B α, ENNReal.ofReal (p P X α * p P X β)) +
        ∑' β : {β : I | β ∈ B α ∧ β ≠ α}, ENNReal.ofReal (pab P X α β)) +
      ENNReal.ofReal C * s' P X B α := by
  let z := fun ω => ((X α ω : ℝ) - p P X α) * f (V X B α ω + 1)
  have hz : Integrable z P := far_term_integrable hm hX B hf α
  have he : (∫ ω, localTerm P X f α ω ∂P) =
      (∫ ω, localTerm P X f α ω - z ω ∂P) + ∫ ω, z ω ∂P := by
    rw [integral_sub (localTerm_integrable hm hX hf α) hz]; ring
  rw [he]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · apply (enorm_integral_le_lintegral_enorm _).trans
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal D * nearEnergy P X B α ω ∂P := by
        apply lintegral_mono_ae
        filter_upwards [ae_finite_indicator_support hm hX hlam] with ω hω
        exact local_error_enorm hX B α hα hD hdf ω hω
      _ = _ := by rw [lintegral_const_mul _ (nearEnergy_measurable hm B α), lintegral_nearEnergy hm hX B α hα]
  · simpa only [Real.enorm_eq_ofReal_abs] using far_term_bound hm hX B hf α
end ChenStein.OneVar.Proof
-- End LocalError

-- Begin SteinBound
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma stein_expectation_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {f : ℕ → ℝ} {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hdf : ∀ n, |f (n + 1) - f n| ≤ D) (hf : ∀ n, |f n| ≤ C) :
    ENNReal.ofReal |∫ ω, T lam f (W X ω) ∂P| ≤
      (b1 P X B + b2 P X B) * ENNReal.ofReal D + b3' P X B * ENNReal.ofReal C := by
  rw [integral_congr_ae (ae_T_eq_tsum hm hX hlam f),
    ← integral_tsum_of_summable_integral_norm (fun α => localTerm_integrable hm hX hf α)
      (localTerm_summable_integrals hm hX hlam hC hf), ← Real.enorm_eq_ofReal_abs]
  apply enorm_tsum_le_tsum_enorm.trans
  calc
    _ ≤ ∑' α, (ENNReal.ofReal D * ((∑' β : B α, ENNReal.ofReal (p P X α * p P X β)) +
        ∑' β : {β : I | β ∈ B α ∧ β ≠ α}, ENNReal.ofReal (pab P X α β)) +
      ENNReal.ofReal C * s' P X B α) :=
      ENNReal.tsum_le_tsum fun α => local_integral_bound hm hX hlam B α (hB α) hD hdf hf
    _ = _ := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_add]
      simp only [b1, b2, b3']
      ac_rfl
end ChenStein.OneVar.Proof
-- End SteinBound

-- Begin TVBound
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
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
noncomputable def eventTest (A : Set ℕ) : ℕ → ℝ := A.indicator (fun _ => 1)
lemma eventTest_bounds (A : Set ℕ) (n : ℕ) : 0 ≤ eventTest A n ∧ eventTest A n ≤ 1 := by
  classical
  by_cases hn : n ∈ A <;> simp [eventTest, hn]
lemma integral_eventTest {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (g : E → ℕ) (hg : Measurable g) (A : Set ℕ) :
    (∫ x, eventTest A (g x) ∂μ) = (μ (g ⁻¹' A)).toReal := by
  have hA : MeasurableSet A := Set.to_countable A |>.measurableSet
  have he : (fun x => eventTest A (g x)) = (g ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext x
    classical
    by_cases hx : g x ∈ A <;> simp [eventTest, hx]
  rw [he, integral_indicator (hg hA)]
  simp [Measure.real]
lemma poissonMean_eventTest (lam : ℝ≥0) (A : Set ℕ) :
    poissonMean lam (eventTest A) = ((poissonMeasure lam) A).toReal := by
  simpa only [poissonMean, Set.preimage_id_eq, id_eq] using integral_eventTest (poissonMeasure lam) id measurable_id A
end ChenStein.OneVar.Proof
-- End TVBound

-- Begin TestBound
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma test_integrable (hm : ∀ α, Measurable (X α)) {h : ℕ → ℝ}
    (hh : ∀ n, |h n| ≤ 1) : Integrable (fun ω => h (W X ω)) P := by
  exact (integrable_const (1 : ℝ)).mono' (bounded_count_measurable hm h).aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hh (W X ω))
lemma stein_test_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {h f : ℕ → ℝ} (hh : ∀ n, |h n| ≤ 1)
    (hstein : ∀ n, T lam f n = h n - poissonMean lam.toNNReal h)
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hdf : ∀ n, |f (n + 1) - f n| ≤ D) (hf : ∀ n, |f n| ≤ C) :
    ENNReal.ofReal |(∫ ω, h (W X ω) ∂P) - poissonMean lam.toNNReal h| ≤
      (b1 P X B + b2 P X B) * ENNReal.ofReal D + b3' P X B * ENNReal.ofReal C := by
  have he : (∫ ω, T lam f (W X ω) ∂P) = (∫ ω, h (W X ω) ∂P) - poissonMean lam.toNNReal h := by
    simp_rw [hstein]
    rw [integral_sub (test_integrable hm hh) (integrable_const _)]
    simp
  rw [← he]
  exact stein_expectation_bound hm hX hlam B hB hD hC hdf hf
lemma event_test_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (B : I → Set I) (hB : ∀ α, α ∈ B α)
    (A : Set ℕ) {f : ℕ → ℝ}
    (hstein : ∀ n, T lam f n = eventTest A n - poissonMean lam.toNNReal (eventTest A))
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hdf : ∀ n, |f (n + 1) - f n| ≤ D) (hf : ∀ n, |f n| ≤ C) :
    ENNReal.ofReal |((P.map (W X)) A).toReal - ((poissonMeasure lam.toNNReal) A).toReal| ≤
      (b1 P X B + b2 P X B) * ENNReal.ofReal D + b3' P X B * ENNReal.ofReal C := by
  have hb : ∀ n, |eventTest A n| ≤ 1 := fun n => by
    rw [abs_of_nonneg (eventTest_bounds A n).1]; exact (eventTest_bounds A n).2
  have H := stein_test_bound hm hX hlam B hB hb hstein hD hC hdf hf
  rw [integral_eventTest P (W X) (measurable_W hm) A, poissonMean_eventTest] at H
  simpa only [Measure.map_apply (measurable_W hm) (Set.to_countable A).measurableSet] using H
end ChenStein.OneVar.Proof
-- End TestBound

-- Begin CoefficientBasic
open MeasureTheory
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : I → Ω → ℕ}
omit [IsProbabilityMeasure P] in
lemma b1_pos (hp : ∀ α, 0 < p P X α) (B : I → Set I) (hB : ∀ α, α ∈ B α)
    (α : I) : 0 < b1 P X B := by
  have h : 0 < ENNReal.ofReal (p P X α * p P X α) := ENNReal.ofReal_pos.mpr (mul_pos (hp α) (hp α))
  unfold b1
  exact h.trans_le ((ENNReal.le_tsum (f := fun β : B α => ENNReal.ofReal (p P X α * p P X β)) ⟨α, hB α⟩).trans (ENNReal.le_tsum α))
omit [IsProbabilityMeasure P] in
lemma index_nonempty {lam : ℝ} (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam) : Nonempty I := by
  by_contra h
  have : IsEmpty I := not_nonempty_iff.mp h
  have hz : lam = 0 := by simpa using hlam.tsum_eq.symm
  linarith
lemma q_pos {lam : ℝ} (hlam : 0 < lam) : 0 < (1 - Real.exp (-lam)) / lam := by
  exact div_pos (sub_pos.mpr ((Real.exp_lt_one_iff).mpr (by linarith))) hlam
lemma q_lt_one {lam : ℝ} (hlam : 0 < lam) : (1 - Real.exp (-lam)) / lam < 1 := by
  rw [div_lt_one hlam]
  have h := Real.add_one_lt_exp (show -lam ≠ 0 by linarith)
  linarith
lemma q_lt_inv {lam : ℝ} (hlam : 0 < lam) : (1 - Real.exp (-lam)) / lam < lam⁻¹ := by
  rw [div_eq_mul_inv]
  exact (mul_lt_mul_of_pos_right (by linarith [Real.exp_pos (-lam)] : 1 - Real.exp (-lam) < 1)
    (inv_pos.mpr hlam)).trans_eq (one_mul _)
end ChenStein.OneVar.Proof
-- End CoefficientBasic

-- Begin RootBounds
open scoped ENNReal
namespace ChenStein.OneVar.Proof
lemma coarse_bound {lam : ℝ} (hlam : 0 < lam) {a c c' : ℝ≥0∞} (hc : c' ≤ c) :
    2 * (a * ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) +
      c' * ENNReal.ofReal (min 1 (1.4 * lam ^ (-(1/2 : ℝ))))) ≤ 2 * (a + c) := by
  gcongr
  · calc
      a * ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) ≤ a * 1 := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr (q_lt_one hlam).le
      _ = a := mul_one _
  · calc
      c' * ENNReal.ofReal (min 1 (1.4 * lam ^ (-(1/2 : ℝ)))) ≤ c' * 1 := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr (min_le_left _ _)
      _ ≤ c := by simpa using hc
lemma strict_improvement {lam : ℝ} (hlam : 0 < lam) {a c c' : ℝ≥0∞}
    (hc : c' ≤ c) (hpos : 0 < a + c) (hfin : a + c < ⊤) :
    (a + c') * ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) <
      ENNReal.ofReal (min 1 lam⁻¹) * (a + c) := by
  have hq : ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) < ENNReal.ofReal (min 1 lam⁻¹) := by
    exact ENNReal.ofReal_lt_ofReal_iff (lt_min zero_lt_one (inv_pos.mpr hlam)) |>.mpr
      (lt_min (q_lt_one hlam) (q_lt_inv hlam))
  calc
    _ ≤ (a + c) * ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) := by gcongr
    _ < (a + c) * ENNReal.ofReal (min 1 lam⁻¹) := by
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos.ne' hfin.ne hq
    _ = _ := mul_comm _ _
end ChenStein.OneVar.Proof
-- End RootBounds

-- Begin NativeBounds
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace ChenStein.OneVar.Proof
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : I → Ω → ℕ}
lemma native_tv_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    (hsol : ∀ A : Set ℕ, ∃ f : ℕ → ℝ,
      (∀ n, T lam f n = eventTest A n - poissonMean lam.toNNReal (eventTest A)) ∧
      (∀ n, |f n| ≤ min 1 (1.4 * lam ^ (-(1/2 : ℝ)))) ∧
      ∀ n, |f (n + 1) - f n| ≤ (1 - Real.exp (-lam)) / lam) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (W X)) (poissonMeasure lam.toNNReal)) ≤
      2 * ((b1 P X B + b2 P X B) * ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) +
        b3' P X B * ENNReal.ofReal (min 1 (1.4 * lam ^ (-(1/2 : ℝ))))) := by
  apply ofReal_twice_tv_le
  intro A _
  obtain ⟨f, hstein, hf, hdf⟩ := hsol A
  exact event_test_bound hm hX hlam B hB A hstein (q_pos hlam0).le (by positivity) hdf hf
lemma native_zero_bound (hm : ∀ α, Measurable (X α)) (hX : ∀ α ω, X α ω ≤ 1)
    {lam : ℝ} (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α) {f : ℕ → ℝ}
    (hstein : ∀ n, T lam f n = eventTest {0} n - poissonMean lam.toNNReal (eventTest {0}))
    (hf : ∀ n, |f n| ≤ (1 - Real.exp (-lam)) / lam)
    (hdf : ∀ n, |f (n + 1) - f n| ≤ (1 - Real.exp (-lam)) / lam) :
    ENNReal.ofReal |P.real {ω | W X ω = 0} - Real.exp (-lam)| ≤
      (b1 P X B + b2 P X B + b3' P X B) * ENNReal.ofReal ((1 - Real.exp (-lam)) / lam) := by
  have H := event_test_bound hm hX hlam B hB {0} hstein (q_pos hlam0).le (q_pos hlam0).le hdf hf
  rw [Measure.map_apply (measurable_W hm) (measurableSet_singleton 0),
    poissonMeasure_singleton] at H
  have hset : W X ⁻¹' ({0} : Set ℕ) = {ω | W X ω = 0} := rfl
  rw [hset] at H
  simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one,
    Real.coe_toNNReal _ hlam0.le, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Measure.real, add_mul] using H
end ChenStein.OneVar.Proof
-- End NativeBounds

-- Begin PoissonSeries

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators NNReal

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End PoissonSeries

-- Begin PoissonWeights

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End PoissonWeights

-- Begin PoissonMoments

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End PoissonMoments

-- Begin WeightedCauchy

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End WeightedCauchy

-- Begin PoissonScore

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End PoissonScore

-- Begin PoissonDerivative

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End PoissonDerivative

-- Begin BernoulliSmoothing

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End BernoulliSmoothing

-- Begin PoissonBound

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End PoissonBound

-- Begin SteinIntegral

open Filter Topology MeasureTheory
open scoped BigOperators

namespace ChenStein.OneVar.Proof

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

end ChenStein.OneVar.Proof
-- End SteinIntegral

-- Begin ScoreIntegral

open Filter Topology MeasureTheory
open scoped BigOperators

namespace ChenStein.OneVar.Proof

lemma score_majorant_integrable (lam : ℝ) :
    IntervalIntegrable (fun s : ℝ => (1/(2*Real.sqrt lam))*(1-s)^(-(1/2:ℝ))) volume 0 1 := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(1/2:ℝ))
    (a := (0:ℝ)) (b := 1)).comp_sub_left 1
  norm_num only [sub_zero,sub_self] at hi
  exact hi.symm.const_mul _

lemma score_majorant_integral (lam : ℝ) :
    (∫ s in (0:ℝ)..1, (1/(2*Real.sqrt lam))*(1-s)^(-(1/2:ℝ))) = 1/Real.sqrt lam := by
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x^(-(1/2:ℝ)))]
  norm_num only [sub_self,sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : -1 < -(1/2:ℝ)))]
  norm_num
  ring

lemma steinSmooth_abs_le_sqrt {lam : ℝ} (hl : 0 < lam) {h : ℕ → ℝ}
    (h0 : ∀ n,0 ≤ h n) (h1 : ∀ n,h n ≤ 1) (w : ℕ) :
    |steinSmooth lam h w| ≤ 1/Real.sqrt lam := by
  have hh : BoundedSeq h := ⟨1,by norm_num,fun n => by rw [abs_of_nonneg (h0 n)]; exact h1 n⟩
  cases w with
  | zero => simp only [steinSmooth,abs_zero]; positivity
  | succ n =>
    have hi := (smooth_continuous lam (boundedSeq_delta hh) n 0).intervalIntegrable (μ := volume)
      (a := (0:ℝ)) (b := 1)
    have hb : ∀ s ∈ Set.Ioo (0:ℝ) 1, ‖smooth lam (Δ h) n s 0‖ ≤
        (1/(2*Real.sqrt lam))*(1-s)^(-(1/2:ℝ)) := by
      intro s hs
      rw [Real.norm_eq_abs]
      convert smooth_delta_abs_le_score hl h0 h1 n ⟨hs.1.le,hs.2⟩ 0 using 1
      rw [Real.rpow_neg (sub_nonneg.mpr hs.2.le),← Real.sqrt_eq_rpow,
        Real.sqrt_mul hl.le]
      ring
    calc
      |steinSmooth lam h (n+1)| ≤ ∫ s in (0:ℝ)..1, ‖smooth lam (Δ h) n s 0‖ := by
        simpa only [steinSmooth,Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun s => smooth lam (Δ h) n s 0) (by norm_num : (0:ℝ) ≤ 1)
      _ ≤ ∫ s in (0:ℝ)..1, (1/(2*Real.sqrt lam))*(1-s)^(-(1/2:ℝ)) :=
        intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi.norm (score_majorant_integrable lam) hb
      _ = 1/Real.sqrt lam := score_majorant_integral lam

end ChenStein.OneVar.Proof
-- End ScoreIntegral

-- Begin PoissonHead

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

noncomputable def headWeight (t : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, poissonWeight t j
noncomputable def headValue (t : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, poissonWeight t j*h j

lemma headWeight_succ (t : ℝ) (n : ℕ) : headWeight t (n+1)=headWeight t n+poissonWeight t n := by
  simp [headWeight,Finset.sum_range_succ]

lemma headValue_succ (t : ℝ) (h : ℕ → ℝ) (n : ℕ) : headValue t h (n+1)=headValue t h n+poissonWeight t n*h n := by
  simp [headValue,Finset.sum_range_succ]

lemma headWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ headWeight t n :=
  Finset.sum_nonneg (fun j _ => poissonWeight_nonneg ht j)

lemma headWeight_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : headWeight t n ≤ 1 := by
  exact ((poissonWeight_sum t).summable.sum_le_tsum (Finset.range n)
    (fun j _ => poissonWeight_nonneg ht j)).trans_eq (poissonWeight_sum t).tsum_eq

lemma head_first (t : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1),(j:ℝ)*poissonWeight t j)=t*headWeight t n := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,zero_mul,add_zero]
  simp only [poissonWeight_succ,headWeight,Finset.mul_sum]

lemma head_weighted_bound {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    t*headWeight t n ≤ (n:ℝ)*headWeight t (n+1) := by
  rw [← head_first,headWeight,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (poissonWeight_nonneg ht j)

lemma tail_weighted_bound {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (n:ℝ)*(1-headWeight t (n+1)) ≤ t*(1-headWeight t n) := by
  have hs : Summable (fun j : ℕ => ((j:ℝ)-(n:ℝ))*poissonWeight t j) := by
    convert! ((poissonWeight_first t).summable.sub ((poissonWeight_sum t).summable.mul_left (n:ℝ))) using 1
    funext j
    ring
  have he : (∑'j : ℕ,((j:ℝ)-(n:ℝ))*poissonWeight t j)=t-n := by
    have hh := (poissonWeight_first t).sub ((poissonWeight_sum t).mul_left (n:ℝ))
    convert! hh.tsum_eq using 1
    · congr 1; funext j; ring
    · ring
  have hb := hs.sum_le_tsum (Finset.range (n+1)) (fun j hj => by
    apply mul_nonneg _ (poissonWeight_nonneg ht j)
    exact sub_nonneg.mpr (by exact_mod_cast Nat.le_trans (Nat.le_succ n) (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))))
  rw [he] at hb
  have hf : (∑ j ∈ Finset.range (n+1),((j:ℝ)-(n:ℝ))*poissonWeight t j)=
      t*headWeight t n-(n:ℝ)*headWeight t (n+1) := by
    simp only [sub_mul,Finset.sum_sub_distrib,head_first,headWeight,Finset.mul_sum]
  rw [hf] at hb
  nlinarith

lemma head_weighted_bound_zero {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    t*headWeight t n ≤ (n:ℝ)*(headWeight t (n+1)-poissonWeight t 0) := by
  have he : headWeight t (n+1)-poissonWeight t 0 = ∑ j ∈ Finset.range n,poissonWeight t (j+1) := by
    rw [headWeight,Finset.sum_range_succ']
    ring
  rw [he,Finset.mul_sum,headWeight,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← poissonWeight_succ]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    (poissonWeight_nonneg ht (j+1))

end ChenStein.OneVar.Proof
-- End PoissonHead

-- Begin SteinPrefix

open Filter Topology
open scoped BigOperators

namespace ChenStein.OneVar.Proof

lemma stein_unique {lam : ℝ} (hl : lam ≠ 0) {f g : ℕ → ℝ}
    (h0 : f 0=g 0) (he : T lam f=T lam g) : f=g := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have ht := congrFun he n
    dsimp [T] at ht
    rw [ih] at ht
    exact (mul_left_cancel₀ hl) (by linarith)

lemma stein_prefix {lam : ℝ} {h f : ℕ → ℝ} {E : ℝ}
    (he : ∀ n,T lam f n=h n-E) (n : ℕ) :
    lam*poissonWeight lam n*f (n+1)=headWeight lam (n+1)*E-headValue lam h (n+1) := by
  induction n with
  | zero =>
    have h0 := he 0
    simp only [T,Nat.cast_zero,zero_mul,zero_sub] at h0
    simp only [headWeight,headValue,Nat.zero_add,Finset.sum_range_one]
    linear_combination -poissonWeight lam 0 * h0
  | succ n ih =>
    have hn := he (n+1)
    dsimp [T] at hn
    rw [headWeight_succ,headValue_succ]
    have hr := poissonWeight_succ lam n
    calc
      lam*poissonWeight lam (n+1)*f (n+1+1) =
          (n+1:ℕ)*poissonWeight lam (n+1)*f (n+1)-poissonWeight lam (n+1)*(h (n+1)-E) := by
            linear_combination -poissonWeight lam (n+1)*hn
      _ = lam*poissonWeight lam n*f (n+1)-poissonWeight lam (n+1)*(h (n+1)-E) := by rw [hr]
      _ = _ := by rw [ih]; ring

lemma headValue_nonneg {t : ℝ} (ht : 0 ≤ t) {h : ℕ → ℝ} (h0 : ∀ j,0 ≤ h j) (n : ℕ) :
    0 ≤ headValue t h n := Finset.sum_nonneg (fun j _ => mul_nonneg (poissonWeight_nonneg ht j) (h0 j))

lemma headValue_le_head {t : ℝ} (ht : 0 ≤ t) {h : ℕ → ℝ} (h1 : ∀ j,h j ≤ 1) (n : ℕ) :
    headValue t h n ≤ headWeight t n := by
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (h1 j) (poissonWeight_nonneg ht j)

lemma headValue_le_average {t : ℝ} (ht : 0 ≤ t) {h : ℕ → ℝ} (hh : BoundedSeq h)
    (h0 : ∀ j,0 ≤ h j) (n : ℕ) : headValue t h n ≤ poissonAverage h t := by
  rw [poissonAverage_eq_tsum]
  exact (poissonWeight_mul_summable hh t).sum_le_tsum (Finset.range n)
    (fun j _ => mul_nonneg (poissonWeight_nonneg ht j) (h0 j))

lemma average_sub_head_le {t : ℝ} (ht : 0 ≤ t) {h : ℕ → ℝ} (hh : BoundedSeq h)
    (h1 : ∀ j,h j ≤ 1) (n : ℕ) : poissonAverage h t-headValue t h n ≤ 1-headWeight t n := by
  have hh' : BoundedSeq (fun j => 1-h j) := by
    obtain ⟨M,hM,hb⟩ := hh
    refine ⟨1+M,by positivity,fun j => ?_⟩
    exact (abs_sub_le _ 0 _).trans (by simpa using add_le_add_left (hb j) 1)
  have hb := headValue_le_average ht hh' (fun j => sub_nonneg.mpr (h1 j)) n
  have he : poissonAverage (fun j => 1-h j) t = 1-poissonAverage h t := by
    rw [poissonAverage_eq_tsum,poissonAverage_eq_tsum]
    have hs := (poissonWeight_sum t).sub (poissonWeight_mul_summable hh t).hasSum
    convert! hs.tsum_eq using 1
    congr 1
    funext j
    ring
  have hf : headValue t (fun j => 1-h j) n=headWeight t n-headValue t h n := by
    simp only [headValue,headWeight,mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [he,hf] at hb
  linarith

end ChenStein.OneVar.Proof
-- End SteinPrefix

-- Begin KernelAlgebra

namespace ChenStein.OneVar.Proof

lemma kernel_difference_bound {t w p F p0 L U v : ℝ}
    (ht : 0 < t) (hw : 0 < w) (hp : 0 < p) (hp0 : 0 ≤ p0)
    (hF : 0 ≤ F) (hTail : 0 ≤ 1-F-p)
    (hHead : t*F ≤ w*(F+p-p0)) (hLast : w*(1-F-p) ≤ t*(1-F))
    (hL : 0 ≤ L ∧ L ≤ F) (hU : 0 ≤ U ∧ U ≤ 1-F-p) (hv : 0 ≤ v ∧ v ≤ 1) :
    |((F+p)*(L+p*v+U)-(L+p*v))/(t*p)-
      (F*(L+p*v+U)-L)/(w*p)| ≤ (1-p0)/t := by
  let A := ((F+p)/t-F/w)/p
  let B := ((1-F)/w-(1-F-p)/t)/p
  let M := F/w+(1-F-p)/t
  have hA : 0 ≤ A := by
    apply div_nonneg _ hp.le
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ hw ht).mpr
    nlinarith
  have hB : 0 ≤ B := by
    apply div_nonneg _ hp.le
    exact sub_nonneg.mpr ((div_le_div_iff₀ ht hw).mpr (by nlinarith [hLast]))
  have hM : 0 ≤ M := add_nonneg (div_nonneg hF hw.le) (div_nonneg hTail ht.le)
  have he : A*(1-F-p)+B*F=M := by
    dsimp [A,B,M]
    field_simp
    ring
  have he' : ((F+p)*(L+p*v+U)-(L+p*v))/(t*p)-(F*(L+p*v+U)-L)/(w*p)=
      A*U+B*L-M*v := by
    dsimp [A,B,M]
    field_simp
    ring
  have hlo : 0 ≤ A*U+B*L := add_nonneg (mul_nonneg hA hU.1) (mul_nonneg hB hL.1)
  have hhi : A*U+B*L ≤ M := by
    rw [← he]
    exact add_le_add (mul_le_mul_of_nonneg_left hU.2 hA) (mul_le_mul_of_nonneg_left hL.2 hB)
  have hb : |A*U+B*L-M*v| ≤ M := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hm : M ≤ (1-p0)/t := by
    dsimp [M]
    have hh : F/w ≤ (F+p-p0)/t := (div_le_div_iff₀ hw ht).mpr (by nlinarith [hHead])
    calc
      F/w+(1-F-p)/t ≤ (F+p-p0)/t+(1-F-p)/t := add_le_add hh le_rfl
      _ = (1-p0)/t := by ring

  rw [he']
  exact hb.trans hm

end ChenStein.OneVar.Proof
-- End KernelAlgebra

-- Begin SteinDifference

namespace ChenStein.OneVar.Proof

lemma steinSmooth_difference_bound {lam : ℝ} (hl : 0 < lam) {h : ℕ → ℝ}
    (h0 : ∀ n,0 ≤ h n) (h1 : ∀ n,h n ≤ 1) (w : ℕ) :
    |steinSmooth lam h (w+1)-steinSmooth lam h w| ≤ (1-Real.exp (-lam))/lam := by
  have hh : BoundedSeq h := ⟨1,by norm_num,fun n => by rw [abs_of_nonneg (h0 n)]; exact h1 n⟩
  have he := steinSmooth_equation lam hh
  have hprefix := stein_prefix he
  have hp := poissonWeight_pos hl
  have hp0 : poissonWeight lam 0=Real.exp (-lam) := by simp [poissonWeight]
  cases w with
  | zero =>
    have ht := he 0
    simp only [T,Nat.cast_zero,zero_mul,zero_sub,steinSmooth] at ht
    have hlv := headValue_le_average hl.le hh h0 1
    have huv := average_sub_head_le hl.le hh h1 1
    simp only [headValue,headWeight,Finset.sum_range_one] at hlv huv
    have he1 : steinSmooth lam h 1=(poissonAverage h lam-h 0)/lam := by
      apply (eq_div_iff hl.ne').mpr
      dsimp [steinSmooth]
      linarith
    rw [steinSmooth_zero,sub_zero,he1,abs_div,abs_of_pos hl]
    apply (div_le_div_iff_of_pos_right hl).mpr
    rw [← hp0]
    have hp01 := headWeight_le_one hl.le 1
    simp only [headWeight,Finset.sum_range_one] at hp01
    exact abs_le.mpr ⟨by nlinarith [h0 0,h1 0],by nlinarith [h0 0,h1 0]⟩
  | succ n =>
    let k := n+1
    let F := headWeight lam k
    let p := poissonWeight lam k
    let L := headValue lam h k
    let U := poissonAverage h lam-headValue lam h (k+1)
    have hk : 0 < (k:ℝ) := by dsimp [k]; positivity
    have hL : 0 ≤ L ∧ L ≤ F := ⟨headValue_nonneg hl.le h0 k,headValue_le_head hl.le h1 k⟩
    have hU : 0 ≤ U ∧ U ≤ 1-F-p := by
      constructor
      · exact sub_nonneg.mpr (headValue_le_average hl.le hh h0 (k+1))
      · have hu := average_sub_head_le hl.le hh h1 (k+1)
        simpa only [headWeight_succ,sub_add_eq_sub_sub] using hu
    have hE : poissonAverage h lam=L+p*h k+U := by
      dsimp [L,p,U]
      rw [headValue_succ lam h k]
      ring
    have hf : steinSmooth lam h k=(F*poissonAverage h lam-L)/((k:ℝ)*p) := by
      apply (eq_div_iff (mul_ne_zero hk.ne' (hp k).ne')).mpr
      have hb := hprefix n
      have hr := poissonWeight_succ lam n
      dsimp [k,F,L,p]
      rw [← hr] at hb
      nlinarith [hb]
    have hf' : steinSmooth lam h (k+1)=((F+p)*poissonAverage h lam-(L+p*h k))/(lam*p) := by
      apply (eq_div_iff (mul_ne_zero hl.ne' (hp k).ne')).mpr
      have hb := hprefix k
      rw [headWeight_succ,headValue_succ] at hb
      dsimp [F,p,L]
      nlinarith [hb]
    change |steinSmooth lam h (k+1)-steinSmooth lam h k| ≤ _
    rw [hf',hf,hE,← hp0]
    apply kernel_difference_bound hl hk (hp k) (hp 0).le (headWeight_nonneg hl.le k)
    · have hb := headWeight_le_one hl.le (k+1)
      rw [headWeight_succ] at hb
      linarith
    · simpa only [headWeight_succ] using head_weighted_bound_zero hl.le k
    · simpa only [headWeight_succ,sub_add_eq_sub_sub] using tail_weighted_bound hl.le k
    · exact hL
    · exact hU
    · exact ⟨h0 k,h1 k⟩

end ChenStein.OneVar.Proof
-- End SteinDifference

-- Begin ZeroStein

open Filter Topology MeasureTheory

namespace ChenStein.OneVar.Proof

noncomputable def zeroTest (n : ℕ) : ℝ := if n=0 then 1 else 0

lemma zeroTest_nonneg (n : ℕ) : 0 ≤ zeroTest n := by unfold zeroTest; split <;> norm_num
lemma zeroTest_le_one (n : ℕ) : zeroTest n ≤ 1 := by unfold zeroTest; split <;> norm_num
lemma zeroTest_bounded : BoundedSeq zeroTest := ⟨1,by norm_num,fun n => by
  rw [abs_of_nonneg (zeroTest_nonneg n)]; exact zeroTest_le_one n⟩

lemma poissonAverage_zero_delta (t : ℝ) (j : ℕ) :
    poissonAverage (fun k => Δ zeroTest (j+k)) t = if j=0 then -Real.exp (-t) else 0 := by
  have hd (m : ℕ) : Δ zeroTest m=if m=0 then -1 else 0 := by
    cases m <;> simp [Δ,zeroTest]
  rw [poissonAverage_eq_tsum]
  simp_rw [hd]
  cases j with
  | zero => simp [poissonWeight]
  | succ j => simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,false_and,if_false,mul_zero,tsum_zero]

lemma smooth_zero_abs_bound (lam : ℝ) (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    |smooth lam (Δ zeroTest) n s 0| ≤ Real.exp (-lam*(1-s)) := by
  apply smooth_abs_bound lam (Δ zeroTest) n s hs _ _ 0
  intro j
  rw [poissonAverage_zero_delta]
  split
  · rw [abs_neg,abs_of_pos (Real.exp_pos _)]
    simp only [neg_mul,le_refl]
  · simp only [abs_zero]
    positivity

lemma integral_exp_score {lam : ℝ} (hl : 0 < lam) :
    (∫ s in (0:ℝ)..1,Real.exp (-lam*(1-s)))=(1-Real.exp (-lam))/lam := by
  have hd : ∀ s : ℝ,HasDerivAt (fun s => Real.exp (-lam*(1-s))/lam) (Real.exp (-lam*(1-s))) s := by
    intro s
    have he := (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).const_mul (-lam)).exp.div_const lam
    convert! he using 1
    simp only [zero_sub,mul_neg,mul_one,Pi.sub_apply,id_eq]
    field_simp
  have hc : Continuous (fun s : ℝ => Real.exp (-lam*(1-s))) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun s _ => hd s) (hc.intervalIntegrable 0 1)
  simpa only [sub_self,mul_zero,Real.exp_zero,sub_zero,mul_one,div_sub_div_same] using he

lemma steinSmooth_zero_bound {lam : ℝ} (hl : 0 < lam) (w : ℕ) :
    |steinSmooth lam zeroTest w| ≤ (1-Real.exp (-lam))/lam := by
  have hq : 0 ≤ (1-Real.exp (-lam))/lam := by
    apply div_nonneg _ hl.le
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  cases w with
  | zero => simpa only [steinSmooth,abs_zero] using hq
  | succ n =>
    have hi := (smooth_continuous lam (boundedSeq_delta zeroTest_bounded) n 0).intervalIntegrable
      (μ := volume) (a := (0:ℝ)) (b := 1)
    have hc : Continuous (fun s : ℝ => Real.exp (-lam*(1-s))) := by fun_prop
    calc
      |steinSmooth lam zeroTest (n+1)| ≤ ∫ s in (0:ℝ)..1,‖smooth lam (Δ zeroTest) n s 0‖ := by
        simpa only [steinSmooth,Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun s => smooth lam (Δ zeroTest) n s 0) (by norm_num : (0:ℝ) ≤ 1)
      _ ≤ ∫ s in (0:ℝ)..1,Real.exp (-lam*(1-s)) :=
        intervalIntegral.integral_mono_on (by norm_num) hi.norm (hc.intervalIntegrable 0 1)
          (fun s hs => by rw [Real.norm_eq_abs]; exact smooth_zero_abs_bound lam n hs)
      _ = _ := integral_exp_score hl

end ChenStein.OneVar.Proof
-- End ZeroStein

-- Begin SteinFactors
open MeasureTheory ProbabilityTheory
namespace ChenStein.OneVar.Proof
lemma poissonAverage_native {lam : ℝ} (hl : 0 ≤ lam) (h : ℕ → ℝ) :
    poissonAverage h lam = poissonMean lam.toNNReal h := by
  have H := poissonAverage_eq_integral (h := h) lam.toNNReal
  rw [Real.coe_toNNReal _ hl] at H
  exact H
lemma native_factor_comparison {lam : ℝ} (hl : 0 < lam) :
    1 / Real.sqrt lam ≤ 1.4 * lam ^ (-(1/2 : ℝ)) := by
  rw [Real.rpow_neg hl.le, ← Real.sqrt_eq_rpow]
  have h : 0 ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  simp only [one_div]
  linarith
lemma stein_factors {lam : ℝ} (hl : 0 < lam) {h : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ h n) (h1 : ∀ n, h n ≤ 1) :
    ∃ f : ℕ → ℝ,
      (∀ n, T lam f n = h n - poissonMean lam.toNNReal h) ∧
      (∀ n, |f n| ≤ min 1 (1.4 * lam ^ (-(1/2 : ℝ)))) ∧
      ∀ n, |f (n + 1) - f n| ≤ (1 - Real.exp (-lam)) / lam := by
  have hh : BoundedSeq h := ⟨1, by norm_num, fun n => by rw [abs_of_nonneg (h0 n)]; exact h1 n⟩
  refine ⟨steinSmooth lam h, ?_, ?_, ?_⟩
  · intro n
    rw [steinSmooth_equation lam hh, poissonAverage_native hl.le]
  · intro n
    exact le_min (steinSmooth_abs_le_one hl.le h0 h1 n)
      ((steinSmooth_abs_le_sqrt hl h0 h1 n).trans (native_factor_comparison hl))
  · exact steinSmooth_difference_bound hl h0 h1
lemma zeroTest_eq_eventTest : zeroTest = eventTest {0} := by
  funext n
  classical
  by_cases hn : n = 0 <;> simp [zeroTest, eventTest, hn]
lemma zero_stein_factors {lam : ℝ} (hl : 0 < lam) :
    ∃ f : ℕ → ℝ,
      (∀ n, T lam f n = eventTest {0} n - poissonMean lam.toNNReal (eventTest {0})) ∧
      (∀ n, |f n| ≤ (1 - Real.exp (-lam)) / lam) ∧
      ∀ n, |f (n + 1) - f n| ≤ (1 - Real.exp (-lam)) / lam := by
  refine ⟨steinSmooth lam zeroTest, ?_, steinSmooth_zero_bound hl, ?_⟩
  · intro n
    rw [steinSmooth_equation lam zeroTest_bounded, poissonAverage_native hl.le, zeroTest_eq_eventTest]
  · exact steinSmooth_difference_bound hl zeroTest_nonneg zeroTest_le_one
end ChenStein.OneVar.Proof
-- End SteinFactors

-- Begin RootAssembly

namespace ChenStein.OneVar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Arratia--Goldstein--Gordon (1989), p. 11, Theorem 1. -/
theorem theorem_1 {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α) :
    let q := (1 - Real.exp (-lam)) / lam
    let a := b1 P X B + b2 P X B
    let c := b3 P X B
    let c' := b3' P X B
    let firstBound := 2 * (a * ENNReal.ofReal q +
      c' * ENNReal.ofReal (min 1 (1.4 * lam ^ (-(1/2 : ℝ)))))
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (W X))
      (poissonMeasure lam.toNNReal)) ≤ firstBound ∧
    firstBound ≤ 2 * (a + c) ∧
    ENNReal.ofReal |P.real {ω | W X ω = 0} - Real.exp (-lam)| ≤
      (a + c') * ENNReal.ofReal q ∧
    (a + c < ⊤ →
      (a + c') * ENNReal.ofReal q <
        ENNReal.ofReal (min 1 lam⁻¹) * (a + c)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Proof.native_tv_bound hXm hX01 hlam hlam0 B hB
    intro A
    exact Proof.stein_factors hlam0 (fun n => (Proof.eventTest_bounds A n).1)
      (fun n => (Proof.eventTest_bounds A n).2)
  · exact Proof.coarse_bound hlam0 (Proof.b3'_le_b3 hXm B)
  · obtain ⟨f, he, hf, hd⟩ := Proof.zero_stein_factors hlam0
    exact Proof.native_zero_bound hXm hX01 hlam hlam0 B hB he hf hd
  · intro hfin
    obtain ⟨α⟩ := Proof.index_nonempty hlam hlam0
    have hpos := Proof.b1_pos hp B hB α
    apply Proof.strict_improvement hlam0 (Proof.b3'_le_b3 hXm B) _ hfin
    exact hpos.trans_le (le_trans (le_self_add : b1 P X B ≤ b1 P X B + b2 P X B) le_self_add)


end ChenStein.OneVar
-- End RootAssembly

-- Begin Solution
open MeasureTheory ProbabilityTheory ChenStein.OneVar
open scoped ENNReal NNReal

theorem solution {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α) :
    let q := (1 - Real.exp (-lam)) / lam
    let a := b1 P X B + b2 P X B
    let c := b3 P X B
    let c' := b3' P X B
    let firstBound := 2 * (a * ENNReal.ofReal q +
      c' * ENNReal.ofReal (min 1 (1.4 * lam ^ (-(1/2 : ℝ)))))
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (W X))
      (poissonMeasure lam.toNNReal)) ≤ firstBound ∧
    firstBound ≤ 2 * (a + c) ∧
    ENNReal.ofReal |P.real {ω | W X ω = 0} - Real.exp (-lam)| ≤
      (a + c') * ENNReal.ofReal q ∧
    (a + c < ⊤ →
      (a + c') * ENNReal.ofReal q <
        ENNReal.ofReal (min 1 lam⁻¹) * (a + c)) := by
  exact ChenStein.OneVar.theorem_1 P X hXm hX01 hp lam hlam hlam0 B hB
-- End Solution
