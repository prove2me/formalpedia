-- Prove2me | solution 1 for EthierKurtz.euler_scheme_approx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T20:00:48.596994+00:00
-- url     : https://prove2.me/submissions/08e314b2-ca64-465b-808c-46a063184fcf

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_EthierKurtz_sde_stability_in_probability

set_option linter.all false

-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

/-- The coordinates of a standard `d`-dimensional Brownian motion form one real Gaussian
process indexed by `time × coordinate`. -/
theorem stdBrownian_isGaussianProcess {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) :
    IsGaussianProcess (fun (p : ℝ≥0 × Fin d) ω => W p.1 ω p.2) P := by
  obtain ⟨_, _, hBM, hind⟩ := hW
  refine ⟨fun I => ?_⟩
  classical
  let I' : Finset ℝ≥0 := I.image Prod.fst
  let V : Fin d → Ω → (I' → ℝ) := fun i ω => fun t => W t ω i
  have hV : ∀ i, HasGaussianLaw (V i) P := fun i =>
    (hBM i).isGaussianProcess.hasGaussianLaw I'
  have hVind : iIndepFun V P :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) => fun t : I' => f t) (fun _ => by fun_prop)
  have hjoint := hVind.hasGaussianLaw hV
  let L0 : (Fin d → (I' → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x p => x p.1.2 ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have := hjoint.map (LinearMap.toContinuousLinearMap L0)
  have heq : (fun ω => I.restrict (fun p : ℝ≥0 × Fin d => W p.1 ω p.2)) =
      (LinearMap.toContinuousLinearMap L0) ∘ (fun ω x => V x ω) := by
    funext ω p; rfl
  rw [heq]; exact this

/-- The covariance of two coordinates of a standard Brownian motion. -/
theorem stdBrownian_cov {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s t : ℝ≥0) (i j : Fin d) :
    cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then ((min s t : ℝ≥0) : ℝ) else 0 := by
  obtain ⟨hm, _, hBM, hind⟩ := hW
  split_ifs with hij
  · subst hij
    exact (hBM i).covariance_fun_eval s t
  · have h2 : IndepFun (fun ω => W s ω i) (fun ω => W t ω j) P := by
      have := hind.indepFun hij
      exact this.comp (φ := fun f : ℝ≥0 → ℝ => f s) (ψ := fun f : ℝ≥0 → ℝ => f t)
        (by fun_prop) (by fun_prop)
    have hP : IsProbabilityMeasure P := (hBM i).isGaussianProcess.isProbabilityMeasure
    exact h2.covariance_eq_zero ((hBM i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      ((hBM j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem stdBrownian_coord_measurable {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : Measurable (fun ω => W t ω i) := by
  have := hW.1 t
  fun_prop

theorem stdBrownian_memLp_two {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : MemLp (fun ω => W t ω i) 2 P :=
  ((hW.2.2.1 i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- Weak Markov property of a standard `d`-dimensional Brownian motion: all future increments
after `t₀` are independent of the whole past up to `t₀`. -/
theorem stdBrownian_indep_shift {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) :
    IndepFun (fun ω (p : ℝ≥0 × Fin d) => W (t₀ + p.1) ω p.2 - W t₀ ω p.2)
      (fun ω (q : Set.Iic t₀ × Fin d) => W q.1 ω q.2) P := by
  have hG := stdBrownian_isGaussianProcess hW
  have hP : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun (p : ℝ≥0 × Fin d) ω => W (t₀ + p.1) ω p.2 - W t₀ ω p.2)
    (Y := fun (q : Set.Iic t₀ × Fin d) ω => W q.1 ω q.2)
  · apply hG.of_isGaussianProcess
    rintro (⟨t, i⟩ | ⟨⟨t, ht⟩, i⟩)
    · exact ⟨{(t₀ + t, i), (t₀, i)},
        { toFun x := x ⟨(t₀ + t, i), by simp⟩ - x ⟨(t₀, i), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(t, i)},
        { toFun x := x ⟨(t, i), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p; exact ((hm (t₀ + p.1) p.2).sub (hm t₀ p.2)).aemeasurable
  · intro q; exact (hm _ _).aemeasurable
  · rintro ⟨s, i⟩ ⟨⟨t, ht⟩, j⟩
    have ht' : t ≤ t₀ := ht
    simp only
    rw [covariance_fun_sub_left (stdBrownian_memLp_two hW _ _) (stdBrownian_memLp_two hW _ _)
      (stdBrownian_memLp_two hW _ _), stdBrownian_cov hW, stdBrownian_cov hW]
    split_ifs
    · rw [min_eq_right (ht'.trans (le_add_right le_rfl)), min_eq_right ht', sub_self]
    · simp

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

/-- The `P`-a.e. closure of a σ-algebra `G`: sets a.e. equal to a `G`-set (null sets taken
for the outer measure, so arbitrary subsets of null sets qualify). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B, MeasurableSet[G] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, EventuallyEq.rfl⟩
  measurableSet_compl A := fun ⟨B, hB, h⟩ => ⟨Bᶜ, hB.compl, h.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB h using hf
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, Filter.EventuallyEq.countable_iUnion h⟩

theorem le_aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : G ≤ aeClosure P G :=
  fun A hA => ⟨A, hA, EventuallyEq.rfl⟩

/-- Independence passes to the a.e. closure. -/
theorem indep_aeClosure {P : Measure Ω} {G H : MeasurableSpace Ω} (h : Indep G H P) :
    Indep (aeClosure P G) H P := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨B, hB, hAB⟩ hC
  rw [measure_congr (hAB.inter (EventuallyEq.refl _ C)), measure_congr hAB]
  exact h B C hB hC

end AEC

section CP
variable [MeasurableSpace Ω]

/-- With a constant initial value, the completed Brownian past lies in the a.e. closure of the
natural Brownian past. -/
theorem completedBrownianPast_const_le (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (s : ℝ≥0) :
    completedBrownianPast P W (fun _ => x₀) s ≤
      aeClosure P (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) := by
  set G : MeasurableSpace Ω := ⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance
  refine sup_le (sup_le (le_aeClosure _ _) ?_) ?_
  · rintro A ⟨T, -, rfl⟩
    by_cases hx : x₀ ∈ T
    · refine ⟨Set.univ, @MeasurableSet.univ Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = Set.univ := Set.preimage_const_of_mem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
    · refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
      have : (fun _ : Ω => x₀) ⁻¹' T = ∅ := Set.preimage_const_of_notMem hx
      rw [this]
      exact Filter.EventuallyEq.rfl
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨N, -, hN, hAN⟩
    refine ⟨∅, @MeasurableSet.empty Ω G, ?_⟩
    rw [ae_eq_empty]
    exact measure_mono_null hAN hN

/-- The future increments of a standard Brownian motion after `s` are independent of the
completed Brownian past at `s` (constant initial value). -/
theorem stdBrownian_indep_completedPast {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) :
    Indep (completedBrownianPast P W (fun _ => x₀) s)
      (MeasurableSpace.comap (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2)
        inferInstance) P := by
  refine indep_of_indep_of_le_left (indep_aeClosure ?_) (completedBrownianPast_const_le P W x₀ s)
  have h := ((IndepFun_iff_Indep _ _ _).1 (stdBrownian_indep_shift hW s)).symm
  refine indep_of_indep_of_le_left h ?_
  refine iSup_le fun r => ?_
  have hg : Measurable (fun f : Set.Iic s × Fin d → ℝ =>
      (WithLp.toLp 2 (fun i => f (r, i)) : SDEState d)) := by
    refine (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp ?_
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (r, i))
  have hc : Measurable[MeasurableSpace.comap (fun ω (q : Set.Iic s × Fin d) => W q.1 ω q.2)
      inferInstance] (W r.val) :=
    hg.comp (comap_measurable _)
  exact hc.comap_le

end CP

section M2

theorem nullMeasurable_of_aeClosure {G : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (hG : G ≤ mΩ) {f : Ω → ℝ} (hf : Measurable[aeClosure P G] f) :
    NullMeasurable f P := by
  intro A hA
  obtain ⟨B, hB, h⟩ := hf hA
  exact (hG _ hB).nullMeasurableSet.congr h.symm

variable [MeasurableSpace Ω]

theorem naturalPast_le {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s : ℝ≥0) :
    (⨆ r : Set.Iic s, MeasurableSpace.comap (W r.val) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun r => (hW.1 r.val).comap_le

/-- A function measurable for the completed Brownian past (constant initial value) is
a.e.-strongly measurable for the ambient σ-algebra. -/
theorem aestronglyMeasurable_of_completedPast {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    AEStronglyMeasurable a P :=
  (nullMeasurable_of_aeClosure (naturalPast_le hW s)
    (ha.mono (completedBrownianPast_const_le P W x₀ s) le_rfl)).aemeasurable.aestronglyMeasurable

/-- A completed-past-measurable function is independent of each later increment. -/
theorem indepFun_completedPast_increment {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    IndepFun a (fun ω => W (s + h) ω j - W s ω j) P := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (stdBrownian_indep_completedPast hW x₀ s) ha.comap_le) ?_
  have hm : Measurable[MeasurableSpace.comap
      (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) inferInstance]
      (fun ω => W (s + h) ω j - W s ω j) := by
    have := (measurable_pi_apply (h, j) : Measurable fun f : ℝ≥0 × Fin d → ℝ => f (h, j)).comp
      (comap_measurable (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2))
    exact this
  exact hm.comap_le

theorem stdBrownian_integral_increment {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    ∫ ω, (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hB := hW.2.2.1 j
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
    hB.integral_eval, sub_self]

theorem stdBrownian_integral_increment_sq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    ∫ ω, (W (s + h) ω j - W s ω j) ^ 2 ∂P = h := by
  have hB := hW.2.2.1 j
  have hL := hB.hasLaw_sub (s + h) s
  have h1 : ∫ ω, (W (s + h) ω j - W s ω j) ^ 2 ∂P =
      ∫ x, x ^ 2 ∂(gaussianReal 0 (nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))) :=
    hL.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [h1]
  have h2 := variance_fun_id_gaussianReal (μ := (0 : ℝ))
    (v := nndist ((s + h : ℝ≥0) : ℝ) (s : ℝ))
  rw [variance_eq_integral (X := fun x : ℝ => x) aemeasurable_id'] at h2
  simp only [integral_id_gaussianReal, sub_zero] at h2
  rw [h2, coe_nndist, Real.dist_eq]
  push_cast
  rw [add_sub_cancel_left]
  exact abs_of_nonneg h.2

end M2

section M3
variable [MeasurableSpace Ω]

theorem completedBrownianPast_mono (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

theorem coord_measurable_completedPast (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {r t : ℝ≥0} (hrt : r ≤ t) (j : Fin d) :
    Measurable[completedBrownianPast P W ξ t] (fun ω => W r ω j) := by
  have h1 : Measurable[MeasurableSpace.comap (W r) inferInstance] (W r) := comap_measurable _
  have h0 : MeasurableSpace.comap (W r) inferInstance ≤
      ⨆ q : Set.Iic t, MeasurableSpace.comap (W q.val) inferInstance :=
    le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r, hrt⟩
  have h2 : MeasurableSpace.comap (W r) inferInstance ≤ completedBrownianPast P W ξ t := by
    unfold completedBrownianPast
    exact le_sup_of_le_left (le_sup_of_le_left h0)
  have h3 : Measurable[completedBrownianPast P W ξ t] (W r) := Measurable.mono h1 h2 le_rfl
  have h4 : Measurable fun x : SDEState d => x j := by fun_prop
  exact h4.comp h3

/-- `E[a · ΔW] = 0` for any completed-past-measurable `a` (no integrability needed). -/
theorem integral_mul_increment_eq_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    ∫ ω, a ω * (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hm := stdBrownian_coord_measurable hW
  rw [(indepFun_completedPast_increment hW x₀ s h j ha).integral_fun_mul_eq_mul_integral
    (aestronglyMeasurable_of_completedPast hW x₀ s ha)
    ((hm _ j).sub (hm _ j)).aestronglyMeasurable, stdBrownian_integral_increment hW, mul_zero]

/-- `E[a² · ΔW²] = E[a²] · h` for any completed-past-measurable `a`. -/
theorem integral_sq_mul_increment_sq {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0) (j : Fin d) {a : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a) :
    ∫ ω, (a ω * (W (s + h) ω j - W s ω j)) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * h := by
  have hm := stdBrownian_coord_measurable hW
  have hi := (indepFun_completedPast_increment hW x₀ s h j ha).comp
    (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
  have key := hi.integral_fun_mul_eq_mul_integral
    ((aestronglyMeasurable_of_completedPast hW x₀ s ha).pow 2)
    (((hm _ j).sub (hm _ j)).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply] at key
  simp_rw [mul_pow]
  rw [key, stdBrownian_integral_increment_sq hW]

end M3

section M4
variable [MeasurableSpace Ω]

/-- Discrete Itô isometry for the dyadic step sums of `HasBrownianItoIntegral`: bounded
coefficients measurable for the completed Brownian past at the left endpoints. -/
theorem itoStepSum_isometry {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (n : ℕ) (j : Fin d)
    (a : ℕ → Ω → ℝ)
    (ha : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (a k))
    (C₁ : ℝ) (hC₁ : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a k ω| ≤ C₁) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t n a ω) ^ 2 ∂P =
      ∑ k ∈ Finset.range (2 ^ n), (∫ ω, a k ω ^ 2 ∂P) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  set C : ℝ := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |a k ω| ≤ C := fun k hk ω =>
    (hC₁ k hk ω).trans (le_max_left _ _)
  set h : ℝ≥0 := t / (2 : ℝ≥0) ^ n with hh
  let τ : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n
  have hstep : ∀ k : ℕ, ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n = τ k + h := by
    intro k; simp only [τ, hh]; ring
  have hτmono : ∀ l k : ℕ, l ≤ k → τ l ≤ τ k := by
    intro l k hlk; simp only [τ]; gcongr
  have hτsucc : ∀ l k : ℕ, l < k → τ l + h ≤ τ k := by
    intro l k hlk
    rw [← hstep]; simp only [τ]; gcongr
    exact_mod_cast Nat.succ_le_of_lt hlk
  let Δ : ℕ → Ω → ℝ := fun k ω => W (τ k + h) ω j - W (τ k) ω j
  let X : ℕ → Ω → ℝ := fun k ω => a k ω * Δ k ω
  have hsum : ∀ ω, itoStepSum (fun s ω => W s ω j) t n a ω =
      ∑ k ∈ Finset.range (2 ^ n), X k ω := by
    intro ω; unfold itoStepSum
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [X, Δ]; rw [hstep k]
  have hΔL2 : ∀ k, MemLp (Δ k) 2 P := fun k =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have haesm : ∀ k, k < 2 ^ n → AEStronglyMeasurable (a k) P := fun k hk =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (ha k hk)
  have hint : ∀ k, k < 2 ^ n → ∀ l, l < 2 ^ n → Integrable (fun ω => X k ω * X l ω) P := by
    intro k hk l hl
    have hg : Integrable (fun ω => (C * C) * |Δ k ω * Δ l ω|) P :=
      ((hΔL2 k).integrable_mul (hΔL2 l)).abs.const_mul _
    refine hg.mono' (((haesm k hk).mul (hΔL2 k).1).mul ((haesm l hl).mul (hΔL2 l).1)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    calc |X k ω * X l ω| = (|a k ω| * |a l ω|) * |Δ k ω * Δ l ω| := by
          simp only [X, abs_mul]; ring
      _ ≤ (C * C) * |Δ k ω * Δ l ω| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hC k hk ω) (hC l hl ω) (abs_nonneg _) hC0)
            (abs_nonneg _)
  have off : ∀ l k, l < k → k < 2 ^ n → ∫ ω, X l ω * X k ω ∂P = 0 := by
    intro l k hlk hk
    have hl : l < 2 ^ n := hlk.trans hk
    have hb : Measurable[completedBrownianPast P W (fun _ => x₀) (τ k)]
        (fun ω => a l ω * Δ l ω * a k ω) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (ha k hk)
      · exact (ha l hl).mono (completedBrownianPast_mono P W _ (hτmono l k hlk.le)) le_rfl
      · exact (coord_measurable_completedPast P W _ (hτsucc l k hlk) j).sub
          (coord_measurable_completedPast P W _ (hτmono l k hlk.le) j)
    have := integral_mul_increment_eq_zero hW x₀ (τ k) h j hb
    rw [← this]
    congr 1; funext ω; simp only [X, Δ]; ring
  have hkey : ∀ ω, (itoStepSum (fun s ω => W s ω j) t n a ω) ^ 2 =
      ∑ k ∈ Finset.range (2 ^ n), ∑ l ∈ Finset.range (2 ^ n), X k ω * X l ω := by
    intro ω; rw [hsum ω, sq, Finset.sum_mul_sum]
  simp_rw [hkey]
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _
    (fun l hl => hint k (Finset.mem_range.1 hk) l (Finset.mem_range.1 hl)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [integral_finsetSum _ (fun l hl => hint k hk' l (Finset.mem_range.1 hl))]
  rw [Finset.sum_eq_single k]
  · calc ∫ ω, X k ω * X k ω ∂P
          = ∫ ω, (a k ω * (W (τ k + h) ω j - W (τ k) ω j)) ^ 2 ∂P := by
            congr 1; funext ω; simp only [X, Δ]; ring
      _ = _ := integral_sq_mul_increment_sq hW x₀ (τ k) h j (ha k hk')
  · intro l hl hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · rw [← off l k hlt hk']
      congr 1; funext ω; ring
    · exact off k l hgt (Finset.mem_range.1 hl)
  · intro hnot; exact absurd hk hnot

end M4

section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

theorem itoStepSum_memLp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (n : ℕ) (j : Fin d) (a : ℕ → Ω → ℝ)
    (ha : ∀ k, k < 2 ^ n → AEStronglyMeasurable (a k) P)
    (C : ℝ) (hC : ∀ k, k < 2 ^ n → ∀ ω, |a k ω| ≤ C) :
    MemLp (itoStepSum (fun s ω => W s ω j) t n a) 2 P := by
  have heq : itoStepSum (fun s ω => W s ω j) t n a = ∑ k ∈ Finset.range (2 ^ n),
      fun ω => a k ω * (W (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) ω j -
        W ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) ω j) := by
    funext ω; simp [itoStepSum, Finset.sum_apply]
  rw [heq]
  refine memLp_finsetSum' _ fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hΔ := (stdBrownian_memLp_two hW (((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n) j).sub
    (stdBrownian_memLp_two hW ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n) j)
  refine hΔ.of_le_mul (c := C) ((ha k hk').mul hΔ.1) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC k hk' ω) (abs_nonneg _)

end M5

section M5b

theorem tendstoInMeasure_zero_of_abs_le [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {F A B : ι → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hA : TendstoInMeasure P A l (fun _ => 0)) (hB : TendstoInMeasure P B l (fun _ => 0))
    (hF : ∀ i ω, |F i ω| ≤ K * (|A i ω| + |B i ω|)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hsum := (hA _ hε').add (hB _ hε')
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hF i ω
  have h2 : K * (|A i ω| + |B i ω|) < K * (ε / (2 * K) + ε / (2 * K)) :=
    mul_lt_mul_of_pos_left (add_lt_add hcon.1 hcon.2) hK
  have h3 : K * (ε / (2 * K) + ε / (2 * K)) = ε := by field_simp; ring
  linarith only [hω, h1, h2, h3]

theorem tendstoInMeasure_real_iff_sub [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f : ι → Ω → ℝ} {g : Ω → ℝ} :
    TendstoInMeasure P f l g ↔ TendstoInMeasure P (fun i ω => f i ω - g ω) l (fun _ => 0) := by
  simp only [tendstoInMeasure_iff_dist, Real.dist_eq, sub_zero]

theorem tendstoInMeasure_sub_real [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω - f' i ω) l (fun ω => g ω - g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hf' ⊢
  refine tendstoInMeasure_zero_of_abs_le one_pos hf hf' fun i ω => ?_
  rw [one_mul, abs_le]
  constructor <;> linarith only [le_abs_self (f i ω - g ω), neg_abs_le (f i ω - g ω),
    le_abs_self (f' i ω - g' ω), neg_abs_le (f' i ω - g' ω)]

theorem itoStepSum_sub (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n a ω - itoStepSum W t n b ω =
      itoStepSum W t n (fun k ω => a k ω - b k ω) ω := by
  unfold itoStepSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc

theorem itoStepValue_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => itoStepValue t n c u ω) volume 0 t.val := by
  have heq : (fun u => itoStepValue t n c u ω) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_eq_sum_indicator]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c

section M6refine

theorem sum_range_mul_block {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N K : ℕ) :
    ∑ j ∈ Finset.range (N * K), f j =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range K, f (k * K + r) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A step sum on the grid of mesh `t / 2^n` is the step sum on the finer grid `t / 2^(n+m)`
with the coefficients held constant on each coarse cell. -/
theorem itoStepSum_refine (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n m : ℕ) (a : ℕ → Ω → ℝ) (ω : Ω) :
    itoStepSum W t n a ω = itoStepSum W t (n + m) (fun k => a (k / 2 ^ m)) ω := by
  unfold itoStepSum
  rw [show (2 : ℕ) ^ (n + m) = 2 ^ n * 2 ^ m from pow_add 2 n m, sum_range_mul_block]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdiv : ∀ r ∈ Finset.range (2 ^ m), (k * 2 ^ m + r) / 2 ^ m = k := by
    intro r hr
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt (Finset.mem_range.1 hr), zero_add]
  set g : ℕ → ℝ := fun r => W (((k * 2 ^ m + r : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω
    with hg
  have hterm : ∀ r ∈ Finset.range (2 ^ m),
      a ((k * 2 ^ m + r) / 2 ^ m) ω *
        (W ((((k * 2 ^ m + r : ℕ) : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ (n + m)) ω -
          W (((k * 2 ^ m + r : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m)) ω) =
      a k ω * (g (r + 1) - g r) := by
    intro r hr
    have ht : ((k * 2 ^ m + r : ℕ) : ℝ≥0) + 1 = ((k * 2 ^ m + (r + 1) : ℕ) : ℝ≥0) := by
      push_cast; ring
    rw [hdiv r hr, ht]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_range_sub]
  have h1 : ((k * 2 ^ m + 2 ^ m : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m) =
      ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n := by
    push_cast; rw [pow_add]; field_simp; try ring
  have h0 : ((k * 2 ^ m + 0 : ℕ) : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m) =
      (k : ℝ≥0) * t / (2 : ℝ≥0) ^ n := by
    push_cast; rw [pow_add]; field_simp; try ring
  simp only [hg, h1, h0]

end M6refine

section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

/-- Left-point coefficients of a process on the dyadic grid of mesh `t / 2^n`. -/
noncomputable def leftCoef (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  H (dyTime t n k) ω

/-- Oscillation event: two dyadic times in `[0,t]` at distance at most `δ` at which `H` differs
by more than `η`. -/
def oscSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (δ η : ℝ) : Set Ω :=
  ⋃ p : (ℕ × ℕ) × (ℕ × ℕ), {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
    |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
    η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|}

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _

theorem dyTime_coarse (t : ℝ≥0) (n m k : ℕ) :
    dyTime t n (k / 2 ^ m) ≤ dyTime t (n + m) k ∧
    (dyTime t (n + m) k : ℝ) - dyTime t n (k / 2 ^ m) ≤ (t : ℝ) / 2 ^ n := by
  have hk := Nat.div_add_mod k (2 ^ m)
  have hr := Nat.mod_lt k (show 0 < 2 ^ m by positivity)
  set q := k / 2 ^ m
  set r := k % 2 ^ m
  have hkR : (k : ℝ) = 2 ^ m * q + r := by exact_mod_cast hk.symm
  have hrR : (r : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast hr
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have e1 : (dyTime t (n + m) k : ℝ) = (k : ℝ) * t / (2 ^ n * 2 ^ m) := by
    simp [dyTime, pow_add]
  have e2 : (dyTime t n q : ℝ) = (q : ℝ) * t / 2 ^ n := by simp [dyTime]
  have key : (dyTime t (n + m) k : ℝ) - dyTime t n q = (r : ℝ) * t / (2 ^ n * 2 ^ m) := by
    rw [e1, e2, hkR]; field_simp; try ring
  constructor
  · rw [← NNReal.coe_le_coe, ← sub_nonneg, key]; positivity
  · rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ 2 ^ m by linarith) ht
    calc (r : ℝ) * t * 2 ^ n ≤ 2 ^ m * t * 2 ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = t * (2 ^ n * 2 ^ m) := by ring

theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩

theorem oscSet_nullMeasurable [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (δ η : ℝ) :
    NullMeasurableSet (oscSet H t δ η) P := by
  refine NullMeasurableSet.iUnion fun p => ?_
  by_cases hc : p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
      |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ
  · have heq : {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
        |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
        η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} =
        {ω | η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} := by
      ext ω
      exact ⟨fun h => h.2.2.2, fun h => ⟨hc.1, hc.2.1, hc.2.2, h⟩⟩
    rw [heq]
    exact AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (continuous_abs.comp_aestronglyMeasurable ((hHm _).sub (hHm _)))
  · have heq : {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
        |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
        η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|} = ∅ := by
      ext ω
      exact ⟨fun h => absurd ⟨h.1, h.2.1, h.2.2.1⟩ hc, fun h => h.elim⟩
    rw [heq]
    exact nullMeasurableSet_empty

theorem iInter_oscSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  have huc : UniformContinuousOn (fun s => H s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hHc ω).continuousOn
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have htn : (t : ℝ) / 2 ^ n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    have hnδ := mul_lt_mul_of_pos_right h2n hδ
    linarith only [hn, hnδ]
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  exact absurd hp4 (not_lt.2 this.le)

theorem oscSet_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => P (oscSet H t ((t : ℝ) / 2 ^ n) η)) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => oscSet H t ((t : ℝ) / 2 ^ n) η) := by
    intro n n' hnn'
    exact oscSet_mono H t (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hnn')) η
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun n => oscSet_nullMeasurable hHm t ((t : ℝ) / 2 ^ n) η) hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_oscSet_eq_empty hHc t hη, measure_empty] at this
  exact this

end M6osc

section M6cauchy
variable [MeasurableSpace Ω]

/-- L² Cauchy estimate for left-point Ito sums of a bounded adapted process: refining the grid
from `t/2^n` to `t/2^(n+m)` changes the sum by at most `η² t + 4K² t P(osc)` in mean square. -/
theorem leftPoint_cauchy_bound {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ s ω, |H s ω| ≤ K) (t : ℝ≥0) (n m : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    ∫ ω, (itoStepSum (fun s ω => W s ω j) t (n + m) (leftCoef H t (n + m)) ω -
        itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω) ^ 2 ∂P ≤
      η ^ 2 * t + 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  let D : ℕ → Ω → ℝ := fun k ω => leftCoef H t (n + m) k ω - leftCoef H t n (k / 2 ^ m) ω
  have hdiff : ∀ ω, itoStepSum (fun s ω => W s ω j) t (n + m) (leftCoef H t (n + m)) ω -
      itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω =
      itoStepSum (fun s ω => W s ω j) t (n + m) D ω := by
    intro ω
    rw [itoStepSum_refine _ t n m (leftCoef H t n) ω, itoStepSum_sub]
  simp_rw [hdiff]
  have hDm : ∀ k : ℕ, k < 2 ^ (n + m) → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ (n + m))] (D k) := by
    intro k _
    exact (hHm (dyTime t (n + m) k)).sub ((hHm (dyTime t n (k / 2 ^ m))).mono
      (completedBrownianPast_mono P W _ (dyTime_coarse t n m k).1) le_rfl)
  have hDb : ∀ k : ℕ, k < 2 ^ (n + m) → ∀ ω, |D k ω| ≤ 2 * K := by
    intro k _ ω
    have h1 := abs_le.1 (hHb (dyTime t (n + m) k) ω)
    have h2 := abs_le.1 (hHb (dyTime t n (k / 2 ^ m)) ω)
    exact abs_le.2 ⟨by simp only [D, leftCoef]; linarith only [h1.1, h2.2],
      by simp only [D, leftCoef]; linarith only [h1.2, h2.1]⟩
  rw [itoStepSum_isometry hW x₀ t (n + m) j D hDm (2 * K) hDb]
  have hint : ∀ k ∈ Finset.range (2 ^ (n + m)), Integrable (fun ω => D k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hDm k hk')).pow 2) ((2 * K) ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDb k hk' ω) 2
  set h : ℝ := ((t / (2 : ℝ≥0) ^ (n + m) : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hNh : ((2 ^ (n + m) : ℕ) : ℝ) * h = t := by
    rw [hhdef]; push_cast; field_simp
  have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  set O := toMeasurable P (oscSet H t ((t : ℝ) / 2 ^ n) η) with hO
  have hOm : MeasurableSet O := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h ≤
      η ^ 2 * t + 4 * K ^ 2 * t * O.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ O
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hs : ∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2 ≤
          (Finset.range (2 ^ (n + m))).card • ((2 * K) ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have := hDb k (Finset.mem_range.1 hk) ω
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      have := mul_le_mul_of_nonneg_right hs hh
      calc (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h
          ≤ ((2 ^ (n + m) : ℕ) : ℝ) * (2 * K) ^ 2 * h := this
        _ = 4 * K ^ 2 * (((2 ^ (n + m) : ℕ) : ℝ) * h) := by ring
        _ = 4 * K ^ 2 * t := by rw [hNh]
        _ ≤ η ^ 2 * t + 4 * K ^ 2 * t := le_add_of_nonneg_left (by positivity)
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hno : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h' => hω (subset_toMeasurable _ _ h')
      have hs : ∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2 ≤
          (Finset.range (2 ^ (n + m))).card • (η ^ 2) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        have hDk : |D k ω| ≤ η := by
          by_contra hcon
          push Not at hcon
          refine hno (Set.mem_iUnion.2 ⟨((n + m, k), (n, k / 2 ^ m)), hk'.le, ?_, ?_, hcon⟩)
          · show k / 2 ^ m ≤ 2 ^ n
            rw [pow_add] at hk'
            exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hk' |>.le
          · show |(dyTime t (n + m) k : ℝ) - dyTime t n (k / 2 ^ m)| ≤ (t : ℝ) / 2 ^ n
            have hc := dyTime_coarse t n m k
            rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hc.1))]
            exact hc.2
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hDk 2
      rw [Finset.card_range, nsmul_eq_mul] at hs
      calc (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h
          ≤ ((2 ^ (n + m) : ℕ) : ℝ) * η ^ 2 * h := mul_le_mul_of_nonneg_right hs hh
        _ = η ^ 2 * (((2 ^ (n + m) : ℕ) : ℝ) * h) := by ring
        _ = η ^ 2 * t := by rw [hNh]
  have hOreal : P.real O = P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
    simp only [measureReal_def, hO, measure_toMeasurable]
  have hIi : Integrable (fun ω => 4 * K ^ 2 * (t : ℝ) * O.indicator 1 ω) P :=
    ((integrable_indicator_iff hOm).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _
  calc ∑ k ∈ Finset.range (2 ^ (n + m)), (∫ ω, D k ω ^ 2 ∂P) * h
      = ∫ ω, (∑ k ∈ Finset.range (2 ^ (n + m)), D k ω ^ 2) * h ∂P := by
        rw [integral_mul_const, integral_finsetSum _ hint, Finset.sum_mul]
    _ ≤ ∫ ω, (η ^ 2 * t + 4 * K ^ 2 * t * O.indicator 1 ω) ∂P :=
        integral_mono ((integrable_finsetSum _ hint).mul_const h)
          ((integrable_const _).add hIi) hpt
    _ = η ^ 2 * t + 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ n) η) := by
        rw [integral_add (integrable_const _) hIi, integral_const, integral_const_mul,
          integral_indicator_one hOm, hOreal]
        simp

end M6cauchy

section M6limit
variable [MeasurableSpace Ω]

theorem dist_toLp_lt_of_integral_sq {P : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) {ε : ℝ} (hε : 0 < ε) (h : ∫ ω, (f ω - g ω) ^ 2 ∂P < ε ^ 2) :
    dist (hf.toLp f) (hg.toLp g) < ε := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp,
    (hf.sub hg).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hA : ∫ ω, ‖(f - g) ω‖ ^ (ENNReal.toReal 2) ∂P = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
    congr 1; funext ω; simp [Real.norm_eq_abs, sq_abs]
  rw [hA]
  have hnn : 0 ≤ ∫ ω, (f ω - g ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  have h2 : (ENNReal.toReal 2)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [h2, ← Real.sqrt_eq_rpow, Real.sqrt_lt' hε]
  exact h

/-- Left-point Ito sums of a bounded adapted process with continuous paths converge in
probability (indeed in `L²`). -/
theorem leftPoint_tendstoInMeasure {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ s ω, |H s ω| ≤ K) (t : ℝ≥0) :
    ∃ J : Ω → ℝ, TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n)) atTop J := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hS : ∀ n, MemLp (itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n)) 2 P := fun n =>
    itoStepSum_memLp hW t n j _
      (fun k _ => aestronglyMeasurable_of_completedPast hW x₀ _ (hHm (dyTime t n k))) K
      (fun k _ ω => hHb _ ω)
  let f : ℕ → Lp ℝ 2 P := fun n => (hS n).toLp _
  have hcau : CauchySeq f := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hε2 : 0 < ε ^ 2 := by positivity
    have ht : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    set η : ℝ := min 1 (ε ^ 2 / 2 / ((t : ℝ) + 1)) with hηdef
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    have hηt : η ^ 2 * t < ε ^ 2 / 2 := by
      have h1 : η ≤ 1 := min_le_left _ _
      have h2 : η ≤ ε ^ 2 / 2 / ((t : ℝ) + 1) := min_le_right _ _
      have h3 : η ^ 2 ≤ η := by linarith only [mul_le_mul_of_nonneg_right h1 hηpos.le]
      have h4 : η * ((t : ℝ) + 1) ≤ ε ^ 2 / 2 := by rwa [le_div_iff₀ (by positivity)] at h2
      linarith only [mul_le_mul_of_nonneg_right h3 ht, h4, hηpos]
    have hosc := oscSet_tendsto
      (fun s => aestronglyMeasurable_of_completedPast hW x₀ s (hHm s)) hHc t hηpos
    have hosc' : Tendsto (fun n : ℕ => P.real (oscSet H t ((t : ℝ) / 2 ^ n) η)) atTop
        (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hosc
      simpa [measureReal_def, Function.comp_def] using this
    have hev := hosc'.eventually (gt_mem_nhds
      (show (0 : ℝ) < (ε ^ 2 / 2) / (4 * K ^ 2 * t + 1) by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine dist_toLp_lt_of_integral_sq (hS _) (hS _) hε ?_
    have hb := leftPoint_cauchy_bound hW x₀ j hHm hK hHb t N m hηpos.le
    have hpN := hN N le_rfl
    have hq : 4 * K ^ 2 * t * P.real (oscSet H t ((t : ℝ) / 2 ^ N) η) < ε ^ 2 / 2 := by
      have hc : 0 ≤ 4 * K ^ 2 * (t : ℝ) := by positivity
      have hr : 0 ≤ P.real (oscSet H t ((t : ℝ) / 2 ^ N) η) := measureReal_nonneg
      rw [lt_div_iff₀ (by positivity)] at hpN
      linarith only [hpN, hr]
    linarith only [hb, hηt, hq]
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨F, (tendstoInMeasure_of_tendsto_Lp hF).congr_left (fun n => (hS n).coeFn_toLp)⟩

end M6limit

section M6trunc

/-- Truncation of a process at level `R`. -/
noncomputable def clampH (H : ℝ≥0 → Ω → ℝ) (R : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  max (-R) (min (H s ω) R)

theorem abs_clampH_le (H : ℝ≥0 → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (s : ℝ≥0) (ω : Ω) :
    |clampH H R s ω| ≤ R := by
  unfold clampH
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith only [hR]) (min_le_right _ _)⟩

theorem clampH_eq_of_abs_le (H : ℝ≥0 → Ω → ℝ) {R : ℝ} {s : ℝ≥0} {ω : Ω} (h : |H s ω| ≤ R) :
    clampH H R s ω = H s ω := by
  unfold clampH
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem clampH_continuous {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω) (R : ℝ)
    (ω : Ω) : Continuous fun s => clampH H R s ω := by
  unfold clampH
  exact continuous_const.max ((hHc ω).min continuous_const)

theorem clampH_measurable {m : MeasurableSpace Ω} {H : ℝ≥0 → Ω → ℝ} {s : ℝ≥0}
    (h : Measurable[m] (H s)) (R : ℝ) : Measurable[m] (clampH H R s) := by
  unfold clampH
  exact measurable_const.max (h.min measurable_const)

/-- Event that `|H|` exceeds `R` at some dyadic time of `[0,t]`. -/
def bigSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (R : ℝ) : Set Ω :=
  ⋃ p : ℕ × ℕ, {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|}

theorem abs_le_of_not_mem_bigSet {H : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {R : ℝ} {ω : Ω}
    (h : ω ∉ bigSet H t R) {N i : ℕ} (hi : i ≤ 2 ^ N) : |H (dyTime t N i) ω| ≤ R := by
  by_contra hc
  exact h (Set.mem_iUnion.2 ⟨(N, i), hi, lt_of_not_ge hc⟩)

theorem bigSet_nullMeasurable [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, AEStronglyMeasurable (H s) P) (t : ℝ≥0) (R : ℝ) :
    NullMeasurableSet (bigSet H t R) P := by
  refine NullMeasurableSet.iUnion fun p => ?_
  by_cases hc : p.2 ≤ 2 ^ p.1
  · have heq : {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|} =
        {ω | R < |H (dyTime t p.1 p.2) ω|} := by
      ext ω; exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
    rw [heq]
    exact AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const
      (continuous_abs.comp_aestronglyMeasurable (hHm _))
  · have heq : {ω | p.2 ≤ 2 ^ p.1 ∧ R < |H (dyTime t p.1 p.2) ω|} = ∅ := by
      ext ω; exact ⟨fun h => absurd h.1 hc, fun h => h.elim⟩
    rw [heq]
    exact nullMeasurableSet_empty

theorem iInter_bigSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) : (⋂ R : ℕ, bigSet H t R) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hHc ω).continuousOn
  obtain ⟨R, hR⟩ := exists_nat_gt C
  obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.1 (hall R)
  have := hC _ ⟨zero_le, dyTime_le t hp1⟩
  rw [Real.norm_eq_abs] at this
  linarith

theorem bigSet_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) :
    Tendsto (fun R : ℕ => P (bigSet H t R)) atTop (𝓝 0) := by
  have hanti : Antitone (fun R : ℕ => bigSet H t R) := by
    intro R R' hRR' ω hω
    obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.1 hω
    exact Set.mem_iUnion.2 ⟨p, hp1, lt_of_le_of_lt (by exact_mod_cast hRR') hp2⟩
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun R : ℕ => bigSet_nullMeasurable hHm t (R : ℝ)) hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_bigSet_eq_empty hHc t, measure_empty] at this
  exact this

/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht, mul_comm (2 ^ n : ℝ)]; exact mul_le_mul_of_nonneg_right hu.2 h2.le
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith only [this, hkR]
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith only [hlt]
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith only [hge]
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1', this, hlo]
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1, this, hhi]
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

/-- Off the oscillation event of mesh `t/2^n`, `H` at the left grid point `t_k` is within `η` of
`H u` for every `u ∈ [t_k, t_{k+1}]` (dyadic approximation of `u` from the left + continuity). -/
theorem abs_H_sub_le_of_not_mem_oscSet {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n k : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω}
    (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η) (hk : k < 2 ^ n) {u : ℝ} (hu0 : 0 ≤ u)
    (hlo : (k : ℝ) * t.val / 2 ^ n ≤ u) (hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n)
    (hut : u ≤ t.val) :
    |H (dyTime t n k) ω - H u.toNNReal ω| ≤ η := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · have hu : u = 0 := le_antisymm (h0 ▸ hut) hu0
    have hd : dyTime t n k = 0 := by
      have : t = 0 := NNReal.coe_eq_zero.1 h0.symm
      simp [dyTime, this]
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    simp [hs, dyTime]
  have hy0 : ∀ m, 0 ≤ y m := fun m => by simp only [hy]; positivity
  have hyt : ∀ m, y m * t.val / 2 ^ (m + n) = u := fun m => by
    simp only [hy]; field_simp
  have hs_le : ∀ m, (s m : ℝ) ≤ u := fun m => by
    rw [hsR, ← hyt m]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le (hy0 m)) ht)
      (by positivity)
  have hs_gt : ∀ m, u - t.val / 2 ^ (m + n) ≤ (s m : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (y m)
    have h3 : u - t.val / 2 ^ (m + n) = (y m - 1) * t.val / 2 ^ (m + n) := by
      rw [← hyt m]; field_simp; try ring
    rw [hsR, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [h1]) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      have h2m := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [h2m]
    have hfl : ((k * 2 ^ m : ℕ) : ℝ) ≤ (⌊y m⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor hkm
    have e : (dyTime t n k : ℝ) = ((k * 2 ^ m : ℕ) : ℝ) * t.val / 2 ^ (m + n) := by
      simp only [dyTime]; push_cast; rw [pow_add]; field_simp; try rfl
    rw [e, hsR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfl ht) (by positivity)
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by simp [dyTime]
  have hbound : ∀ m, |H (dyTime t n k) ω - H (s m) ω| ≤ η := fun m => by
    by_contra hc
    refine hω (Set.mem_iUnion.2 ⟨((n, k), (m + n, ⌊y m⌋₊)), hk.le, ?_, ?_, lt_of_not_ge hc⟩)
    · refine Nat.floor_le_of_le ?_
      simp only [hy]
      rw [div_le_iff₀ hpos]; push_cast
      exact (mul_le_mul_of_nonneg_right hut (by positivity)).trans_eq (mul_comm _ _)
    · show |(dyTime t n k : ℝ) - (s m : ℝ)| ≤ (t : ℝ) / 2 ^ n
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hs_ge m])]
      have hcell : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by
        ring
      have hsm := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [hcell, hsm, hhi]
  have hreal : Tendsto (fun m => (s m : ℝ)) atTop (𝓝 u) := by
    have hpow : Tendsto (fun m : ℕ => t.val / 2 ^ (m + n)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))).comp
        (tendsto_add_atTop_nat n)
      exact Tendsto.div_atTop tendsto_const_nhds h
    have hlow : Tendsto (fun m : ℕ => u - t.val / 2 ^ (m + n)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa [Function.comp_def] using this
  have hcont : Continuous fun x : ℝ≥0 => |H (dyTime t n k) ω - H x ω| :=
    (continuous_const.sub (hHc ω)).abs
  exact le_of_tendsto' ((hcont.tendsto u.toNNReal).comp hnn) (fun m => hbound m)

/-- Pathwise approximation: off the oscillation event, a step process with the left-point values
of `H` is uniformly `η`-close to `H` on `(0,t]`, so its integrated squared error is at most
`η² t`. -/
theorem integral_stepValue_sub_sq_le {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω} (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η)
    {c : ℕ → Ω → ℝ} (hc : ∀ k < 2 ^ n, c k ω = H (dyTime t n k) ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω - H u.toNNReal ω) ^ 2 ≤ η ^ 2 * t.val := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖(itoStepValue t n c u ω - H u.toNNReal ω) ^ 2‖ ≤ η ^ 2 := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ := itoStepValue_eq_cell t n c hu ω
    rw [hval, hc k hk, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_H_sub_le_of_not_mem_oscSet hHc t n k hη hω hk hu.1.le hlo.le hhi hu.2) 2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- The approximation clause of `HasBrownianItoIntegral` for the truncated left-point
coefficients `clamp_n (H t_k)` of a continuous process. -/
theorem clampLeft_approx [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, AEStronglyMeasurable (H s) P)
    (hHc : ∀ ω, Continuous fun s => H s ω) (t : ℝ≥0) :
    TendstoInMeasure P (fun (n : ℕ) ω => ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (leftCoef (clampH H n) t n) u ω - H u.toNNReal ω) ^ 2)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have ht : (0 : ℝ) ≤ t.val := t.2
  set η : ℝ := min 1 (ε / (2 * (t.val + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hηt : η ^ 2 * t.val < ε := by
    have h1 : η ≤ 1 := min_le_left _ _
    have h2 : η ≤ ε / (2 * (t.val + 1)) := min_le_right _ _
    have h3 : η ^ 2 * t.val ≤ η * t.val := by
      have : η ^ 2 ≤ η := by linarith only [mul_le_mul_of_nonneg_right h1 hη.le]
      exact mul_le_mul_of_nonneg_right this ht
    have h4 : η * t.val ≤ ε / (2 * (t.val + 1)) * t.val := mul_le_mul_of_nonneg_right h2 ht
    have h5 : ε / (2 * (t.val + 1)) * t.val < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; linarith only [mul_nonneg hε.le ht, hε]
    linarith only [h3, h4, h5]
  have hsum := (oscSet_tendsto hHm hHc t hη).add (bigSet_tendsto hHm hHc t)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  have hc : ∀ k < 2 ^ n, leftCoef (clampH H n) t n k ω = H (dyTime t n k) ω := fun k hk =>
    clampH_eq_of_abs_le H (abs_le_of_not_mem_bigSet hcon.2 hk.le)
  have hle := integral_stepValue_sub_sq_le hHc t n hη.le hcon.1 hc
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..t.val,
      (itoStepValue t n (leftCoef (clampH H n) t n) u ω - H u.toNNReal ω) ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun u _ => sq_nonneg _)
  rw [abs_of_nonneg hnn] at hω
  linarith only [hω, hle, hηt]

/-- Limits in probability of two sequences that agree on a set `A` agree a.e. on `A`. -/
theorem tendstoInMeasure_ae_eq_on [MeasurableSpace Ω] {P : Measure Ω} {f f' : ℕ → Ω → ℝ}
    {g g' : Ω → ℝ} {A : Set Ω} (hf : TendstoInMeasure P f atTop g)
    (hf' : TendstoInMeasure P f' atTop g') (hA : ∀ n, ∀ ω ∈ A, f n ω = f' n ω) :
    ∀ᵐ ω ∂P, ω ∈ A → g ω = g' ω := by
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_sub_real hf hf').exists_seq_tendsto_ae
  filter_upwards [hns] with ω hω hωA
  have h0 : Tendsto (fun i => f (ns i) ω - f' (ns i) ω) atTop (𝓝 0) := by
    simp only [hA _ ω hωA, sub_self]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hω h0
  linarith

/-- Localization: `f n → J` in probability if, off sets of arbitrarily small measure, `f n`
eventually coincides with a sequence converging to a limit that equals `J` a.e. there. -/
theorem tendstoInMeasure_of_local [MeasurableSpace Ω] {P : Measure Ω} {f : ℕ → Ω → ℝ}
    {J : Ω → ℝ}
    (h : ∀ δ : ℝ≥0∞, 0 < δ → ∃ B : Set Ω, P B ≤ δ ∧ ∃ g : ℕ → Ω → ℝ, ∃ G : Ω → ℝ,
      TendstoInMeasure P g atTop G ∧ (∀ᶠ n in atTop, ∀ ω ∉ B, f n ω = g n ω) ∧
      (∀ᵐ ω ∂P, ω ∉ B → J ω = G ω)) :
    TendstoInMeasure P f atTop J := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨B, hB, g, G, hg, hfg, hJG⟩ := h (δ / 2) hδ2
  rw [tendstoInMeasure_iff_dist] at hg
  have hg' := (ENNReal.tendsto_nhds_zero.1 (hg ε hε)) (δ / 2) hδ2
  rw [ae_iff] at hJG
  filter_upwards [hg', hfg] with n hn hfn
  calc P {ω | ε ≤ dist (f n ω) (J ω)}
      ≤ P (B ∪ {ω | ε ≤ dist (g n ω) (G ω)} ∪ {ω | ¬(ω ∉ B → J ω = G ω)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωB : ω ∈ B
        · exact Or.inl (Or.inl hωB)
        by_cases hJ : J ω = G ω
        · refine Or.inl (Or.inr ?_)
          simp only [Set.mem_setOf_eq] at hω ⊢
          rwa [← hfn ω hωB, ← hJ]
        · exact Or.inr (fun h => hJ (h hωB))
    _ ≤ P B + P {ω | ε ≤ dist (g n ω) (G ω)} + P {ω | ¬(ω ∉ B → J ω = G ω)} :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 + 0 := by rw [hJG]; gcongr
    _ = δ := by rw [add_zero, ENNReal.add_halves]

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate, in the sense of `HasBrownianItoIntegral` (truncated left-point
sums; localization by truncation `clamp_R H` on the events `{sup |H| ≤ R}`). -/
theorem exists_hasBrownianItoIntegral_clamp {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J ∧ ∀ t, TendstoInMeasure P
        (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  have hHae : ∀ s, AEStronglyMeasurable (H s) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (hHm s)
  have key : ∀ t : ℝ≥0, ∃ J : Ω → ℝ, TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop J := by
    intro t
    have hJR : ∀ R : ℕ, ∃ JR : Ω → ℝ, TendstoInMeasure P
        (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R) t n)) atTop JR :=
      fun R => leftPoint_tendstoInMeasure hW x₀ j (fun s => clampH_measurable (hHm s) (R : ℝ))
        (clampH_continuous hHc (R : ℝ)) (Nat.cast_nonneg R)
        (abs_clampH_le H (Nat.cast_nonneg R)) t
    choose JR hJR using hJR
    have hagree : ∀ R R' : ℕ, R ≤ R' → ∀ n, ∀ ω ∉ bigSet H t R,
        itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R) t n) ω =
          itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H R') t n) ω := by
      intro R R' hRR' n ω hω
      unfold itoStepSum
      refine Finset.sum_congr rfl fun k hk => ?_
      have hb := abs_le_of_not_mem_bigSet hω (N := n) (i := k) (Finset.mem_range.1 hk).le
      have hb' : |H (dyTime t n k) ω| ≤ (R' : ℝ) := hb.trans (by exact_mod_cast hRR')
      simp only [leftCoef, clampH_eq_of_abs_le H hb, clampH_eq_of_abs_le H hb']
    have hae : ∀ᵐ ω ∂P, ∀ R R' : ℕ, R ≤ R' → ω ∉ bigSet H t R → JR R ω = JR R' ω := by
      rw [ae_all_iff]; intro R; rw [ae_all_iff]; intro R'
      by_cases hRR : R ≤ R'
      · filter_upwards [tendstoInMeasure_ae_eq_on (A := (bigSet H t R)ᶜ) (hJR R) (hJR R')
          (fun n ω hω => hagree R R' hRR n ω hω)] with ω hω _ h2 using hω h2
      · exact Eventually.of_forall fun ω h => absurd h hRR
    have hex : ∀ ω, ∃ R : ℕ, ω ∉ bigSet H t R := by
      intro ω
      by_contra hc
      push Not at hc
      have hmem : ω ∈ ⋂ R : ℕ, bigSet H t R := Set.mem_iInter.2 hc
      rw [iInter_bigSet_eq_empty hHc t] at hmem
      exact hmem
    classical
    refine ⟨fun ω => JR (Nat.find (hex ω)) ω, tendstoInMeasure_of_local fun δ hδ => ?_⟩
    obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 (bigSet_tendsto hHae hHc t)) δ hδ).exists
    refine ⟨bigSet H t R, hR, _, JR R, hJR R, ?_, ?_⟩
    · filter_upwards [eventually_ge_atTop R] with n hn ω hω
      exact (hagree R n hn n ω hω).symm
    · filter_upwards [hae] with ω hω hωB
      exact hω _ _ (Nat.find_min' _ hωB) (Nat.find_spec (hex ω))
  choose J hJ using key
  refine ⟨J, ⟨fun t ω => ?_, fun t => ⟨fun n k => leftCoef (clampH H n) t n k, ?_, ?_, ?_, hJ t⟩⟩, hJ⟩
  · exact (((hHc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _
  · intro n k _
    exact clampH_measurable (hHm (dyTime t n k)) (n : ℝ)
  · intro n
    exact ⟨n, fun k _ ω => abs_clampH_le H (Nat.cast_nonneg n) _ ω⟩
  · exact clampLeft_approx hHae hHc t

end M6exist

section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero

section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e

section M8f
variable [MeasurableSpace Ω]

end M8f

section M8f2
variable [MeasurableSpace Ω]

theorem itoStepValue_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n c u ω =
      (∑ k ∈ Finset.range (2 ^ n), c k ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith only [this]
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

/-- M8f: left-point Riemann sums of a pathwise continuous process converge pathwise. -/
theorem riemann_tendsto {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω)) := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (t.val + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hempty := iInter_oscSet_eq_empty hHc t hη
  have hex : ∃ n0 : ℕ, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n0) η := by
    by_contra h
    push_neg at h
    have hmem : ω ∈ (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) := Set.mem_iInter.2 h
    rw [hempty] at hmem
    exact hmem
  obtain ⟨n0, hn0⟩ := hex
  refine ⟨n0, fun n hn => ?_⟩
  have hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h => hn0 (oscSet_mono H t
    (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hn)) η h)
  have hI := itoStepValue_integral t n (fun k ω => H (dyTime t n k) ω) ω
  have hHi : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω) volume 0 t.val :=
    ((hHc ω).comp continuous_real_toNNReal).intervalIntegrable _ _
  rw [Real.dist_eq, ← hI, ← intervalIntegral.integral_sub
    (itoStepValue_intervalIntegrable _ _ _ _) hHi]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖itoStepValue t n (fun k ω => H (dyTime t n k) ω) u ω - H u.toNNReal ω‖ ≤ η := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ :=
      itoStepValue_eq_cell t n (fun k ω => H (dyTime t n k) ω) hu ω
    rw [hval, Real.norm_eq_abs]
    exact abs_H_sub_le_of_not_mem_oscSet hHc t n k hη.le hω hk hu.1.le hlo.le hhi hu.2
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith only [mul_nonneg hε.le ht, hε]

end M8f2

section M8f3
variable [MeasurableSpace Ω]

end M8f3

section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g

section M8g2

theorem dyTime_coe (t : ℝ≥0) (n k : ℕ) : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by
  unfold dyTime; push_cast; rfl

end M8g2

section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

end M8g4

section M8g5
variable [MeasurableSpace Ω]

end M8g5

section M9a
variable [MeasurableSpace Ω]

end M9a

section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF

section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

/-- `(x, y, a) ↦ u` with `u (ixc k) = x k`, `u (iyc k) = y k`, `u iac = a`. -/
noncomputable def pack (x y : SDEState d) (a : ℝ) : SDEState (d + d + 1) :=
  WithLp.toLp 2 (fun i => Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j) i)

end M9c2

section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d

section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2

section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

theorem measurable_intervalIntegral_of_continuous [MeasurableSpace Ω] (m : MeasurableSpace Ω)
    {H : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (hHm : ∀ s, s ≤ t → Measurable[m] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    Measurable[m] (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) := by
  refine measurable_of_tendsto_metrizable (f := fun n ω => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) (fun n => ?_)
    (tendsto_pi_nhds.2 fun ω => riemann_tendsto hHc t ω)
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun k hk =>
    hHm _ (dyTime_le t (Finset.mem_range.1 hk).le)

end M9e1

section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2

end ItoLib

-- ===== E =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

/-- Riemann-Stieltjes integration by parts on dyadic grids. -/
theorem rs_ibp {t : ℝ} (ht : 0 ≤ t) {w h D : ℝ → ℝ} (hw : Continuous w)
    (hD : IntervalIntegrable D volume 0 t)
    (hh : ∀ s ∈ Set.Icc (0 : ℝ) t, h s = h 0 + ∫ v in (0 : ℝ)..s, D v) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (2 ^ n),
      h ((k : ℝ) * t / 2 ^ n) * (w (((k : ℝ) + 1) * t / 2 ^ n) - w ((k : ℝ) * t / 2 ^ n)))
      atTop (𝓝 (h t * w t - h 0 * w 0 - ∫ v in (0 : ℝ)..t, w v * D v)) := by
  set s : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * t / 2 ^ n with hs
  have hs_mem : ∀ n k, k ≤ 2 ^ n → s n k ∈ Set.Icc (0 : ℝ) t := fun n k hk => by
    refine ⟨by positivity, ?_⟩
    simp only [hs]
    rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
    nlinarith
  have hs_mono : ∀ n k, s n k ≤ s n (k + 1) := fun n k => by
    simp only [hs]; push_cast
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have hs_succ : ∀ n k, s n (k + 1) = ((k : ℝ) + 1) * t / 2 ^ n := fun n k => by
    simp only [hs]; push_cast; ring
  have hs_top : ∀ n, s n (2 ^ n) = t := fun n => by
    simp only [hs]; push_cast; field_simp
  have hs_zero : ∀ n, s n 0 = 0 := fun n => by simp [hs]
  have hsub : ∀ n k, k + 1 ≤ 2 ^ n → Set.uIcc (s n k) (s n (k + 1)) ⊆ Set.uIcc 0 t := fun n k hk => by
    rw [Set.uIcc_of_le (hs_mono n k), Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc (hs_mem n k (by omega)).1 (hs_mem n (k + 1) hk).2
  have hDk : ∀ n k, k + 1 ≤ 2 ^ n → IntervalIntegrable D volume (s n k) (s n (k + 1)) :=
    fun n k hk => hD.mono_set (hsub n k hk)
  have hwD : IntervalIntegrable (fun v => w v * D v) volume 0 t :=
    hD.continuousOn_mul hw.continuousOn
  have hAD : IntervalIntegrable (fun v => |D v|) volume 0 t := hD.abs
  set I := ∫ v in (0 : ℝ)..t, |D v| with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht fun v _ => abs_nonneg _
  -- the Abel identity
  have habel : ∀ n, ∑ k ∈ Finset.range (2 ^ n), h (s n k) * (w (s n (k + 1)) - w (s n k)) =
      h t * w t - h 0 * w 0 -
        ∑ k ∈ Finset.range (2 ^ n), ∫ v in (s n k)..(s n (k + 1)), w (s n (k + 1)) * D v := by
    intro n
    have htel := Finset.sum_range_sub (fun k => h (s n k) * w (s n k)) (2 ^ n)
    simp only [hs_top, hs_zero] at htel
    have hdiff : ∀ k ∈ Finset.range (2 ^ n),
        ∫ v in (s n k)..(s n (k + 1)), w (s n (k + 1)) * D v =
          w (s n (k + 1)) * (h (s n (k + 1)) - h (s n k)) := by
      intro k hk
      have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
      rw [intervalIntegral.integral_const_mul, hh _ (hs_mem n (k + 1) hk'),
        hh _ (hs_mem n k (by omega)), add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (hD.mono_set ?_) (hD.mono_set ?_)]
      · rw [Set.uIcc_of_le (hs_mem n (k + 1) hk').1, Set.uIcc_of_le ht]
        exact Set.Icc_subset_Icc le_rfl (hs_mem n (k + 1) hk').2
      · rw [Set.uIcc_of_le (hs_mem n k (by omega)).1, Set.uIcc_of_le ht]
        exact Set.Icc_subset_Icc le_rfl (hs_mem n k (by omega)).2
    rw [Finset.sum_congr rfl hdiff, ← htel, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : ∀ n, ∑ k ∈ Finset.range (2 ^ n), ∫ v in (s n k)..(s n (k + 1)), w v * D v =
      ∫ v in (0 : ℝ)..t, w v * D v := fun n => by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := s n), hs_zero, hs_top]
    intro k hk
    exact hwD.mono_set (hsub n k hk)
  have hsplitA : ∀ n, ∑ k ∈ Finset.range (2 ^ n), ∫ v in (s n k)..(s n (k + 1)), |D v| = I :=
    fun n => by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := s n), hs_zero, hs_top]
    intro k hk
    exact hAD.mono_set (hsub n k hk)
  -- uniform continuity
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := t)).uniformContinuousOn_of_continuous
    hw.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδw⟩ := huc (ε / (I + 1)) (by positivity)
  have hmesh : Tendsto (fun n : ℕ => t / 2 ^ n) atTop (𝓝 0) := by
    simp_rw [div_eq_mul_inv, ← inv_pow]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul t
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hmesh) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hmn : t / 2 ^ n < δ := by
    have := hN n hn; rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    exact this
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      |(∫ v in (s n k)..(s n (k + 1)), w (s n (k + 1)) * D v) -
        ∫ v in (s n k)..(s n (k + 1)), w v * D v| ≤
        ε / (I + 1) * ∫ v in (s n k)..(s n (k + 1)), |D v| := by
    intro k hk
    have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
    rw [← intervalIntegral.integral_sub ((hDk n k hk').const_mul _)
      ((hDk n k hk').continuousOn_mul hw.continuousOn), ← intervalIntegral.integral_const_mul]
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le (hs_mono n k)
      (Eventually.of_forall fun v hv => ?_) (((hDk n k hk').abs).const_mul _)
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hv0 : v ∈ Set.Icc (0 : ℝ) t :=
      ⟨(hs_mem n k (by omega)).1.trans hv.1.le, hv.2.trans (hs_mem n (k + 1) hk').2⟩
    have hd : dist (s n (k + 1)) v < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hv.2])]
      have : s n (k + 1) - s n k = t / 2 ^ n := by simp only [hs]; push_cast; ring
      linarith [hv.1]
    exact (le_of_lt (by simpa [Real.dist_eq] using hδw _ (hs_mem n (k + 1) hk') _ hv0 hd))
  have e : ∀ k : ℕ, h ((k : ℝ) * t / 2 ^ n) * (w (((k : ℝ) + 1) * t / 2 ^ n) - w ((k : ℝ) * t / 2 ^ n))
      = h (s n k) * (w (s n (k + 1)) - w (s n k)) := fun k => by rw [hs_succ]
  rw [Real.dist_eq, Finset.sum_congr rfl fun k _ => e k, habel n, ← hsplit n]
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.range (2 ^ n))
    (f := fun k => (∫ v in (s n k)..(s n (k + 1)), w (s n (k + 1)) * D v) -
        ∫ v in (s n k)..(s n (k + 1)), w v * D v)
  have hb := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, hsplitA n] at hb
  have hlt : ε / (I + 1) * I < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  calc _
      = |∑ k ∈ Finset.range (2 ^ n), ((∫ v in (s n k)..(s n (k + 1)), w (s n (k + 1)) * D v) -
          ∫ v in (s n k)..(s n (k + 1)), w v * D v)| := by
        rw [Finset.sum_sub_distrib, ← abs_neg]; congr 1; ring
    _ ≤ _ := hsum
    _ ≤ _ := hb
    _ < ε := hlt

/-- Pathwise limits of left-point sums of a continuous adapted integrand are Ito integrals. -/
theorem hasBrownianItoIntegral_of_pathwise [MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hlim : ∀ (t : ℝ≥0) ω, Tendsto
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω) atTop (𝓝 (J t ω))) :
    HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  obtain ⟨J', hJ', hconv⟩ := exists_hasBrownianItoIntegral_clamp hW x₀ j hHm hHc
  have hae : ∀ t, J' t =ᵐ[P] J t := by
    intro t
    -- clamped sums agree with plain sums for large n
    have hev : ∀ ω, ∀ᶠ n : ℕ in atTop,
        itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n) ω =
          itoStepSum (fun s ω => W s ω j) t n (leftCoef H t n) ω := by
      intro ω
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
        (hHc ω).continuousOn
      obtain ⟨N, hN⟩ := exists_nat_ge C
      filter_upwards [eventually_ge_atTop N] with n hn
      unfold itoStepSum
      refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      unfold leftCoef clampH
      have hle := hC _ (show dyTime t n k ∈ Set.Icc 0 t from
        ⟨bot_le, dyTime_le t (Finset.mem_range.1 hk).le⟩)
      rw [Real.norm_eq_abs, abs_le] at hle
      have : C ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    have hpw : ∀ ω, Tendsto (fun n =>
        itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n) ω) atTop (𝓝 (J t ω)) :=
      fun ω => (hlim t ω).congr' (by filter_upwards [hev ω] with n hn using hn.symm)
    have hmeas : ∀ n, AEStronglyMeasurable
        (itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) P := by
      intro n
      unfold itoStepSum
      refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact aestronglyMeasurable_of_completedPast hW x₀ _ (clampH_measurable (hHm _) _)
      · exact ((stdBrownian_coord_measurable hW _ j).sub
          (stdBrownian_coord_measurable hW _ j)).aestronglyMeasurable
    have hJt : TendstoInMeasure P (fun n =>
        itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) :=
      tendstoInMeasure_of_tendsto_ae hmeas (Eventually.of_forall hpw)
    have := tendstoInMeasure_ae_eq_on (A := Set.univ) (hconv t) hJt (fun _ _ _ => rfl)
    filter_upwards [this] with ω hω using hω (Set.mem_univ _)
  refine ⟨hJ'.1, fun t => ?_⟩
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := hJ'.2 t
  exact ⟨a, ha1, ha2, ha3, ha4.congr_right (hae t)⟩

/-- Ito integral of an integrand that is an indefinite time integral, by integration by parts:
`∫₀ᵗ H dW = H t W t - H 0 W 0 - ∫₀ᵗ W D`. -/
theorem hasBrownianItoIntegral_ibp [MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hD : ∀ (t : ℝ≥0) ω, IntervalIntegrable (fun u => D u ω) volume 0 t)
    (hHD : ∀ (s : ℝ≥0) ω, H s ω = H 0 ω + ∫ u in (0 : ℝ)..s, D u ω) :
    HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀)) (fun s ω => W s ω j) H
      (fun t ω => H t ω * W t ω j - H 0 ω * W 0 ω j -
        ∫ u in (0 : ℝ)..t, W u.toNNReal ω j * D u ω) := by
  refine hasBrownianItoIntegral_of_pathwise hW x₀ j hHm hHc fun t ω => ?_
  have hwc : Continuous fun r : ℝ => W r.toNNReal ω j :=
    ((EuclideanSpace.proj j).continuous.comp (hW.2.1 ω)).comp continuous_real_toNNReal
  have key := rs_ibp t.2 (w := fun r : ℝ => W r.toNNReal ω j) (h := fun r : ℝ => H r.toNNReal ω)
    (D := fun u => D u ω) hwc (hD t ω) (fun r hr => by
      have := hHD r.toNNReal ω
      rw [Real.coe_toNNReal _ hr.1] at this
      simpa using this)
  have e1 : ∀ n k : ℕ, ((k : ℝ) * t.val / 2 ^ n).toNNReal = dyTime t n k := fun n k => by
    ext; rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg k.cast_nonneg t.2) (by positivity)),
      dyTime_coe]
  have e2 : ∀ n k : ℕ, (((k : ℝ) + 1) * t.val / 2 ^ n).toNNReal =
      ((k : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ n := fun n k => by
    ext; rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg (by positivity) t.2) (by positivity))]
    push_cast; rfl
  have e3 : Real.toNNReal t.val = t := by ext; exact Real.coe_toNNReal _ t.2
  simp only [e1, e2, e3, show ((0 : ℝ).toNNReal) = 0 by simp] at key
  refine key.congr' (Eventually.of_forall fun n => ?_)
  unfold itoStepSum leftCoef dyTime
  rfl

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

/-- Slope of the interpolation on the cell `[k h, (k+1) h)`. -/
noncomputable def pwSlope (h : ℝ) (c : ℕ → ℝ) (u : ℝ) : ℝ := (c (⌊u / h⌋₊ + 1) - c ⌊u / h⌋₊) / h

/-- Piecewise-linear interpolation of `c` at the grid times `k h`. -/
noncomputable def pwLin (h : ℝ) (c : ℕ → ℝ) (u : ℝ) : ℝ := c 0 + ∫ v in (0 : ℝ)..u, pwSlope h c v

theorem pwSlope_measurable (h : ℝ) (c : ℕ → ℝ) : Measurable (pwSlope h c) := by
  unfold pwSlope
  have hf : Measurable fun u : ℝ => ⌊u / h⌋₊ := Nat.measurable_floor.comp (measurable_id.div_const h)
  exact (((measurable_from_nat (f := fun k => c (k + 1))).comp hf).sub
    ((measurable_from_nat (f := c)).comp hf)).div_const h

theorem pwSlope_eq_on_cell {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (k * h) ((k + 1) * h)) : pwSlope h c u = (c (k + 1) - c k) / h := by
  have : ⌊u / h⌋₊ = k := by
    rw [Nat.floor_eq_iff (div_nonneg ((mul_nonneg k.cast_nonneg hh.le).trans hu.1) hh.le)]
    exact ⟨(le_div_iff₀ hh).2 hu.1, (div_lt_iff₀ hh).2 hu.2⟩
  simp only [pwSlope, this]

theorem pwSlope_intervalIntegrable {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (pwSlope h c) volume a b := by
  -- bounded on bounded sets
  set N := ⌊max |a| |b| / h⌋₊ with hN
  set C := ∑ k ∈ Finset.range (N + 1), |(c (k + 1) - c k) / h| with hC
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
    (pwSlope_measurable h c).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun u hu => ?_)
  have hu' : |u| ≤ max |a| |b| := by
    rcases Set.mem_uIcc.1 (Set.uIoc_subset_uIcc hu) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;>
      constructor <;> linarith [neg_abs_le a, neg_abs_le b, le_abs_self a, le_abs_self b,
        le_max_left |a| |b|, le_max_right |a| |b|]
  have hk : ⌊u / h⌋₊ ≤ N := by
    rcases le_or_gt u 0 with hu0 | hu0
    · rw [Nat.floor_eq_zero.2 (by
        exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hu0 hh.le) one_pos)]
      exact Nat.zero_le _
    · exact Nat.floor_le_floor (div_le_div_of_nonneg_right ((le_abs_self u).trans hu') hh.le)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun k => |(c (k + 1) - c k) / h|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

theorem pwLin_continuous {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) : Continuous (pwLin h c) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => pwSlope_intervalIntegrable hh c a b) 0)

theorem integral_pwSlope_cell {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (k * h) ((k + 1) * h)) :
    ∫ v in (k * h : ℝ)..u, pwSlope h c v = (u - k * h) / h * (c (k + 1) - c k) := by
  have hae : ∀ᵐ v ∂volume, v ∈ Set.uIoc (k * h : ℝ) u → pwSlope h c v = (c (k + 1) - c k) / h := by
    filter_upwards [(Set.countable_singleton u).ae_notMem volume] with v hv hvI
    rw [Set.uIoc_of_le hu.1] at hvI
    exact pwSlope_eq_on_cell hh c k ⟨hvI.1.le, lt_of_lt_of_le
      (lt_of_le_of_ne hvI.2 (by simpa using hv)) hu.2⟩
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul]
  field_simp

theorem pwLin_grid {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) (k : ℕ) : pwLin h c (k * h) = c k := by
  induction k with
  | zero => simp [pwLin]
  | succ k ih =>
    have hcell := integral_pwSlope_cell hh c k (u := ((k + 1 : ℕ) : ℝ) * h)
      ⟨by push_cast; nlinarith, by push_cast; rfl⟩
    unfold pwLin at ih ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (k * h : ℝ))
      (pwSlope_intervalIntegrable hh c _ _) (pwSlope_intervalIntegrable hh c _ _), hcell]
    push_cast
    field_simp
    linarith

theorem pwLin_on_cell {h : ℝ} (hh : 0 < h) (c : ℕ → ℝ) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (k * h) ((k + 1) * h)) :
    pwLin h c u = c k + (u - k * h) / h * (c (k + 1) - c k) := by
  have hg := pwLin_grid hh c k
  unfold pwLin at hg ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (k * h : ℝ))
    (pwSlope_intervalIntegrable hh c _ _) (pwSlope_intervalIntegrable hh c _ _),
    integral_pwSlope_cell hh c k hu]
  linarith

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

/-- The path coordinate `j` as a function of real time. -/
noncomputable def wr (j : Fin d) (r : ℝ) : ℝ := w r.toNNReal j

/-- Increment of the scheme over `[k h, k h + r]` from the pair `(a, z) = (Z_{k-1}, Z_k)`. -/
noncomputable def cellInc (a z : SDEState d) (k : ℕ) (r : ℝ) : SDEState d :=
  WithLp.toLp 2 fun i => (∑ j, (s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h)) +
      (s₁ z (i, j) - s₁ a (i, j)) / h *
        (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v))) +
    b₁ a i * r + (b₁ z i - b₁ a i) * r ^ 2 / (2 * h)

/-- Grid values: `eulerZZ k = (Z_{k-1}, Z_k)`, `Z_{-1} = a`, `Z_0 = y`. -/
noncomputable def eulerZZ (a y : SDEState d) : ℕ → SDEState d × SDEState d
  | 0 => (a, y)
  | k + 1 => ((eulerZZ a y k).2,
      (eulerZZ a y k).2 + cellInc s₁ b₁ h w (eulerZZ a y k).1 (eulerZZ a y k).2 k h)

/-- Diffusion integrand of the scheme (continuous, piecewise linear in time). -/
noncomputable def eulerH (a y : SDEState d) (i j : Fin d) : ℝ → ℝ :=
  pwLin h (fun k => s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j))

/-- Its time derivative (piecewise constant). -/
noncomputable def eulerD (a y : SDEState d) (i j : Fin d) : ℝ → ℝ :=
  pwSlope h (fun k => s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j))

/-- Drift of the scheme (continuous, piecewise linear in time). -/
noncomputable def eulerB (a y : SDEState d) (i : Fin d) : ℝ → ℝ :=
  pwLin h (fun k => b₁ (eulerZZ s₁ b₁ h w a y k).1 i)

/-- The scheme in Ito form: `y + ∑ⱼ (H W |₀ᵘ - ∫ W D) + ∫ b`. -/
noncomputable def eulerY (a y : SDEState d) (u : ℝ) : SDEState d :=
  WithLp.toLp 2 fun i => y i + (∑ j, (eulerH s₁ b₁ h w a y i j u * wr w j u -
      eulerH s₁ b₁ h w a y i j 0 * wr w j 0 -
      ∫ v in (0 : ℝ)..u, wr w j v * eulerD s₁ b₁ h w a y i j v)) +
    ∫ v in (0 : ℝ)..u, eulerB s₁ b₁ h w a y i v

variable {s₁ b₁ h w}

theorem eulerZZ_succ_fst (a y : SDEState d) (k : ℕ) :
    (eulerZZ s₁ b₁ h w a y (k + 1)).1 = (eulerZZ s₁ b₁ h w a y k).2 := rfl

theorem wr_continuous (hw : Continuous w) (j : Fin d) : Continuous (wr w j) :=
  ((EuclideanSpace.proj j).continuous.comp hw).comp continuous_real_toNNReal

theorem eulerY_sub_cell (hh : 0 < h) (hw : Continuous w) (a y : SDEState d) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (k * h) ((k + 1) * h)) :
    eulerY s₁ b₁ h w a y u - eulerY s₁ b₁ h w a y (k * h) =
      cellInc s₁ b₁ h w (eulerZZ s₁ b₁ h w a y k).1 (eulerZZ s₁ b₁ h w a y k).2 k (u - k * h) := by
  have hk0 : (k * h : ℝ) ∈ Set.Icc (k * h) ((k + 1) * h) := ⟨le_rfl, by nlinarith⟩
  have hint : ∀ (c : ℕ → ℝ) (j : Fin d) (p q : ℝ),
      IntervalIntegrable (fun v => wr w j v * pwSlope h c v) volume p q := fun c j p q =>
    (pwSlope_intervalIntegrable hh c p q).continuousOn_mul (wr_continuous hw j).continuousOn
  have hintB : ∀ (c : ℕ → ℝ) (p q : ℝ), IntervalIntegrable (pwLin h c) volume p q :=
    fun c p q => (pwLin_continuous hh c).intervalIntegrable p q
  ext i
  simp only [eulerY, cellInc, PiLp.sub_apply, PiLp.toLp_apply]
  -- the drift part
  have hB : (∫ v in (0 : ℝ)..u, eulerB s₁ b₁ h w a y i v) -
      ∫ v in (0 : ℝ)..(k * h), eulerB s₁ b₁ h w a y i v =
      b₁ (eulerZZ s₁ b₁ h w a y k).1 i * (u - k * h) +
        (b₁ (eulerZZ s₁ b₁ h w a y k).2 i - b₁ (eulerZZ s₁ b₁ h w a y k).1 i) *
          (u - k * h) ^ 2 / (2 * h) := by
    simp only [eulerB]
    rw [intervalIntegral.integral_interval_sub_left (hintB _ _ _) (hintB _ _ _)]
    have hcongr : ∀ v ∈ Set.uIcc (k * h : ℝ) u,
        pwLin h (fun k => b₁ (eulerZZ s₁ b₁ h w a y k).1 i) v =
        b₁ (eulerZZ s₁ b₁ h w a y k).1 i + (v - k * h) / h *
          (b₁ (eulerZZ s₁ b₁ h w a y k).2 i - b₁ (eulerZZ s₁ b₁ h w a y k).1 i) := by
      intro v hv
      rw [Set.uIcc_of_le hu.1] at hv
      rw [pwLin_on_cell hh _ k ⟨hv.1, hv.2.trans hu.2⟩]
      rfl
    rw [intervalIntegral.integral_congr hcongr]
    set α := b₁ (eulerZZ s₁ b₁ h w a y k).1 i
    set β := b₁ (eulerZZ s₁ b₁ h w a y k).2 i - b₁ (eulerZZ s₁ b₁ h w a y k).1 i
    have hderiv : ∀ x ∈ Set.uIcc (k * h : ℝ) u, HasDerivAt
        (fun x : ℝ => α * x + (x - k * h) ^ 2 / (2 * h) * β) (α + (x - k * h) / h * β) x := by
      intro x _
      have h1 := ((hasDerivAt_id' x).const_mul α).add
        ((((hasDerivAt_id' x).sub_const ((k : ℝ) * h)).pow 2).div_const (2 * h) |>.mul_const β)
      exact h1.congr_deriv (by field_simp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_const.add (((continuous_id.sub continuous_const).div_const h).mul
        continuous_const)).intervalIntegrable _ _)]
    field_simp
    ring
  -- the diffusion part, coordinate by coordinate
  have hJ : ∀ j : Fin d,
      (eulerH s₁ b₁ h w a y i j u * wr w j u - eulerH s₁ b₁ h w a y i j 0 * wr w j 0 -
        ∫ v in (0 : ℝ)..u, wr w j v * eulerD s₁ b₁ h w a y i j v) -
      (eulerH s₁ b₁ h w a y i j (k * h) * wr w j (k * h) - eulerH s₁ b₁ h w a y i j 0 * wr w j 0 -
        ∫ v in (0 : ℝ)..(k * h), wr w j v * eulerD s₁ b₁ h w a y i j v) =
      s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j) * (wr w j (k * h + (u - k * h)) - wr w j (k * h)) +
        (s₁ (eulerZZ s₁ b₁ h w a y k).2 (i, j) - s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j)) / h *
          ((u - k * h) * wr w j (k * h + (u - k * h)) -
            ∫ v in (k * h : ℝ)..(k * h + (u - k * h)), wr w j v) := by
    intro j
    have hHu : eulerH s₁ b₁ h w a y i j u = s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j) +
        (u - k * h) / h * (s₁ (eulerZZ s₁ b₁ h w a y k).2 (i, j) -
          s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j)) := by
      simp only [eulerH]; rw [pwLin_on_cell hh _ k hu]; rfl
    have hHk : eulerH s₁ b₁ h w a y i j (k * h) = s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j) := by
      simp only [eulerH]; rw [pwLin_grid hh]
    have hD : (∫ v in (0 : ℝ)..u, wr w j v * eulerD s₁ b₁ h w a y i j v) -
        ∫ v in (0 : ℝ)..(k * h), wr w j v * eulerD s₁ b₁ h w a y i j v =
        (s₁ (eulerZZ s₁ b₁ h w a y k).2 (i, j) - s₁ (eulerZZ s₁ b₁ h w a y k).1 (i, j)) / h *
          ∫ v in (k * h : ℝ)..u, wr w j v := by
      simp only [eulerD]
      rw [intervalIntegral.integral_interval_sub_left (hint _ _ _ _) (hint _ _ _ _),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [(Set.countable_singleton u).ae_notMem volume] with v hv hvI
      rw [Set.uIoc_of_le hu.1] at hvI
      rw [pwSlope_eq_on_cell hh _ k ⟨hvI.1.le, lt_of_lt_of_le
        (lt_of_le_of_ne hvI.2 (by simpa using hv)) hu.2⟩, eulerZZ_succ_fst]
      ring
    have e : (k * h : ℝ) + (u - k * h) = u := by ring
    rw [e]
    linear_combination (wr w j u) * hHu - (wr w j (k * h)) * hHk - hD
  have hsum := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hJ j
  rw [Finset.sum_sub_distrib] at hsum
  linear_combination hsum + hB

theorem eulerY_grid (hh : 0 < h) (hw : Continuous w) (a y : SDEState d) (k : ℕ) :
    eulerY s₁ b₁ h w a y (k * h) = (eulerZZ s₁ b₁ h w a y k).2 := by
  induction k with
  | zero =>
    ext i
    simp [eulerY, eulerZZ]
  | succ k ih =>
    have hc := eulerY_sub_cell (s₁ := s₁) (b₁ := b₁) hh hw a y k (u := ((k + 1 : ℕ) : ℝ) * h)
      ⟨by push_cast; nlinarith, by push_cast; rfl⟩
    rw [ih, sub_eq_iff_eq_add] at hc
    rw [hc, add_comm]
    simp only [eulerZZ]
    congr 2
    push_cast; ring

theorem eulerY_cell (hh : 0 < h) (hw : Continuous w) (a y : SDEState d) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (k * h) ((k + 1) * h)) :
    eulerY s₁ b₁ h w a y u = (eulerZZ s₁ b₁ h w a y k).2 +
      cellInc s₁ b₁ h w (eulerZZ s₁ b₁ h w a y k).1 (eulerZZ s₁ b₁ h w a y k).2 k (u - k * h) := by
  have hc := eulerY_sub_cell (s₁ := s₁) (b₁ := b₁) hh hw a y k hu
  rw [eulerY_grid hh hw a y k] at hc
  rw [← hc]
  abel

end M10b2s

section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

theorem wr_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    {r : ℝ} {t : ℝ≥0} (hr : r.toNNReal ≤ t) (j : Fin d) :
    Measurable[G t] fun ω => wr (fun s => W s ω) j r :=
  hG _ _ hr j

theorem intW_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) {p : ℝ} (hp : 0 ≤ p) {t : ℝ≥0}
    (hpt : p.toNNReal ≤ t) (j : Fin d) :
    Measurable[G t] fun ω => ∫ v in (0 : ℝ)..p, wr (fun s => W s ω) j v := by
  let _ : MeasurableSpace Ω := G t
  have := measurable_intervalIntegral_of_continuous (G t) (H := fun s ω => W s ω j) p.toNNReal
    (fun s hs => hG s t (hs.trans hpt) j)
    (fun ω => (EuclideanSpace.proj j).continuous.comp (hWc ω))
  have e : (p.toNNReal).val = p := Real.coe_toNNReal _ hp
  rw [e] at this
  simpa only [wr] using this

theorem cellIntW_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) {t : ℝ≥0}
    (hqt : q.toNNReal ≤ t) (j : Fin d) :
    Measurable[G t] fun ω => ∫ v in p..q, wr (fun s => W s ω) j v := by
  have hi : ∀ ω (a b : ℝ), IntervalIntegrable (wr (fun s => W s ω) j) volume a b :=
    fun ω a b => (wr_continuous (hWc ω) j).intervalIntegrable a b
  have e : (fun ω => ∫ v in p..q, wr (fun s => W s ω) j v) = fun ω =>
      (∫ v in (0 : ℝ)..q, wr (fun s => W s ω) j v) - ∫ v in (0 : ℝ)..p, wr (fun s => W s ω) j v :=
    funext fun ω => (intervalIntegral.integral_interval_sub_left (hi ω 0 q) (hi ω 0 p)).symm
  rw [e]
  exact (intW_meas_G hG hWc (hp.trans hpq) hqt j).sub
    (intW_meas_G hG hWc hp ((Real.toNNReal_le_toNNReal hpq).trans hqt) j)

theorem cellInc_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (hs : Continuous s₁) (hb : Continuous b₁)
    {t : ℝ≥0} {A Z : Ω → SDEState d} (hA : Measurable[G t] A) (hZ : Measurable[G t] Z)
    {k : ℕ} {r : ℝ} (hk0 : 0 ≤ (k : ℝ) * h) (hr : 0 ≤ r) (ht : ((k : ℝ) * h + r).toNNReal ≤ t) :
    Measurable[G t] fun ω => cellInc s₁ b₁ h (fun s => W s ω) (A ω) (Z ω) k r := by
  have hkt : ((k : ℝ) * h).toNNReal ≤ t := (Real.toNNReal_le_toNNReal (by linarith)).trans ht
  have hsc : ∀ i j, Measurable fun z : SDEState d => s₁ z (i, j) := fun i j =>
    ((EuclideanSpace.proj (i, j)).continuous.comp hs).measurable
  have hbc : ∀ i, Measurable fun z : SDEState d => b₁ z i := fun i =>
    ((EuclideanSpace.proj i).continuous.comp hb).measurable
  have hsA : ∀ i j, Measurable[G t] fun ω => s₁ (A ω) (i, j) := fun i j => (hsc i j).comp hA
  have hsZ : ∀ i j, Measurable[G t] fun ω => s₁ (Z ω) (i, j) := fun i j => (hsc i j).comp hZ
  have hbA : ∀ i, Measurable[G t] fun ω => b₁ (A ω) i := fun i => (hbc i).comp hA
  have hbZ : ∀ i, Measurable[G t] fun ω => b₁ (Z ω) i := fun i => (hbc i).comp hZ
  have h1 := fun j => wr_meas_G (W := W) hG ht j
  have h0 := fun j => wr_meas_G (W := W) hG hkt j
  have hI := fun j => cellIntW_meas_G hG hWc hk0 (le_add_of_nonneg_right hr) ht j
  simp only [cellInc]
  let _ : MeasurableSpace Ω := G t
  refine (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp (measurable_pi_lambda _ fun i => ?_)
  refine ((Finset.measurable_sum _ fun j _ => ?_).add ((hbA i).mul_const _)).add
    ((((hbZ i).sub (hbA i)).mul_const _).div_const _)
  exact ((hsA i j).mul ((h1 j).sub (h0 j))).add
    ((((hsZ i j).sub (hsA i j)).div_const _).mul (((h1 j).const_mul _).sub (hI j)))

theorem eulerZZ_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hGm : Monotone G) (hWc : ∀ ω, Continuous fun s => W s ω) (hh : 0 < h)
    (hs : Continuous s₁) (hb : Continuous b₁) (a y : SDEState d) (k : ℕ) :
    Measurable[G ((k : ℝ) * h).toNNReal]
        (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1) ∧
      Measurable[G ((k : ℝ) * h).toNNReal]
        (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2) := by
  induction k with
  | zero => simp only [eulerZZ]; exact ⟨measurable_const, measurable_const⟩
  | succ k ih =>
    have hle : G ((k : ℝ) * h).toNNReal ≤ G (((k + 1 : ℕ) : ℝ) * h).toNNReal :=
      hGm (Real.toNNReal_le_toNNReal (by push_cast; nlinarith))
    refine ⟨ih.2.mono hle le_rfl, ?_⟩
    show Measurable[G (((k + 1 : ℕ) : ℝ) * h).toNNReal] fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 +
      cellInc s₁ b₁ h (fun s => W s ω) (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 k h
    exact (ih.2.mono hle le_rfl).add (cellInc_meas_G hG hWc hs hb (ih.1.mono hle le_rfl)
      (ih.2.mono hle le_rfl) (by positivity) hh.le
      (le_of_eq (by rw [show (((k + 1 : ℕ) : ℝ) * h) = (k : ℝ) * h + h by push_cast; ring])))

theorem floor_cell_mem (hh : 0 < h) (s : ℝ≥0) :
    (s : ℝ) ∈ Set.Icc ((⌊(s : ℝ) / h⌋₊ : ℝ) * h) ((⌊(s : ℝ) / h⌋₊ + 1) * h) := by
  have hk1 : (⌊(s : ℝ) / h⌋₊ : ℝ) ≤ s / h := Nat.floor_le (div_nonneg s.2 hh.le)
  have hk2 : (s : ℝ) / h < ⌊(s : ℝ) / h⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hh] at hk1
  rw [div_lt_iff₀ hh] at hk2
  exact ⟨hk1, hk2.le⟩

theorem pwLin_meas_G (hGm : Monotone G) (hh : 0 < h) {c : ℕ → Ω → ℝ}
    (hc : ∀ k : ℕ, Measurable[G ((k : ℝ) * h).toNNReal] (c k) ∧
      Measurable[G ((k : ℝ) * h).toNNReal] (c (k + 1))) (s : ℝ≥0) :
    Measurable[G s] fun ω => pwLin h (fun k => c k ω) s := by
  have hmem := floor_cell_mem hh s
  set k := ⌊(s : ℝ) / h⌋₊
  have e : (fun ω => pwLin h (fun k => c k ω) s) =
      fun ω => c k ω + ((s : ℝ) - k * h) / h * (c (k + 1) ω - c k ω) :=
    funext fun ω => pwLin_on_cell hh _ k hmem
  have hle : G ((k : ℝ) * h).toNNReal ≤ G s :=
    hGm (by rw [Real.toNNReal_le_iff_le_coe]; exact hmem.1)
  rw [e]
  exact ((hc k).1.mono hle le_rfl).add
    ((((hc k).2.mono hle le_rfl).sub ((hc k).1.mono hle le_rfl)).const_mul _)

theorem eulerH_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hGm : Monotone G) (hWc : ∀ ω, Continuous fun s => W s ω) (hh : 0 < h)
    (hs : Continuous s₁) (hb : Continuous b₁) (a y : SDEState d) (i j : Fin d) (s : ℝ≥0) :
    Measurable[G s] fun ω => eulerH s₁ b₁ h (fun s => W s ω) a y i j s := by
  have hsc : Measurable fun z : SDEState d => s₁ z (i, j) :=
    ((EuclideanSpace.proj (i, j)).continuous.comp hs).measurable
  exact pwLin_meas_G hGm hh (c := fun k ω => s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 (i, j))
    (fun k => ⟨hsc.comp (eulerZZ_meas_G hG hGm hWc hh hs hb a y k).1,
      hsc.comp (eulerZZ_meas_G hG hGm hWc hh hs hb a y k).2⟩) s

theorem eulerB_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hGm : Monotone G) (hWc : ∀ ω, Continuous fun s => W s ω) (hh : 0 < h)
    (hs : Continuous s₁) (hb : Continuous b₁) (a y : SDEState d) (i : Fin d) (s : ℝ≥0) :
    Measurable[G s] fun ω => eulerB s₁ b₁ h (fun s => W s ω) a y i s := by
  have hbc : Measurable fun z : SDEState d => b₁ z i :=
    ((EuclideanSpace.proj i).continuous.comp hb).measurable
  exact pwLin_meas_G hGm hh (c := fun k ω => b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 i)
    (fun k => ⟨hbc.comp (eulerZZ_meas_G hG hGm hWc hh hs hb a y k).1,
      hbc.comp (eulerZZ_meas_G hG hGm hWc hh hs hb a y k).2⟩) s

theorem eulerY_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hGm : Monotone G) (hWc : ∀ ω, Continuous fun s => W s ω) (hh : 0 < h)
    (hs : Continuous s₁) (hb : Continuous b₁) (a y : SDEState d) (s : ℝ≥0) :
    Measurable[G s] fun ω => eulerY s₁ b₁ h (fun s => W s ω) a y s := by
  have hmem := floor_cell_mem hh s
  set k := ⌊(s : ℝ) / h⌋₊
  have e : (fun ω => eulerY s₁ b₁ h (fun s => W s ω) a y s) = fun ω =>
      (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 +
        cellInc s₁ b₁ h (fun s => W s ω) (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1
          (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 k ((s : ℝ) - k * h) :=
    funext fun ω => eulerY_cell hh (hWc ω) a y k hmem
  have hle : G ((k : ℝ) * h).toNNReal ≤ G s :=
    hGm (by rw [Real.toNNReal_le_iff_le_coe]; exact hmem.1)
  have hZ := eulerZZ_meas_G hG hGm hWc hh hs hb a y k
  rw [e]
  exact (hZ.2.mono hle le_rfl).add (cellInc_meas_G hG hWc hs hb (hZ.1.mono hle le_rfl)
    (hZ.2.mono hle le_rfl) (by positivity) (by linarith [hmem.1])
    (le_of_eq (by rw [show (k : ℝ) * h + ((s : ℝ) - k * h) = s by ring]; exact Real.toNNReal_coe)))

theorem eulerY_continuous (hh : 0 < h) {w : ℝ≥0 → SDEState d} (hw : Continuous w)
    (a y : SDEState d) : Continuous (eulerY s₁ b₁ h w a y) := by
  have hint : ∀ (c : ℕ → ℝ) (j : Fin d) (p q : ℝ),
      IntervalIntegrable (fun v => wr w j v * pwSlope h c v) volume p q := fun c j p q =>
    (pwSlope_intervalIntegrable hh c p q).continuousOn_mul (wr_continuous hw j).continuousOn
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine (continuous_const.add (continuous_finsetSum _ fun j _ => ?_)).add
    (intervalIntegral.continuous_primitive
      (fun p q => (pwLin_continuous hh _).intervalIntegrable p q) 0)
  exact (((pwLin_continuous hh _).mul (wr_continuous hw j)).sub continuous_const).sub
    (intervalIntegral.continuous_primitive (hint _ j) 0)

end M10b2w

section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

theorem eulerH_ito {P : Measure Ω} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < h)
    (hs : Continuous s₁) (hb : Continuous b₁) (a y : SDEState d) (i j : Fin d) :
    HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀)) (fun s ω => W s ω j)
      (fun s ω => eulerH s₁ b₁ h (fun s => W s ω) a y i j s)
      (fun t ω => eulerH s₁ b₁ h (fun s => W s ω) a y i j t * W t ω j -
        eulerH s₁ b₁ h (fun s => W s ω) a y i j ((0 : ℝ≥0) : ℝ) * W 0 ω j -
        ∫ u in (0 : ℝ)..t, W u.toNNReal ω j * eulerD s₁ b₁ h (fun s => W s ω) a y i j u) := by
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hGm : Monotone (completedBrownianPast P W (fun _ => x₀)) :=
    fun s t hst => completedBrownianPast_mono P W _ hst
  exact hasBrownianItoIntegral_ibp hW x₀ j
    (H := fun s ω => eulerH s₁ b₁ h (fun s => W s ω) a y i j s)
    (D := fun u ω => eulerD s₁ b₁ h (fun s => W s ω) a y i j u)
    (fun s => eulerH_meas_G hG hGm hW.2.1 hh hs hb a y i j s)
    (fun ω => (pwLin_continuous hh _).comp NNReal.continuous_coe)
    (fun t ω => pwSlope_intervalIntegrable hh _ _ _)
    (fun s ω => by simp [eulerH, eulerD, pwLin])

theorem eulerY_rep (ω : Ω) (a y : SDEState d) (s : ℝ≥0) (i : Fin d) :
    eulerY s₁ b₁ h (fun s => W s ω) a y s i =
      eulerY s₁ b₁ h (fun s => W s ω) a y ((0 : ℝ≥0) : ℝ) i +
      (∑ j, (eulerH s₁ b₁ h (fun s => W s ω) a y i j s * W s ω j -
        eulerH s₁ b₁ h (fun s => W s ω) a y i j ((0 : ℝ≥0) : ℝ) * W 0 ω j -
        ∫ u in (0 : ℝ)..s, W u.toNNReal ω j * eulerD s₁ b₁ h (fun s => W s ω) a y i j u)) +
      ∫ u in (0 : ℝ)..s, eulerB s₁ b₁ h (fun s => W s ω) a y i ((u.toNNReal : ℝ≥0) : ℝ) := by
  have hB : ∫ u in (0 : ℝ)..s, eulerB s₁ b₁ h (fun s => W s ω) a y i ((u.toNNReal : ℝ≥0) : ℝ) =
      ∫ u in (0 : ℝ)..s, eulerB s₁ b₁ h (fun s => W s ω) a y i u :=
    intervalIntegral.integral_congr fun u hu => by
      have hu0 : 0 ≤ u := by
        rcases Set.mem_uIcc.1 hu with h1 | h1
        · exact h1.1
        · exact (NNReal.coe_nonneg s).trans h1.1
      rw [Real.coe_toNNReal _ hu0]
  rw [hB]
  simp [eulerY, wr]

end M10b2i

section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

end M10b4a

section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

end M10b4b

end ItoLib

-- ===== F =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

-- ===== G =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

end M10c4

section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5

section M10c5s
/-! s33 STAB: stability in probability of an SDE solution against Ito processes whose
coefficients are close (in mean integrated square, inside `B̄_{R+3}`) to the SDE coefficients. -/

set_option maxHeartbeats 1000000 in
theorem ito_stability [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {R L S : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hS0 : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (t : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : ℝ≥0 → Ω → SDEState d) (HY JY : ℝ≥0 → Ω → SDEDiffusion d)
      (bY : ℝ≥0 → Ω → SDEState d) (e : ℝ → Ω → ℝ),
      (∀ s, Measurable (Y s)) → (∀ ω, Continuous fun s => Y s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s)) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s)) →
      (∀ ω, Continuous fun s => HY s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s)) →
      (∀ ω, Continuous fun s => bY s ω) →
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j))) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
        ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i) →
      (∀ᵐ ω ∂P, Y 0 ω = x₀) →
      (∀ s ω, ‖HY s ω‖ ≤ S) → (∀ s ω, ‖bY s ω‖ ≤ S) →
      (∀ ω, Continuous fun u => e u ω) → (∀ u ω, 0 ≤ e u ω) →
      (∀ u ω, ‖Y u.toNNReal ω‖ ≤ R + 3 →
        ‖b₀ (Y u.toNNReal ω) - bY u.toNNReal ω‖ ^ 2 +
          ‖σ₀ (Y u.toNNReal ω) - HY u.toNNReal ω‖ ^ 2 ≤ e u ω) →
      Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, e u ω) P →
      ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ δ →
      P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤ ENNReal.ofReal η := by
  exact EthierKurtz.sde_stability_in_probability hW x₀ hσ hb hX hR hL hLip hS0 t hε hη
end M10c5s

section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

theorem cellInc_norm_le {S δ : ℝ} (hh : 0 < h) (hw : Continuous w)
    (hS : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (a z : SDEState d) (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ h) (hδ0 : 0 ≤ δ)
    (hδ : ∀ j v, v ∈ Set.Icc (k * h) (k * h + h) →
      |wr w j v - wr w j (k * h + r)| ≤ δ ∧ |wr w j v - wr w j (k * h)| ≤ δ) :
    ‖cellInc s₁ b₁ h w a z k r‖ ≤ d * (3 * d * S * δ + 2 * S * h) := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS a).1
  refine (euc_norm_le_sum' _).trans ?_
  have hcomp : ∀ i, |cellInc s₁ b₁ h w a z k r i| ≤ 3 * d * S * δ + 2 * S * h := by
    intro i
    have e : cellInc s₁ b₁ h w a z k r i = (∑ j, (s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h)) +
        (s₁ z (i, j) - s₁ a (i, j)) / h *
          (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v))) +
        b₁ a i * r + (b₁ z i - b₁ a i) * r ^ 2 / (2 * h) := rfl
    rw [e]
    have hj : ∀ j, |s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h)) +
        (s₁ z (i, j) - s₁ a (i, j)) / h *
          (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v)| ≤ 3 * S * δ := by
      intro j
      have h1 : |s₁ a (i, j)| ≤ S := by
        have := PiLp.norm_apply_le (s₁ a) (i, j)
        rw [Real.norm_eq_abs] at this
        exact this.trans (hS a).1
      have h2 : |s₁ z (i, j) - s₁ a (i, j)| ≤ 2 * S := by
        have := PiLp.norm_apply_le (s₁ z) (i, j)
        have := PiLp.norm_apply_le (s₁ a) (i, j)
        rw [Real.norm_eq_abs] at *
        have := abs_sub (s₁ z (i, j)) (s₁ a (i, j))
        linarith [(hS z).1, (hS a).1]
      have h3 : |wr w j (k * h + r) - wr w j (k * h)| ≤ δ :=
        (hδ j (k * h + r) ⟨by linarith, by linarith⟩).2
      have hc := wr_continuous hw j
      have h4 : |r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v| ≤ δ * r := by
        have e2 : r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v =
            ∫ v in (k * h : ℝ)..(k * h + r), (wr w j (k * h + r) - wr w j v) := by
          rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
            intervalIntegral.integral_const, smul_eq_mul]
          ring
        have hpt : ∀ v ∈ Set.uIoc (k * h : ℝ) (k * h + r), ‖wr w j (k * h + r) - wr w j v‖ ≤ δ :=
          fun v hv => by
            rw [Set.uIoc_of_le (by linarith)] at hv
            rw [Real.norm_eq_abs, abs_sub_comm]
            exact (hδ j v ⟨hv.1.le, by linarith [hv.2]⟩).1
        have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
        rw [e2, ← Real.norm_eq_abs]
        calc _ ≤ δ * |k * h + r - k * h| := this
          _ = δ * r := by rw [show (k * h + r - k * h : ℝ) = r by ring, abs_of_nonneg hr0]
      have hA : |s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h))| ≤ S * δ := by
        rw [abs_mul]; exact mul_le_mul h1 h3 (abs_nonneg _) hS0
      have hB : |(s₁ z (i, j) - s₁ a (i, j)) / h *
          (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v)| ≤ 2 * S * δ := by
        rw [abs_mul, abs_div, abs_of_pos hh]
        have hq : |s₁ z (i, j) - s₁ a (i, j)| / h ≤ 2 * S / h :=
          (div_le_div_iff_of_pos_right hh).2 h2
        calc _ ≤ 2 * S / h * (δ * r) :=
              mul_le_mul hq h4 (abs_nonneg _) (div_nonneg (by linarith) hh.le)
          _ = 2 * S * δ * (r / h) := by field_simp
          _ ≤ 2 * S * δ * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [div_le_one hh]; exact hrh
          _ = 2 * S * δ := by ring
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ S * δ + 2 * S * δ := add_le_add hA hB
        _ = 3 * S * δ := by ring
    have hb1 : |b₁ a i| ≤ S := by
      have := PiLp.norm_apply_le (b₁ a) i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hS a).2
    have hb2 : |b₁ z i - b₁ a i| ≤ 2 * S := by
      have := PiLp.norm_apply_le (b₁ z) i
      have := PiLp.norm_apply_le (b₁ a) i
      rw [Real.norm_eq_abs] at *
      have := abs_sub (b₁ z i) (b₁ a i)
      linarith [(hS z).2, (hS a).2]
    have hD1 : |b₁ a i * r| ≤ S * h := by
      rw [abs_mul, abs_of_nonneg hr0]; exact mul_le_mul hb1 hrh hr0 hS0
    have hr2 : r ^ 2 / (2 * h) ≤ h / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hD2 : |(b₁ z i - b₁ a i) * r ^ 2 / (2 * h)| ≤ S * h := by
      rw [mul_div_assoc, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2 / (2 * h))]
      calc _ ≤ 2 * S * (h / 2) := mul_le_mul hb2 hr2 (by positivity) (by linarith)
        _ = S * h := by ring
    have hsum : |∑ j, (s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h)) +
        (s₁ z (i, j) - s₁ a (i, j)) / h *
          (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v))| ≤
        d * (3 * S * δ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _j : Fin d, 3 * S * δ := Finset.sum_le_sum fun j _ => hj j
        _ = d * (3 * S * δ) := by simp
    calc _ ≤ |(∑ j, (s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h)) +
          (s₁ z (i, j) - s₁ a (i, j)) / h *
            (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v))) +
          b₁ a i * r| + |(b₁ z i - b₁ a i) * r ^ 2 / (2 * h)| := abs_add_le _ _
      _ ≤ (d * (3 * S * δ) + S * h) + S * h :=
          add_le_add ((abs_add_le _ _).trans (add_le_add hsum hD1)) hD2
      _ = 3 * d * S * δ + 2 * S * h := by ring
  calc _ ≤ ∑ _i : Fin d, (3 * d * S * δ + 2 * S * h) := Finset.sum_le_sum fun i _ => hcomp i
    _ = d * (3 * d * S * δ + 2 * S * h) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem wr_unif (hw : Continuous w) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ h0 > 0, ∀ j v v', v ∈ Set.Icc (0 : ℝ) T → v' ∈ Set.Icc (0 : ℝ) T → |v - v'| ≤ h0 →
      |wr w j v - wr w j v'| ≤ δ := by
  have hc : Continuous fun v : ℝ => w v.toNNReal := hw.comp continuous_real_toNNReal
  obtain ⟨h0, h0pos, H⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn) δ hδ
  refine ⟨h0 / 2, half_pos h0pos, fun j v v' hv hv' hvv => ?_⟩
  have := H v hv v' hv' (by rw [Real.dist_eq]; linarith)
  rw [dist_eq_norm] at this
  calc |wr w j v - wr w j v'| = ‖(w v.toNNReal - w v'.toNNReal) j‖ := by
        simp [wr, Real.norm_eq_abs]
    _ ≤ ‖w v.toNNReal - w v'.toNNReal‖ := PiLp.norm_apply_le _ j
    _ ≤ δ := this.le

end M10c6

end ItoLib

-- ===== H =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

variable (s₁ b₁ h w) in
/-- The diffusion integrand of the scheme as a matrix. -/
noncomputable def eulerHM (a y : SDEState d) (u : ℝ) : SDEDiffusion d :=
  WithLp.toLp 2 fun p : Fin d × Fin d => eulerH s₁ b₁ h w a y p.1 p.2 u

variable (s₁ b₁ h w) in
/-- The drift of the scheme as a vector. -/
noncomputable def eulerBV (a y : SDEState d) (u : ℝ) : SDEState d :=
  WithLp.toLp 2 fun i => eulerB s₁ b₁ h w a y i u

theorem floor_mem_cell (hh : 0 < h) {u : ℝ} (hu : 0 ≤ u) :
    u ∈ Set.Icc ((⌊u / h⌋₊ : ℝ) * h) ((⌊u / h⌋₊ + 1) * h) := by
  have h1 := Nat.floor_le (div_nonneg hu hh.le)
  have h2 := Nat.lt_floor_add_one (u / h)
  exact ⟨(le_div_iff₀ hh).1 h1, ((div_lt_iff₀ hh).1 h2).le⟩

theorem eulerHM_cell (hh : 0 < h) (a y : SDEState d) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (k * h) ((k + 1) * h)) :
    eulerHM s₁ b₁ h w a y u = s₁ (eulerZZ s₁ b₁ h w a y k).1 +
      ((u - k * h) / h) • (s₁ (eulerZZ s₁ b₁ h w a y k).2 - s₁ (eulerZZ s₁ b₁ h w a y k).1) := by
  ext p
  simp only [eulerHM, eulerH, pwLin_on_cell hh _ k hu]
  rfl

theorem eulerBV_cell (hh : 0 < h) (a y : SDEState d) (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (k * h) ((k + 1) * h)) :
    eulerBV s₁ b₁ h w a y u = b₁ (eulerZZ s₁ b₁ h w a y k).1 +
      ((u - k * h) / h) • (b₁ (eulerZZ s₁ b₁ h w a y k).2 - b₁ (eulerZZ s₁ b₁ h w a y k).1) := by
  ext i
  simp only [eulerBV, eulerB, pwLin_on_cell hh _ k hu]
  rfl

theorem interp_err_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SDEState d → E) {L K : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖)
    (Y Z₁ Z₂ : SDEState d) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (h1 : ‖Y - Z₂‖ ≤ K) (h2 : ‖Z₂ - Z₁‖ ≤ K) :
    ‖f Y - (f Z₁ + θ • (f Z₂ - f Z₁))‖ ≤ 2 * L * K := by
  have e : f Y - (f Z₁ + θ • (f Z₂ - f Z₁)) = (f Y - f Z₂) + (1 - θ) • (f Z₂ - f Z₁) := by
    rw [sub_smul, one_smul]; abel
  rw [e]
  have hθ1 : ‖(1 - θ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hθ.2])]; linarith [hθ.1]
  calc _ ≤ ‖f Y - f Z₂‖ + ‖(1 - θ) • (f Z₂ - f Z₁)‖ := norm_add_le _ _
    _ ≤ L * K + 1 * (L * K) := by
        refine add_le_add ((hL _ _).trans (mul_le_mul_of_nonneg_left h1 hL0)) ?_
        rw [norm_smul]
        exact mul_le_mul hθ1 ((hL _ _).trans (mul_le_mul_of_nonneg_left h2 hL0))
          (norm_nonneg _) zero_le_one
    _ = 2 * L * K := by ring

/-- Pathwise error of the scheme started with lag `a = y`. -/
theorem euler_err_le {L S δ T : ℝ} (hh : 0 < h) (hw : Continuous w)
    (hS : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖) (hδ0 : 0 ≤ δ)
    (hδ : ∀ j v v', v ∈ Set.Icc (0 : ℝ) T → v' ∈ Set.Icc (0 : ℝ) T → |v - v'| ≤ h →
      |wr w j v - wr w j v'| ≤ δ)
    (a : SDEState d) {u : ℝ} (hu0 : 0 ≤ u) (huT : u + h ≤ T) :
    ‖s₁ (eulerY s₁ b₁ h w a a u) - eulerHM s₁ b₁ h w a a u‖ ≤
        2 * L * (d * (3 * d * S * δ + 2 * S * h)) ∧
      ‖b₁ (eulerY s₁ b₁ h w a a u) - eulerBV s₁ b₁ h w a a u‖ ≤
        2 * L * (d * (3 * d * S * δ + 2 * S * h)) := by
  set k := ⌊u / h⌋₊ with hk
  have hu := floor_mem_cell hh hu0
  rw [← hk] at hu
  have hkh : (k : ℝ) * h + h ≤ T := by nlinarith [hu.1]
  -- the cell oscillation hypothesis of `cellInc_norm_le` on a cell `m` with `m h + h ≤ T`
  have hcell : ∀ m : ℕ, (m : ℝ) * h + h ≤ T → ∀ r, 0 ≤ r → r ≤ h → ∀ j v,
      v ∈ Set.Icc ((m : ℝ) * h) (m * h + h) →
        |wr w j v - wr w j (m * h + r)| ≤ δ ∧ |wr w j v - wr w j (m * h)| ≤ δ := by
    intro m hm r hr0 hrh j v hv
    have hm0 : (0 : ℝ) ≤ m * h := mul_nonneg m.cast_nonneg hh.le
    constructor
    · exact hδ j v _ ⟨by linarith [hv.1], by linarith [hv.2]⟩ ⟨by linarith, by linarith⟩
        (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2])
    · exact hδ j v _ ⟨by linarith [hv.1], by linarith [hv.2]⟩ ⟨by linarith, by linarith⟩
        (by rw [abs_le]; constructor <;> linarith [hv.1, hv.2])
  set K := (d : ℝ) * (3 * d * S * δ + 2 * S * h) with hK
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS a).1
  have hK0 : 0 ≤ K := by positivity
  set Z := eulerZZ s₁ b₁ h w a a k with hZ
  have h1 : ‖eulerY s₁ b₁ h w a a u - Z.2‖ ≤ K := by
    rw [eulerY_cell hh hw a a k hu, add_sub_cancel_left]
    exact cellInc_norm_le hh hw hS _ _ k (by linarith [hu.1]) (by linarith [hu.2]) hδ0
      (hcell k hkh _ (by linarith [hu.1]) (by linarith [hu.2]))
  have h2 : ‖Z.2 - Z.1‖ ≤ K := by
    rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
    · rw [hZ, h0]; simp [eulerZZ, hK0]
    · rw [hZ, hs]
      show ‖(eulerZZ s₁ b₁ h w a a k.pred).2 + cellInc s₁ b₁ h w (eulerZZ s₁ b₁ h w a a k.pred).1
        (eulerZZ s₁ b₁ h w a a k.pred).2 k.pred h - (eulerZZ s₁ b₁ h w a a k.pred).2‖ ≤ K
      rw [add_sub_cancel_left]
      have hp : ((k.pred : ℕ) : ℝ) * h + h ≤ T := by
        have : ((k.pred : ℕ) : ℝ) + 1 = k := by exact_mod_cast hs.symm
        nlinarith [hu.1]
      exact cellInc_norm_le hh hw hS _ _ k.pred hh.le le_rfl hδ0 (hcell _ hp h hh.le le_rfl)
  have hθ : (u - k * h) / h ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hu.1]) hh.le, (div_le_one hh).2 (by linarith [hu.2])⟩
  constructor
  · rw [eulerHM_cell hh a a k hu]
    exact interp_err_le s₁ hL0 (fun x y => (hL x y).1) _ _ _ hθ h1 h2
  · rw [eulerBV_cell hh a a k hu]
    exact interp_err_le b₁ hL0 (fun x y => (hL x y).2) _ _ _ hθ h1 h2

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

theorem interp_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E} {S θ : ℝ}
    (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : ‖A + θ • (B - A)‖ ≤ S := by
  have e : A + θ • (B - A) = (1 - θ) • A + θ • B := by rw [smul_sub, sub_smul, one_smul]; abel
  rw [e]
  calc _ ≤ ‖(1 - θ) • A‖ + ‖θ • B‖ := norm_add_le _ _
    _ = (1 - θ) * ‖A‖ + θ * ‖B‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hθ.2]), abs_of_nonneg hθ.1]
    _ ≤ (1 - θ) * S + θ * S := add_le_add (mul_le_mul_of_nonneg_left hA (by linarith [hθ.2]))
        (mul_le_mul_of_nonneg_left hB hθ.1)
    _ = S := by ring

theorem eulerHM_norm_le {w : ℝ≥0 → SDEState d} {S : ℝ} (hh : 0 < h)
    (hS : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (a y : SDEState d) {u : ℝ} (hu : 0 ≤ u) :
    ‖eulerHM s₁ b₁ h w a y u‖ ≤ S ∧ ‖eulerBV s₁ b₁ h w a y u‖ ≤ S := by
  have hc := floor_mem_cell hh hu
  have hθ : (u - ⌊u / h⌋₊ * h) / h ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hc.1]) hh.le, (div_le_one hh).2 (by linarith [hc.2])⟩
  rw [eulerHM_cell hh a y _ hc, eulerBV_cell hh a y _ hc]
  exact ⟨interp_norm_le (hS _).1 (hS _).1 hθ, interp_norm_le (hS _).2 (hS _).2 hθ⟩

theorem eulerHM_continuous {w : ℝ≥0 → SDEState d} (hh : 0 < h) (a y : SDEState d) :
    Continuous (eulerHM s₁ b₁ h w a y) ∧ Continuous (eulerBV s₁ b₁ h w a y) :=
  ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => pwLin_continuous hh _),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => pwLin_continuous hh _)⟩

/-- Coefficient-error integrand of the scheme. -/
noncomputable def eulerErr (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
    (h C : ℝ) (W : ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d) (s : ℝ≥0) (ω : Ω) : ℝ :=
  C * (‖b₁ (eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ s) - eulerBV s₁ b₁ h (fun s => W s ω) x₀ x₀ s‖ ^ 2 +
    ‖s₁ (eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ s) - eulerHM s₁ b₁ h (fun s => W s ω) x₀ x₀ s‖ ^ 2)

set_option maxHeartbeats 1000000 in
theorem euler_stab_apply [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    {X : ℝ≥0 → Ω → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) (hh : 0 < h) {R S : ℝ}
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    (t : ℝ≥0) {δ ε η : ℝ}
    (hST : ∀ (Y : ℝ≥0 → Ω → SDEState d) (HY JY : ℝ≥0 → Ω → SDEDiffusion d)
      (bY : ℝ≥0 → Ω → SDEState d) (e : ℝ → Ω → ℝ),
      (∀ s, Measurable (Y s)) → (∀ ω, Continuous fun s => Y s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s)) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s)) →
      (∀ ω, Continuous fun s => HY s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s)) →
      (∀ ω, Continuous fun s => bY s ω) →
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j))) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
        ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i) →
      (∀ᵐ ω ∂P, Y 0 ω = x₀) →
      (∀ s ω, ‖HY s ω‖ ≤ S) → (∀ s ω, ‖bY s ω‖ ≤ S) →
      (∀ ω, Continuous fun u => e u ω) → (∀ u ω, 0 ≤ e u ω) →
      (∀ u ω, ‖Y u.toNNReal ω‖ ≤ R + 3 →
        ‖b₀ (Y u.toNNReal ω) - bY u.toNNReal ω‖ ^ 2 +
          ‖σ₀ (Y u.toNNReal ω) - HY u.toNNReal ω‖ ^ 2 ≤ e u ω) →
      Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, e u ω) P →
      ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ δ →
      P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤ ENNReal.ofReal η)
    (hE : ∫ ω, (∫ u in (0 : ℝ)..t.val, eulerErr s₁ b₁ h 1 W x₀ u.toNNReal ω) ∂P ≤ δ) :
    P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧
      ε < ‖X t ω - eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ t‖ ^ 2} ≤ ENNReal.ofReal η := by
  set Y : ℝ≥0 → Ω → SDEState d := fun s ω => eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ s with hYdef
  set HY : ℝ≥0 → Ω → SDEDiffusion d := fun s ω => eulerHM s₁ b₁ h (fun s => W s ω) x₀ x₀ s
  set bY : ℝ≥0 → Ω → SDEState d := fun s ω => eulerBV s₁ b₁ h (fun s => W s ω) x₀ x₀ s
  set JY : ℝ≥0 → Ω → SDEDiffusion d := fun t ω => WithLp.toLp 2 fun p : Fin d × Fin d =>
    eulerH s₁ b₁ h (fun s => W s ω) x₀ x₀ p.1 p.2 t * W t ω p.2 -
      eulerH s₁ b₁ h (fun s => W s ω) x₀ x₀ p.1 p.2 ((0 : ℝ≥0) : ℝ) * W 0 ω p.2 -
      ∫ u in (0 : ℝ)..t, W u.toNNReal ω p.2 * eulerD s₁ b₁ h (fun s => W s ω) x₀ x₀ p.1 p.2 u
  have hS : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  -- filtrations: the completed past and the ambient σ-algebra
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hGm : Monotone (completedBrownianPast P W (fun _ => x₀)) :=
    fun s t hst => completedBrownianPast_mono P W _ hst
  have hG' : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[(fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) t]
      fun ω => W r ω j :=
    fun r _ _ j => (EuclideanSpace.proj j).continuous.measurable.comp (hW.1 r)
  have hGm' : Monotone (fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) := monotone_const
  have hYm : ∀ s, Measurable (Y s) := fun s => eulerY_meas_G hG' hGm' hW.2.1 hh hs₁ hb₁ x₀ x₀ s
  have hYc : ∀ ω, Continuous fun s => Y s ω := fun ω =>
    (eulerY_continuous hh (hW.2.1 ω) x₀ x₀).comp NNReal.continuous_coe
  have hYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s) :=
    fun s => eulerY_meas_G hG hGm hW.2.1 hh hs₁ hb₁ x₀ x₀ s
  have hHYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s) := fun s => by
    have hp := fun p : Fin d × Fin d => eulerH_meas_G hG hGm hW.2.1 hh hs₁ hb₁ x₀ x₀ p.1 p.2 s
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
    exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ hp)
  have hbYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s) := fun s => by
    have hp := fun i : Fin d => eulerB_meas_G hG hGm hW.2.1 hh hs₁ hb₁ x₀ x₀ i s
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
    exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ hp)
  have hHYm : ∀ s, Measurable (HY s) := fun s =>
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun p => eulerH_meas_G hG' hGm' hW.2.1 hh hs₁ hb₁ x₀ x₀ p.1 p.2 s)
  have hbYm : ∀ s, Measurable (bY s) := fun s =>
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => eulerB_meas_G hG' hGm' hW.2.1 hh hs₁ hb₁ x₀ x₀ i s)
  have hHYc : ∀ ω, Continuous fun s => HY s ω := fun ω =>
    (eulerHM_continuous hh x₀ x₀).1.comp NNReal.continuous_coe
  have hbYc : ∀ ω, Continuous fun s => bY s ω := fun ω =>
    (eulerHM_continuous hh x₀ x₀).2.comp NNReal.continuous_coe
  have hJY : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j)) :=
    fun i j => eulerH_ito hW x₀ hh hs₁ hb₁ x₀ x₀ i j
  have hYeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
      ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i :=
    ae_of_all _ fun ω s i => eulerY_rep ω x₀ x₀ s i
  have hY0 : ∀ᵐ ω ∂P, Y 0 ω = x₀ := ae_of_all _ fun ω => by
    ext i; simp [hYdef, eulerY]
  have hHY : ∀ s ω, ‖HY s ω‖ ≤ S := fun s ω => (eulerHM_norm_le hh hSg x₀ x₀ s.2).1
  have hbY : ∀ s ω, ‖bY s ω‖ ≤ S := fun s ω => (eulerHM_norm_le hh hSg x₀ x₀ s.2).2
  -- the error integrand
  have hEc : ∀ ω, Continuous fun s => eulerErr s₁ b₁ h 1 W x₀ s ω := fun ω =>
    continuous_const.mul ((((hb₁.comp (hYc ω)).sub (hbYc ω)).norm.pow 2).add
      (((hs₁.comp (hYc ω)).sub (hHYc ω)).norm.pow 2))
  have hEm : ∀ s, Measurable fun ω => eulerErr s₁ b₁ h 1 W x₀ s ω := fun s =>
    measurable_const.mul ((((hb₁.measurable.comp (hYm s)).sub (hbYm s)).norm.pow_const 2).add
      (((hs₁.measurable.comp (hYm s)).sub (hHYm s)).norm.pow_const 2))
  have hE0 : ∀ s ω, 0 ≤ eulerErr s₁ b₁ h 1 W x₀ s ω := fun s ω => by
    unfold eulerErr; positivity
  have hEb : ∀ s ω, eulerErr s₁ b₁ h 1 W x₀ s ω ≤ 1 * ((2 * S) ^ 2 + (2 * S) ^ 2) := fun s ω => by
    unfold eulerErr
    have h1 : ‖b₁ (Y s ω) - bY s ω‖ ≤ 2 * S :=
      (norm_sub_le _ _).trans (by linarith [(hSg (Y s ω)).2, hbY s ω])
    have h2 : ‖s₁ (Y s ω) - HY s ω‖ ≤ 2 * S :=
      (norm_sub_le _ _).trans (by linarith [(hSg (Y s ω)).1, hHY s ω])
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) zero_le_one
    · exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hEi : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, eulerErr s₁ b₁ h 1 W x₀ u.toNNReal ω) P := by
    refine (integrable_const (1 * ((2 * S) ^ 2 + (2 * S) ^ 2) * t.val)).mono'
      (measurable_intervalIntegral_of_continuous _ t (fun s _ => hEm s) hEc).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t.val)
      (f := fun u => eulerErr s₁ b₁ h 1 W x₀ u.toNNReal ω)
      (C := 1 * ((2 * S) ^ 2 + (2 * S) ^ 2)) (fun u _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hE0 _ _)]; exact hEb _ _)
    rwa [sub_zero, abs_of_nonneg t.2] at this
  refine hST Y HY JY bY (fun u ω => eulerErr s₁ b₁ h 1 W x₀ u.toNNReal ω) hYm hYc hYa hHYa hHYc
    hbYa hbYc hJY hYeq hY0 hHY hbY (fun ω => (hEc ω).comp continuous_real_toNNReal)
    (fun u ω => hE0 _ _) (fun u ω hY => ?_) hEi hE
  rw [← (hag _ hY).1, ← (hag _ hY).2]
  exact (one_mul _).symm.le

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem eulerErr_props [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    (hWm : ∀ t, Measurable (W t)) (hWc : ∀ ω, Continuous fun s => W s ω)
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {h C S : ℝ} (hh : 0 < h)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (hC : 0 ≤ C) (x₀ : SDEState d) :
    (∀ ω, Continuous fun s => eulerErr s₁ b₁ h C W x₀ s ω) ∧
      (∀ s, Measurable fun ω => eulerErr s₁ b₁ h C W x₀ s ω) ∧
      (∀ s ω, 0 ≤ eulerErr s₁ b₁ h C W x₀ s ω) ∧
      (∀ s ω, eulerErr s₁ b₁ h C W x₀ s ω ≤ C * ((2 * S) ^ 2 + (2 * S) ^ 2)) := by
  set Y : ℝ≥0 → Ω → SDEState d := fun s ω => eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ s
  set HY : ℝ≥0 → Ω → SDEDiffusion d := fun s ω => eulerHM s₁ b₁ h (fun s => W s ω) x₀ x₀ s
  set bY : ℝ≥0 → Ω → SDEState d := fun s ω => eulerBV s₁ b₁ h (fun s => W s ω) x₀ x₀ s
  have hG' : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[(fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) t]
      fun ω => W r ω j :=
    fun r _ _ j => (EuclideanSpace.proj j).continuous.measurable.comp (hWm r)
  have hGm' : Monotone (fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) := monotone_const
  have hYm : ∀ s, Measurable (Y s) := fun s => eulerY_meas_G hG' hGm' hWc hh hs₁ hb₁ x₀ x₀ s
  have hYc : ∀ ω, Continuous fun s => Y s ω := fun ω =>
    (eulerY_continuous hh (hWc ω) x₀ x₀).comp NNReal.continuous_coe
  have hHYm : ∀ s, Measurable (HY s) := fun s =>
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun p => eulerH_meas_G hG' hGm' hWc hh hs₁ hb₁ x₀ x₀ p.1 p.2 s)
  have hbYm : ∀ s, Measurable (bY s) := fun s =>
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => eulerB_meas_G hG' hGm' hWc hh hs₁ hb₁ x₀ x₀ i s)
  have hHYc : ∀ ω, Continuous fun s => HY s ω := fun ω =>
    (eulerHM_continuous hh x₀ x₀).1.comp NNReal.continuous_coe
  have hbYc : ∀ ω, Continuous fun s => bY s ω := fun ω =>
    (eulerHM_continuous hh x₀ x₀).2.comp NNReal.continuous_coe
  have hHY : ∀ s ω, ‖HY s ω‖ ≤ S := fun s ω => (eulerHM_norm_le hh hSg x₀ x₀ s.2).1
  have hbY : ∀ s ω, ‖bY s ω‖ ≤ S := fun s ω => (eulerHM_norm_le hh hSg x₀ x₀ s.2).2
  refine ⟨fun ω => continuous_const.mul ((((hb₁.comp (hYc ω)).sub (hbYc ω)).norm.pow 2).add
      (((hs₁.comp (hYc ω)).sub (hHYc ω)).norm.pow 2)),
    fun s => measurable_const.mul ((((hb₁.measurable.comp (hYm s)).sub (hbYm s)).norm.pow_const 2).add
      (((hs₁.measurable.comp (hYm s)).sub (hHYm s)).norm.pow_const 2)),
    fun s ω => by unfold eulerErr; positivity, fun s ω => ?_⟩
  unfold eulerErr
  have h1 : ‖b₁ (Y s ω) - bY s ω‖ ≤ 2 * S :=
    (norm_sub_le _ _).trans (by linarith [(hSg (Y s ω)).2, hbY s ω])
  have h2 : ‖s₁ (Y s ω) - HY s ω‖ ≤ 2 * S :=
    (norm_sub_le _ _).trans (by linarith [(hSg (Y s ω)).1, hHY s ω])
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC
  · exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- Pathwise: `∫₀ᵗ eulerErr_{hₙ} → 0` for every continuous driving path. -/
theorem eulerErr_integral_tendsto_path {W : ℝ≥0 → Ω → SDEState d} (ω : Ω)
    (hWc : Continuous fun s => W s ω) {C S L : ℝ} (hC : 0 ≤ C) (hL0 : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0)) (x₀ : SDEState d)
    (t : ℝ≥0) :
    Tendsto (fun n => ∫ u in (0 : ℝ)..t.val, eulerErr s₁ b₁ (hn n) C W x₀ u.toNNReal ω)
      atTop (𝓝 0) := by
  have hS : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  set g : ℝ → ℝ := fun ρ => t.val * (C * ((2 * L * (d * (3 * d * S * ρ + 2 * S * ρ))) ^ 2 +
    (2 * L * (d * (3 * d * S * ρ + 2 * S * ρ))) ^ 2)) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hg0 : g 0 = 0 := by simp [hg]
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨ρ', hρ'0, hρ'⟩ := Metric.continuous_iff.1 hgc 0 η hη
  set ρ := ρ' / 2 with hρ
  have hρ0 : 0 < ρ := half_pos hρ'0
  have hgρ : g ρ < η := by
    have := hρ' ρ (by rw [Real.dist_eq, sub_zero, abs_of_pos hρ0]; linarith)
    rw [hg0, Real.dist_eq, sub_zero, abs_lt] at this
    exact this.2
  obtain ⟨h0, h0pos, hU⟩ := wr_unif (w := fun s => W s ω) hWc (t.val + 1) ρ hρ0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (min h0 (min ρ 1)) (by positivity)
  refine ⟨N, fun n hn' => ?_⟩
  have hnN := hN n hn'
  rw [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] at hnN
  have hnh0 : hn n ≤ h0 := hnN.le.trans (min_le_left _ _)
  have hnρ : hn n ≤ ρ := hnN.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hn1 : hn n ≤ 1 := hnN.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  set K := (d : ℝ) * (3 * d * S * ρ + 2 * S * hn n) with hK
  have hK0 : 0 ≤ K := by have := hpos n; positivity
  have hKρ : 2 * L * K ≤ 2 * L * (d * (3 * d * S * ρ + 2 * S * ρ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
  have hpt : ∀ u ∈ Set.uIoc (0 : ℝ) t.val, ‖eulerErr s₁ b₁ (hn n) C W x₀ u.toNNReal ω‖ ≤
      C * ((2 * L * (d * (3 * d * S * ρ + 2 * S * ρ))) ^ 2 +
        (2 * L * (d * (3 * d * S * ρ + 2 * S * ρ))) ^ 2) := by
    intro u hu
    rw [Set.uIoc_of_le t.2] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have he := euler_err_le (s₁ := s₁) (b₁ := b₁) (w := fun s => W s ω) (T := t.val + 1)
      (hpos n) hWc hSg hL0 hLg hρ0.le
      (fun j v v' hv hv' hvv => hU j v v' hv hv' (hvv.trans hnh0)) x₀ hu0 (by linarith [hu.2])
    unfold eulerErr
    rw [Real.coe_toNNReal _ hu0, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC
    · exact pow_le_pow_left₀ (norm_nonneg _) (he.2.trans hKρ) 2
    · exact pow_le_pow_left₀ (norm_nonneg _) (he.1.trans hKρ) 2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [sub_zero, abs_of_nonneg t.2] at this
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  calc _ ≤ _ := this
    _ = g ρ := by rw [hg]; ring
    _ < η := hgρ

/-- `E ∫₀ᵗ eulerErr_{hₙ} → 0` (dominated convergence). -/
theorem eulerErr_expect_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ ω, Continuous fun s => W s ω) (hs₁ : Continuous s₁) (hb₁ : Continuous b₁)
    {C S L : ℝ} (hC : 0 ≤ C) (hL0 : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0)) (x₀ : SDEState d)
    (t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (∫ u in (0 : ℝ)..t.val, eulerErr s₁ b₁ (hn n) C W x₀ u.toNNReal ω) ∂P)
      atTop (𝓝 0) := by
  have key : Tendsto (fun n => ∫ ω, (∫ u in (0 : ℝ)..t.val,
      eulerErr s₁ b₁ (hn n) C W x₀ u.toNNReal ω) ∂P) atTop (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C * ((2 * S) ^ 2 + (2 * S) ^ 2) * t.val)
      (fun n => ?_) (integrable_const _) (fun n => ae_of_all _ fun ω => ?_)
      (ae_of_all _ fun ω => eulerErr_integral_tendsto_path ω (hWc ω) hC hL0 hSg hLg hpos hlim x₀ t)
    · obtain ⟨hc, hm, -, -⟩ := eulerErr_props hWm hWc hs₁ hb₁ (hpos n) hSg hC x₀
      exact (measurable_intervalIntegral_of_continuous _ t (fun s _ => hm s) hc).aestronglyMeasurable
    · obtain ⟨-, -, h0, hb⟩ := eulerErr_props hWm hWc hs₁ hb₁ (hpos n) hSg hC x₀
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t.val)
        (f := fun u => eulerErr s₁ b₁ (hn n) C W x₀ u.toNNReal ω)
        (C := C * ((2 * S) ^ 2 + (2 * S) ^ 2)) (fun u _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h0 _ _)]; exact hb _ _)
      rwa [sub_zero, abs_of_nonneg t.2] at this
  rwa [integral_zero] at key

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem euler_close_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ≥0) :
    Tendsto (fun n => P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧
      ε < ‖X t ω - eulerY s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ t‖ ^ 2}) atTop (𝓝 0) := by
  have hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖ := fun x y hx hy => by
    rw [← (hag x hx).1, ← (hag x hx).2, ← (hag y hy).1, ← (hag y hy).2]
    exact ⟨(hLg x y).2, (hLg x y).1⟩
  have hS0 : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S := fun x hx => by
    rw [← (hag x hx).1, ← (hag x hx).2]; exact hSg x
  have hE := eulerErr_expect_tendsto (P := P) hW.1 hW.2.1 hs₁ hb₁ zero_le_one hL hSg hLg hpos hlim
    x₀ t
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨η', hη'0, hη'⟩ : ∃ η' : ℝ, 0 < η' ∧ ENNReal.ofReal η' ≤ η := by
    rcases eq_or_ne η ⊤ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  obtain ⟨δ, hδ, hST⟩ := ito_stability hW x₀ hσ hb hX hR hL hLip hS0 t hε hη'0
  filter_upwards [hE.eventually (Iic_mem_nhds hδ)] with n hn
  exact (euler_stab_apply hW x₀ hs₁ hb₁ (hpos n) hSg hag t hST hn).trans hη'

end M10c10

end ItoLib

-- ===== I =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

end M10d2

end ItoLib

-- ===== J =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10d3

end ItoLib

-- ===== K =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

-- ===== L =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

-- ===== M =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

-- ===== N =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

theorem cell_small (hw : Continuous w) {S : ℝ} (hS : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ h : ℝ, 0 < h → h ≤ η → ∀ (a z : SDEState d) (k : ℕ) (r : ℝ), 0 ≤ r → r ≤ h →
      (k : ℝ) * h + h ≤ T → ‖cellInc s₁ b₁ h w a z k r‖ ≤ ε := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0).1
  have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set δ : ℝ := ε / (6 * d ^ 2 * S + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨h0, h0pos, H⟩ := wr_unif hw T δ hδ0
  set η : ℝ := min h0 (ε / (4 * d * S + 1)) with hη
  have hη0 : 0 < η := lt_min h0pos (div_pos hε (by positivity))
  refine ⟨η, hη0, fun h hh hhη a z k r hr0 hrh hT => ?_⟩
  have hkh : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh.le
  have hb := cellInc_norm_le (s₁ := s₁) (b₁ := b₁) (a := a) hh hw hS z k hr0 hrh hδ0.le
    (fun j v hv => by
      have hv0 : v ∈ Set.Icc (0 : ℝ) T := ⟨hkh.trans hv.1, hv.2.trans hT⟩
      have hh0 : h ≤ h0 := hhη.trans (min_le_left _ _)
      refine ⟨H j v (k * h + r) hv0 ⟨by linarith, by linarith⟩ ?_,
        H j v (k * h) hv0 ⟨hkh, by linarith⟩ ?_⟩
      · rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
      · rw [abs_le]; constructor <;> linarith [hv.1, hv.2])
  refine hb.trans ?_
  have e1 : 3 * d ^ 2 * S * δ ≤ ε / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hh2 : h ≤ ε / (4 * d * S + 1) := hhη.trans (min_le_right _ _)
  have e2 : 2 * d * S * h ≤ ε / 2 := by
    rw [le_div_iff₀ (by positivity)] at hh2
    nlinarith [mul_nonneg hD hS0, mul_nonneg (mul_nonneg hD hS0) hh.le]
  nlinarith

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem cont_of_lip2 {φ : SDEState d → SDEState d → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hφL : ∀ a y a' y', |φ a y - φ a' y'| ≤ Λ * (‖a - a'‖ + ‖y - y'‖)) :
    Continuous fun p : SDEState d × SDEState d => φ p.1 p.2 := by
  rw [Metric.continuous_iff]
  intro p ε hε
  refine ⟨ε / (2 * Λ + 1), div_pos hε (by positivity), fun q hq => ?_⟩
  rw [Real.dist_eq]
  have h1 : ‖q.1 - p.1‖ ≤ dist q p := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have h2 : ‖q.2 - p.2‖ ≤ dist q p := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_right _ _
  have h3 : (2 * Λ) * dist q p ≤ (2 * Λ) * (ε / (2 * Λ + 1)) :=
    mul_le_mul_of_nonneg_left hq.le (by positivity)
  have h4 : (2 * Λ) * (ε / (2 * Λ + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; linarith only [hε]
  calc |φ q.1 q.2 - φ p.1 p.2| ≤ Λ * (‖q.1 - p.1‖ + ‖q.2 - p.2‖) := hφL _ _ _ _
    _ ≤ Λ * (dist q p + dist q p) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hΛ
    _ < ε := by linarith only [h3, h4]

theorem cell_tendsto {w : ℝ≥0 → SDEState d} (hw : Continuous w) {S : ℝ}
    (hS : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (T : ℝ) {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n)
    (hlim : Tendsto hn atTop (𝓝 0)) (a z : ℕ → SDEState d) (k : ℕ → ℕ) (r : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n ∧ r n ≤ hn n) (hk : ∀ᶠ n in atTop, (k n : ℝ) * hn n + hn n ≤ T) :
    Tendsto (fun n => ‖cellInc s₁ b₁ (hn n) w (a n) (z n) (k n) (r n)‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, H⟩ := cell_small (s₁ := s₁) (b₁ := b₁) hw hS T (half_pos hε)
  filter_upwards [hk, (tendsto_order.1 hlim).2 η hη] with n hkn hhn
  rw [Real.dist_eq, sub_zero, abs_norm]
  exact (H (hn n) (hpos n) hhn.le (a n) (z n) (k n) (r n) (hr n).1 (hr n).2 hkn).trans_lt
    (half_lt_self hε)

theorem apx_pt {φ : SDEState d → SDEState d → ℝ} {K Λ e : ℝ} (hΛ : 0 ≤ Λ)
    (hφK : ∀ a y, |φ a y| ≤ K)
    (hφL : ∀ a y a' y', |φ a y - φ a' y'| ≤ Λ * (‖a - a'‖ + ‖y - y'‖))
    (a z x y : SDEState d) (hxy : ‖x - y‖ ≤ e) :
    |φ a z - φ x x| ≤ 2 * Λ * e + min (2 * K) (Λ * (2 * ‖y - z‖ + ‖a - z‖)) := by
  have hb : |φ a z - φ x x| ≤ 2 * K := (abs_sub _ _).trans (by linarith [hφK a z, hφK x x])
  have h1 : ‖a - x‖ ≤ ‖a - z‖ + ‖y - z‖ + ‖x - y‖ := by
    have : a - x = (a - z) - (y - z) - (x - y) := by abel
    rw [this]; exact (norm_sub_le _ _).trans (by linarith [norm_sub_le (a - z) (y - z)])
  have h2 : ‖z - x‖ ≤ ‖y - z‖ + ‖x - y‖ := by
    have : z - x = -(y - z) - (x - y) := by abel
    rw [this]; exact (norm_sub_le _ _).trans (by rw [norm_neg])
  have hl : |φ a z - φ x x| ≤ Λ * (2 * ‖y - z‖ + ‖a - z‖) + 2 * Λ * e := by
    refine (hφL a z x x).trans ?_
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hΛ
    nlinarith
  have he : 0 ≤ 2 * Λ * e := by
    have : 0 ≤ e := (norm_nonneg _).trans hxy
    positivity
  rcases le_total (2 * K) (Λ * (2 * ‖y - z‖ + ‖a - z‖)) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem euler_apx [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0))
    (T : ℝ≥0) (j : ℕ → ℕ)
    (hj : ∀ n, 1 ≤ j n ∧ (j n : ℝ) * hn n ≤ T ∧ (T : ℝ) ≤ j n * hn n + hn n)
    (φ : ℕ → SDEState d → SDEState d → ℝ) {K Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hφK : ∀ n a y, |φ n a y| ≤ K)
    (hφL : ∀ n a y a' y', |φ n a y - φ n a' y'| ≤ Λ * (‖a - a'‖ + ‖y - y'‖))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, |∫ ω, φ n (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n)).1
        (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n)).2 ∂P -
        ∫ ω, φ n (X T ω) (X T ω) ∂P| ≤
      2 * K * (P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R}ᶜ).toReal + η := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hφK 0 0 0)
  set A : ℕ → Ω → SDEState d := fun n ω => (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n)).1
    with hA
  set Z : ℕ → Ω → SDEState d := fun n ω => (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n)).2
    with hZ
  set Y : ℕ → Ω → SDEState d := fun n ω => eulerY s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ T with hY
  have hG' : ∀ r t : ℝ≥0, r ≤ t → ∀ i, Measurable[(fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) t]
      fun ω => W r ω i :=
    fun r _ _ i => (EuclideanSpace.proj i).continuous.measurable.comp (hW.1 r)
  have mA : ∀ n, Measurable (A n) := fun n =>
    (eulerZZ_meas_G hG' monotone_const hW.2.1 (hpos n) hs₁ hb₁ x₀ x₀ (j n)).1
  have mZ : ∀ n, Measurable (Z n) := fun n =>
    (eulerZZ_meas_G hG' monotone_const hW.2.1 (hpos n) hs₁ hb₁ x₀ x₀ (j n)).2
  have mY : ∀ n, Measurable (Y n) := fun n =>
    eulerY_meas_G hG' monotone_const hW.2.1 (hpos n) hs₁ hb₁ x₀ x₀ T
  have mX : Measurable (X T) := hX.1 T
  have iφ : ∀ n {U V : Ω → SDEState d}, Measurable U → Measurable V →
      Integrable (fun ω => φ n (U ω) (V ω)) P := fun n U V hU hV =>
    memLp_one_iff_integrable.1 (MemLp.of_bound
      ((cont_of_lip2 hΛ (hφL n)).measurable.comp (hU.prodMk hV)).aestronglyMeasurable K
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hφK n _ _))
  -- the tolerance
  set e : ℝ := η / (6 * Λ + 1) with he
  have he0 : 0 < e := div_pos hη (by positivity)
  have he3 : 2 * Λ * e ≤ η / 3 := by
    rw [he, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- (1) convergence in probability on the stay event
  have hclose := euler_close_tendsto hW x₀ hσ hb hX hs₁ hb₁ hR hL hSg hLg hag hpos hlim
    (pow_pos he0 2) T
  have hp := (ENNReal.tendsto_nhds_zero.1 hclose) (ENNReal.ofReal (η / (3 * (2 * K + 1))))
    (by simp only [gt_iff_lt, ENNReal.ofReal_pos]; positivity)
  -- (2) the cell terms
  set F : ℕ → Ω → ℝ := fun n ω => min (2 * K) (Λ * (2 * ‖Y n ω - Z n ω‖ + ‖A n ω - Z n ω‖))
    with hF
  have mF : ∀ n, Measurable (F n) := fun n =>
    measurable_const.min (measurable_const.mul
      ((((mY n).sub (mZ n)).norm.const_mul 2).add ((mA n).sub (mZ n)).norm))
  have F0 : ∀ n ω, 0 ≤ F n ω := fun n ω => le_min (by positivity) (by positivity)
  have hYZ : ∀ n ω, Y n ω - Z n ω = cellInc s₁ b₁ (hn n) (fun s => W s ω) (A n ω) (Z n ω) (j n)
      ((T : ℝ) - j n * hn n) := fun n ω => by
    have := eulerY_cell (s₁ := s₁) (b₁ := b₁) (hpos n) (hW.2.1 ω) x₀ x₀ (j n) (u := (T : ℝ))
      ⟨(hj n).2.1, by linarith [(hj n).2.2]⟩
    simp only [hY, hZ, hA]
    rw [this]; abel
  have hAZ : ∀ n ω, ‖A n ω - Z n ω‖ = ‖cellInc s₁ b₁ (hn n) (fun s => W s ω)
      (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n - 1)).1
      (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n - 1)).2 (j n - 1) (hn n)‖ := fun n ω => by
    obtain ⟨k, hk⟩ : ∃ k, j n = k + 1 := ⟨j n - 1, by have := (hj n).1; omega⟩
    simp only [hA, hZ, hk, Nat.add_sub_cancel, eulerZZ]
    rw [sub_add_cancel_left, norm_neg]
  have hev1 : ∀ᶠ n in atTop, hn n ≤ 1 := (tendsto_order.1 hlim).2 1 one_pos |>.mono fun n h => h.le
  have hFlim : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 0) := fun ω => by
    have t1 := cell_tendsto (s₁ := s₁) (b₁ := b₁) (hW.2.1 ω) hSg ((T : ℝ) + 1) hpos hlim
      (fun n => A n ω) (fun n => Z n ω) j (fun n => (T : ℝ) - j n * hn n)
      (fun n => ⟨by linarith [(hj n).2.1], by linarith [(hj n).2.2]⟩)
      (hev1.mono fun n h1 => by linarith [(hj n).2.1])
    have t2 := cell_tendsto (s₁ := s₁) (b₁ := b₁) (hW.2.1 ω) hSg ((T : ℝ) + 1) hpos hlim
      (fun n => (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n - 1)).1)
      (fun n => (eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ (j n - 1)).2) (fun n => j n - 1)
      (fun n => hn n) (fun n => ⟨(hpos n).le, le_rfl⟩)
      (Eventually.of_forall fun n => by
        have h1 : ((j n - 1 : ℕ) : ℝ) + 1 = j n := by
          have := (hj n).1; exact_mod_cast (Nat.sub_add_cancel this)
        nlinarith [(hj n).2.1, hpos n])
    have t3 : Tendsto (fun n => Λ * (2 * ‖Y n ω - Z n ω‖ + ‖A n ω - Z n ω‖)) atTop (𝓝 0) := by
      have := (t1.const_mul 2).add t2
      simp only [mul_zero, add_zero] at this
      have := this.const_mul Λ
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      simp only [hYZ, hAZ]
    exact squeeze_zero (fun n => F0 n ω) (fun n => min_le_right _ _) t3
  have hFint : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => 2 * K)
      (fun n => (mF n).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (F0 n ω)]; exact min_le_left _ _)
      (ae_of_all _ hFlim)
    simpa using this
  have hF3 := (tendsto_order.1 hFint).2 (η / 3) (by positivity)
  filter_upwards [hp, hF3] with n hpn hFn
  -- (3) pointwise bound and integration
  set E : Set Ω := {ω | e ^ 2 < ‖X T ω - Y n ω‖ ^ 2} with hE
  have mE : MeasurableSet E := measurableSet_lt measurable_const ((mX.sub (mY n)).norm.pow_const 2)
  have hpt : ∀ ω, |φ n (A n ω) (Z n ω) - φ n (X T ω) (X T ω)| ≤
      2 * K * E.indicator 1 ω + (2 * Λ * e + F n ω) := fun ω => by
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have := (abs_sub _ _).trans (add_le_add (hφK n (A n ω) (Z n ω)) (hφK n (X T ω) (X T ω)))
      have : 0 ≤ 2 * Λ * e := by positivity
      linarith [F0 n ω]
    · rw [Set.indicator_of_notMem hω, mul_zero, zero_add]
      have hxy : ‖X T ω - Y n ω‖ ≤ e := by
        by_contra hc; push_neg at hc
        exact hω (pow_lt_pow_left₀ hc he0.le two_ne_zero)
      exact apx_pt hΛ (hφK n) (hφL n) _ _ _ _ hxy
  have hEle : P E ≤ P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R}ᶜ +
      P {ω | (∀ s ≤ T, ‖X s ω‖ ≤ R) ∧ e ^ 2 < ‖X T ω - eulerY s₁ b₁ (hn n)
        (fun s => W s ω) x₀ x₀ T‖ ^ 2} := by
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_cases hs : ∀ s ≤ T, ‖X s ω‖ ≤ R
    · exact Or.inr ⟨hs, hω⟩
    · exact Or.inl hs
  have hEr : (P E).toReal ≤ (P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R}ᶜ).toReal + η / (3 * (2 * K + 1)) := by
    have := ENNReal.toReal_mono (by finiteness) (hEle.trans (add_le_add le_rfl hpn))
    rwa [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal (by positivity)] at this
  have hKe : 2 * K * (η / (3 * (2 * K + 1))) ≤ η / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have iE : Integrable (fun ω => 2 * K * E.indicator 1 ω) P :=
    ((integrable_const (1 : ℝ)).indicator mE).const_mul _
  have iF : Integrable (F n) P := memLp_one_iff_integrable.1 (MemLp.of_bound
      (mF n).aestronglyMeasurable (2 * K) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (F0 n ω)]; exact min_le_left _ _))
  have i2 : Integrable (fun ω => 2 * Λ * e + F n ω) P := (integrable_const _).add iF
  calc |∫ ω, φ n (A n ω) (Z n ω) ∂P - ∫ ω, φ n (X T ω) (X T ω) ∂P|
      = |∫ ω, (φ n (A n ω) (Z n ω) - φ n (X T ω) (X T ω)) ∂P| := by
        rw [integral_sub (iφ n (mA n) (mZ n)) (iφ n mX mX)]
    _ ≤ ∫ ω, |φ n (A n ω) (Z n ω) - φ n (X T ω) (X T ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2 * K * E.indicator 1 ω + (2 * Λ * e + F n ω)) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
          (iE.add i2) (ae_of_all _ hpt)
    _ = 2 * K * (P E).toReal + (2 * Λ * e + ∫ ω, F n ω ∂P) := by
        rw [integral_add iE i2, integral_const_mul,
          integral_indicator_one mE, integral_add (integrable_const _) iF, integral_const]
        simp [measureReal_def]
    _ ≤ 2 * K * (P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R}ᶜ).toReal + η := by
        have := mul_le_mul_of_nonneg_left hEr (by positivity : (0 : ℝ) ≤ 2 * K)
        nlinarith

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f6

end ItoLib

-- ===== O =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10g

end ItoLib

-- ===== P =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

variable {d : ℕ}

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

end M10j

end ItoLib

-- ===== Q =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

-- ===== R =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

-- ===== S =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

-- ===== V =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

-- ===== W =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

end M11d

end ItoLib

-- ===== TA =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TA
/-! TA (s31): universe-polymorphic Markov statement (Ω : Type*), for the theorem_1_1 glue. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end TA

end ItoLib

-- ===== TC =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TC
/-! TC (s31): the new child `StochKolmogorov.Persist.markov_property` of the theorem_1_1 reduction. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end TC

end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open EthierKurtz in
set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hlim : Tendsto hn atTop (𝓝 0))
    (T : ℝ≥0) (j : ℕ → ℕ)
    (hj : ∀ n, 1 ≤ j n ∧ (j n : ℝ) * hn n ≤ T ∧ (T : ℝ) ≤ j n * hn n + hn n)
    (φ : ℕ → SDEState d → SDEState d → ℝ) {K Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hφK : ∀ n a y, |φ n a y| ≤ K)
    (hφL : ∀ n a y a' y', |φ n a y - φ n a' y'| ≤ Λ * (‖a - a'‖ + ‖y - y'‖))
    {η : ℝ} (hη : 0 < η)
    (Z : ℕ → Ω → ℕ → SDEState d × SDEState d) (hZ0 : ∀ n ω, Z n ω 0 = (x₀, x₀))
    (hZs : ∀ n ω (k : ℕ), Z n ω (k + 1) = ((Z n ω k).2, (Z n ω k).2 + WithLp.toLp 2 fun i =>
      (∑ j', (s₁ (Z n ω k).1 (i, j') * (W ((k : ℝ) * hn n + hn n).toNNReal ω j' -
          W ((k : ℝ) * hn n).toNNReal ω j') +
        (s₁ (Z n ω k).2 (i, j') - s₁ (Z n ω k).1 (i, j')) / hn n *
          (hn n * W ((k : ℝ) * hn n + hn n).toNNReal ω j' -
            ∫ v in ((k : ℝ) * hn n)..((k : ℝ) * hn n + hn n), W v.toNNReal ω j'))) +
      b₁ (Z n ω k).1 i * hn n + (b₁ (Z n ω k).2 i - b₁ (Z n ω k).1 i) * hn n ^ 2 / (2 * hn n))) :
    ∀ᶠ n in atTop, |∫ ω, φ n (Z n ω (j n)).1
        (Z n ω (j n)).2 ∂P -
        ∫ ω, φ n (X T ω) (X T ω) ∂P| ≤
      2 * K * (P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R}ᶜ).toReal + η := by
  have hZe : Z = fun n ω k => ItoLib.eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ k := by
    funext n ω k
    induction k with
    | zero => exact hZ0 n ω
    | succ k ih => rw [hZs n ω k, ih]; rfl
  subst hZe
  exact ItoLib.euler_apx hW x₀ hσ hb hX hs₁ hb₁ hR hL hSg hLg hag hpos hlim T j hj φ hΛ hφK hφL hη
