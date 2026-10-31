-- Prove2me | solution 1 for EthierKurtz.sde_markov_property_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T22:14:12.73142+00:00
-- url     : https://prove2.me/submissions/28ffa05c-de24-42dc-b738-a8a529c1cf33

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_EthierKurtz_euler_scheme_approx

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

end M4

section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5

section M5b

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

end M6refine

section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

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

theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩

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

end M6osc

section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy

section M6limit
variable [MeasurableSpace Ω]

end M6limit

section M6trunc

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

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

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

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

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

variable {s₁ b₁ h w}

theorem wr_continuous (hw : Continuous w) (j : Fin d) : Continuous (wr w j) :=
  ((EuclideanSpace.proj j).continuous.comp hw).comp continuous_real_toNNReal

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

end M10b2w

section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

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

end M10c5s

section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

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

theorem floor_mem_cell (hh : 0 < h) {u : ℝ} (hu : 0 ≤ u) :
    u ∈ Set.Icc ((⌊u / h⌋₊ : ℝ) * h) ((⌊u / h⌋₊ + 1) * h) := by
  have h1 := Nat.floor_le (div_nonneg hu hh.le)
  have h2 := Nat.lt_floor_add_one (u / h)
  exact ⟨(le_div_iff₀ hh).1 h1, ((div_lt_iff₀ hh).1 h2).le⟩

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

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

/-- σ-algebra of the Brownian increments after time `s`. -/
def futBrownian [MeasurableSpace Ω] (W : ℝ≥0 → Ω → SDEState d) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) inferInstance

/-- Integrand of the cell noise. -/
noncomputable def zetaF (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (j : Fin d) (u : ℝ) (ω : Ω) : ℝ :=
  W (s + h) ω j - W (s + u.toNNReal) ω j

/-- The cell noise. -/
noncomputable def cellZeta (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (j : Fin d) (ω : Ω) : ℝ :=
  (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω

theorem incr_meas_fut [MeasurableSpace Ω] (W : ℝ≥0 → Ω → SDEState d) (s u : ℝ≥0) (j : Fin d) :
    Measurable[futBrownian W s] fun ω => W (s + u) ω j - W s ω j := by
  have hG : Measurable[futBrownian W s]
      (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) := Measurable.of_comap_le le_rfl
  let _ : MeasurableSpace Ω := futBrownian W s
  exact measurable_pi_iff.1 hG (u, j)

theorem zetaF_continuous {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (s h : ℝ≥0) (j : Fin d) (ω : Ω) : Continuous fun u => zetaF W s h j u ω := by
  unfold zetaF
  have : Continuous fun u : ℝ => W (s + u.toNNReal) ω j :=
    ((EuclideanSpace.proj j).continuous.comp (hWc ω)).comp
      (continuous_const.add continuous_real_toNNReal)
  exact continuous_const.sub this

theorem zeta_meas_fut [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    (hWc : ∀ ω, Continuous fun s => W s ω) (s h : ℝ≥0) (j : Fin d) :
    Measurable[futBrownian W s] (cellZeta W s h j) := by
  have hm : ∀ p : ℝ≥0, p ≤ h → Measurable[futBrownian W s]
      fun ω => W (s + h) ω j - W (s + p) ω j := fun p _ => by
    have e : (fun ω => W (s + h) ω j - W (s + p) ω j) =
        fun ω => (W (s + h) ω j - W s ω j) - (W (s + p) ω j - W s ω j) := by
      funext ω; ring
    rw [e]
    exact (incr_meas_fut W s h j).sub (incr_meas_fut W s p j)
  have hc : ∀ ω, Continuous fun p : ℝ≥0 => W (s + h) ω j - W (s + p) ω j := fun ω =>
    continuous_const.sub (((EuclideanSpace.proj j).continuous.comp (hWc ω)).comp
      (continuous_const.add continuous_id))
  exact (measurable_intervalIntegral_of_continuous (futBrownian W s) h hm hc).const_mul _

theorem indepFun_past_fut [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s : ℝ≥0) {a b : Ω → ℝ}
    (ha : Measurable[completedBrownianPast P W (fun _ => x₀) s] a)
    (hb : Measurable[futBrownian W s] b) : IndepFun a b P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (stdBrownian_indep_completedPast hW x₀ s) ha.comap_le) hb.comap_le

theorem futBrownian_le [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s : ℝ≥0) : futBrownian W s ≤ ‹MeasurableSpace Ω› := by
  refine MeasurableSpace.comap_le_iff_le_map.2 ?_
  refine (measurable_pi_lambda _ fun p => ?_).le_map
  exact (stdBrownian_coord_measurable hW _ _).sub (stdBrownian_coord_measurable hW _ _)

theorem zetaF_moments [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) {u : ℝ} (hu0 : 0 ≤ u) (huh : u ≤ h) :
    ∫ ω, zetaF W s h j u ω ∂P = 0 ∧ ∫ ω, zetaF W s h j u ω ^ 2 ∂P = h - u ∧
      MemLp (zetaF W s h j u) 2 P := by
  have hu' : u.toNNReal ≤ h := Real.toNNReal_le_iff_le_coe.2 huh
  have e : s + h = (s + u.toNNReal) + (h - u.toNNReal) := by
    rw [add_assoc, add_tsub_cancel_of_le hu']
  have hz : zetaF W s h j u = fun ω => W ((s + u.toNNReal) + (h - u.toNNReal)) ω j -
      W (s + u.toNNReal) ω j := by
    funext ω; unfold zetaF; rw [← e]
  rw [hz]
  refine ⟨stdBrownian_integral_increment hW _ _ j, ?_, ?_⟩
  · rw [stdBrownian_integral_increment_sq hW _ _ j, NNReal.coe_sub hu', Real.coe_toNNReal _ hu0]
  · exact (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)

theorem zetaF_measurable_uncurry [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s h : ℝ≥0) (j : Fin d) :
    Measurable (Function.uncurry (zetaF W s h j)) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => zetaF_continuous hW.2.1 s h j ω)
    (fun u => (stdBrownian_coord_measurable hW _ j).sub (stdBrownian_coord_measurable hW _ j))

theorem integrable_restrict_prod [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℝ → Ω → ℝ} (hf : Measurable (Function.uncurry f)) {h : ℝ} (hh : 0 ≤ h) {K : ℝ}
    (hb : ∀ u ∈ Set.Ioc (0 : ℝ) h, ∫⁻ ω, ‖f u ω‖ₑ ∂P ≤ ENNReal.ofReal K) :
    Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc 0 h)).prod P) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hf.enorm.aemeasurable]
  calc ∫⁻ u, ∫⁻ ω, ‖Function.uncurry f (u, ω)‖ₑ ∂P ∂(volume.restrict (Set.uIoc 0 h))
      ≤ ∫⁻ _u, ENNReal.ofReal K ∂(volume.restrict (Set.uIoc 0 h)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_uIoc).2
          (Eventually.of_forall fun u hu => ?_))
        rw [Set.uIoc_of_le hh] at hu
        exact hb u hu
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [Set.uIoc_of_le hh]; exact measure_Ioc_lt_top)

theorem lintegral_ofReal_sq_eq [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ} (hg : MemLp g 2 P) :
    ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P = ENNReal.ofReal (∫ ω, g ω ^ 2 ∂P) :=
  (ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg (g ω))).symm

theorem sq_intervalIntegral_le {F : ℝ → ℝ} (hF : Continuous F) {h : ℝ} (hh : 0 < h) :
    (∫ u in (0 : ℝ)..h, F u) ^ 2 ≤ h * ∫ u in (0 : ℝ)..h, F u ^ 2 := by
  set I := ∫ u in (0 : ℝ)..h, F u
  set J := ∫ u in (0 : ℝ)..h, F u ^ 2
  set m := I / h with hm
  have hmI : m * h = I := by rw [hm]; field_simp
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..h, (F u - m) ^ 2 :=
    intervalIntegral.integral_nonneg hh.le fun u _ => sq_nonneg _
  have e : ∫ u in (0 : ℝ)..h, (F u - m) ^ 2 = J - 2 * m * I + m ^ 2 * h := by
    have : (fun u => (F u - m) ^ 2) = fun u => F u ^ 2 - 2 * m * F u + m ^ 2 := by
      funext u; ring
    have i1 : IntervalIntegrable (fun u => F u ^ 2 - 2 * m * F u) volume 0 h :=
      ((hF.pow 2).sub (continuous_const.mul hF)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => F u ^ 2) volume 0 h := (hF.pow 2).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => 2 * m * F u) volume 0 h :=
      (continuous_const.mul hF).intervalIntegrable _ _
    rw [this, intervalIntegral.integral_add i1 intervalIntegrable_const,
      intervalIntegral.integral_sub i2 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have hm2 : m ^ 2 * h = m * I := by rw [← hmI]; ring
  have h1 : 0 ≤ J - m * I := by linarith only [h0, hm2]
  have e2 : I ^ 2 = h * (m * I) := by rw [← hmI]; ring
  linarith only [mul_nonneg hh.le h1, e2]

theorem cellZeta_moments [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (s h : ℝ≥0) (hh : 0 < (h : ℝ))
    (j : Fin d) :
    ∫ ω, cellZeta W s h j ω ∂P = 0 ∧ MemLp (cellZeta W s h j) 2 P ∧
      ∫ ω, cellZeta W s h j ω ^ 2 ∂P ≤ h / 2 := by
  have hmeas := zetaF_measurable_uncurry hW s h j
  have hmom := fun u (hu : u ∈ Set.Ioc (0 : ℝ) h) => zetaF_moments hW s h j (P := P) hu.1.le hu.2
  -- integrability of `zetaF` and `zetaF²` on the product
  have hI1 : Integrable (Function.uncurry (zetaF W s h j))
      ((volume.restrict (Set.uIoc 0 (h : ℝ))).prod P) := by
    refine integrable_restrict_prod hmeas h.2 (K := h + 1) fun u hu => ?_
    obtain ⟨-, h2, hL⟩ := hmom u hu
    calc ∫⁻ ω, ‖zetaF W s h j u ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (zetaF W s h j u ω ^ 2 + 1) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          linarith only [sq_nonneg (|zetaF W s h j u ω| - 1 / 2), sq_abs (zetaF W s h j u ω)]
      _ = ENNReal.ofReal (h - u + 1) := by
          have hint : Integrable (fun ω => zetaF W s h j u ω ^ 2 + 1) P :=
            hL.integrable_sq.add (integrable_const 1)
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun ω => by positivity), integral_add hL.integrable_sq
            (integrable_const 1), h2]
          simp
      _ ≤ ENNReal.ofReal (h + 1) := ENNReal.ofReal_le_ofReal (by linarith [hu.1])
  have hI2 : Integrable (Function.uncurry fun u ω => zetaF W s h j u ω ^ 2)
      ((volume.restrict (Set.uIoc 0 (h : ℝ))).prod P) := by
    refine integrable_restrict_prod (hmeas.pow_const 2) h.2 (K := h) fun u hu => ?_
    obtain ⟨-, h2, hL⟩ := hmom u hu
    calc ∫⁻ ω, ‖zetaF W s h j u ω ^ 2‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (zetaF W s h j u ω ^ 2) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ = ENNReal.ofReal (h - u) := by rw [lintegral_ofReal_sq_eq hL, h2]
      _ ≤ ENNReal.ofReal h := ENNReal.ofReal_le_ofReal (by linarith [hu.1])
  have hsw1 := intervalIntegral_integral_swap hI1
  have hsw2 := intervalIntegral_integral_swap hI2
  -- mean zero
  have hmean : ∫ ω, (∫ u in (0 : ℝ)..h, zetaF W s h j u ω) ∂P = 0 := by
    rw [← hsw1]
    refine (intervalIntegral.integral_congr_ae ?_).trans intervalIntegral.integral_zero
    refine Eventually.of_forall fun u hu => ?_
    rw [Set.uIoc_of_le (NNReal.coe_nonneg h)] at hu
    exact (hmom u hu).1
  -- second moment of the integral
  have hsq : ∫ ω, (∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) ∂P = (h : ℝ) ^ 2 / 2 := by
    rw [← hsw2]
    have : ∫ u in (0 : ℝ)..h, ∫ ω, zetaF W s h j u ω ^ 2 ∂P = ∫ u in (0 : ℝ)..h, ((h : ℝ) - u) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
      rw [Set.uIoc_of_le (NNReal.coe_nonneg h)] at hu
      exact (hmom u hu).2.1
    rw [this, intervalIntegral.integral_sub (f := fun _ => (h : ℝ)) (g := fun u => u) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    simp; ring
  have hJi : Integrable (fun ω => ∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) P := by
    have := hI2.integral_prod_right
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg h), Set.uIoc_of_le (NNReal.coe_nonneg h)]
  have hZm : AEStronglyMeasurable (cellZeta W s h j) P :=
    ((zeta_meas_fut hW.2.1 s h j).mono (futBrownian_le hW s) le_rfl).aestronglyMeasurable
  have hpt : ∀ ω, cellZeta W s h j ω ^ 2 ≤
      (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2 := fun ω => by
    have hc := sq_intervalIntegral_le (zetaF_continuous hW.2.1 s h j ω) hh
    unfold cellZeta
    rw [mul_pow]
    calc (1 / (h : ℝ)) ^ 2 * (∫ u in (0 : ℝ)..h, zetaF W s h j u ω) ^ 2
        ≤ (1 / (h : ℝ)) ^ 2 * ((h : ℝ) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by field_simp
  have hL2 : MemLp (cellZeta W s h j) 2 P := by
    refine (memLp_two_iff_integrable_sq hZm).2 ?_
    refine (hJi.const_mul (1 / (h : ℝ))).mono' (hZm.pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨?_, hL2, ?_⟩
  · unfold cellZeta
    rw [integral_const_mul, hmean, mul_zero]
  · calc ∫ ω, cellZeta W s h j ω ^ 2 ∂P ≤ ∫ ω, (1 / (h : ℝ)) *
          (∫ u in (0 : ℝ)..h, zetaF W s h j u ω ^ 2) ∂P :=
          integral_mono hL2.integrable_sq (hJi.const_mul _) hpt
      _ = (h : ℝ) / 2 := by rw [integral_const_mul, hsq]; field_simp

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

/-- The cell noise vector. -/
noncomputable def cellNoise (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (A B : Ω → SDEDiffusion d)
    (ω : Ω) : SDEState d :=
  WithLp.toLp 2 fun i => ∑ j, (A ω (i, j) * (W (s + h) ω j - W s ω j) +
    B ω (i, j) * cellZeta W s h j ω)

theorem state_norm_sq (x : SDEState d) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem diff_norm_sq (A : SDEDiffusion d) : ‖A‖ ^ 2 = ∑ i, ∑ j, A (i, j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.univ_product_univ, Finset.sum_product]
  simp [Real.norm_eq_abs, sq_abs]

theorem cellNoise_pt (D : SDEState d) (a b : Fin d → Fin d → ℝ) (ξ ζ : Fin d → ℝ) :
    ‖D + WithLp.toLp 2 (fun i => ∑ j, (a i j * ξ j + b i j * ζ j))‖ ^ 2 ≤
      ‖D‖ ^ 2 + 2 * ∑ i, ∑ j, (D i * a i j * ξ j + D i * b i j * ζ j) +
        2 * d * ∑ i, ∑ j, (a i j ^ 2 * ξ j ^ 2 + b i j ^ 2 * ζ j ^ 2) := by
  rw [state_norm_sq, state_norm_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hN : (∑ j, (a i j * ξ j + b i j * ζ j)) ^ 2 ≤ d * ∑ j, 2 * (a i j ^ 2 * ξ j ^ 2 + b i j ^ 2 * ζ j ^ 2) := by
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
    linarith only [sq_nonneg (a i j * ξ j - b i j * ζ j)]
  have e : (D + WithLp.toLp 2 (fun i => ∑ j, (a i j * ξ j + b i j * ζ j))) i =
      D i + ∑ j, (a i j * ξ j + b i j * ζ j) := rfl
  rw [e, ← Finset.mul_sum] at *
  have e2 : ∑ j, (D i * a i j * ξ j + D i * b i j * ζ j) = D i * ∑ j, (a i j * ξ j + b i j * ζ j) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [e2]
  linarith only [hN]

set_option maxHeartbeats 1000000 in
theorem cellNoise_step [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) {D : Ω → SDEState d} {A B : Ω → SDEDiffusion d} {K : ℝ}
    (hD : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => D ω i)
    (hDL : ∀ i, MemLp (fun ω => D ω i) 2 P)
    (hA : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p)
    (hB : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p)
    (hAK : ∀ ω, ‖A ω‖ ≤ K) (hBK : ∀ ω, ‖B ω‖ ≤ K) :
    ∫ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ∂P ≤
      ∫ ω, ‖D ω‖ ^ 2 ∂P + 2 * d * h * ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P := by
  set ξ : Fin d → Ω → ℝ := fun j ω => W (s + h) ω j - W s ω j with hξ
  set ζ : Fin d → Ω → ℝ := fun j ω => cellZeta W s h j ω with hζ
  have hK : ∀ ω, 0 ≤ K := fun ω => (norm_nonneg _).trans (hAK ω)
  have hm := stdBrownian_coord_measurable hW
  have hξL : ∀ j, MemLp (ξ j) 2 P := fun j =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have hζm := fun j => cellZeta_moments (P := P) hW s h hh j
  have hasm : ∀ {a : Ω → ℝ}, Measurable[completedBrownianPast P W (fun _ => x₀) s] a →
      AEStronglyMeasurable a P :=
    fun ha => aestronglyMeasurable_of_completedPast hW x₀ s ha
  have hζas : ∀ j, AEStronglyMeasurable (ζ j) P := fun j =>
    ((zeta_meas_fut hW.2.1 s h j).mono (futBrownian_le hW s) le_rfl).aestronglyMeasurable
  have hAb : ∀ ω p, |A ω p| ≤ K := fun ω p => by
    have := PiLp.norm_apply_le (A ω) p; rw [Real.norm_eq_abs] at this; exact this.trans (hAK ω)
  have hBb : ∀ ω p, |B ω p| ≤ K := fun ω p => by
    have := PiLp.norm_apply_le (B ω) p; rw [Real.norm_eq_abs] at this; exact this.trans (hBK ω)
  -- integrability of the pieces
  have aA : ∀ p, AEStronglyMeasurable (fun ω => A ω p) P := fun p => hasm (hA p)
  have aB : ∀ p, AEStronglyMeasurable (fun ω => B ω p) P := fun p => hasm (hB p)
  have iDA : ∀ i j, Integrable (fun ω => D ω i * A ω (i, j)) P := fun i j =>
    (((hDL i).integrable one_le_two).norm.const_mul K).mono' (((hDL i).1).mul (aA _))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hAb ω _) (abs_nonneg _))
  have iDB : ∀ i j, Integrable (fun ω => D ω i * B ω (i, j)) P := fun i j =>
    (((hDL i).integrable one_le_two).norm.const_mul K).mono' (((hDL i).1).mul (aB _))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hBb ω _) (abs_nonneg _))
  have indA : ∀ i j, IndepFun (fun ω => D ω i * A ω (i, j)) (ξ j) P := fun i j =>
    indepFun_completedPast_increment hW x₀ s h j ((hD i).mul (hA _))
  have indB : ∀ i j, IndepFun (fun ω => D ω i * B ω (i, j)) (ζ j) P := fun i j =>
    indepFun_past_fut hW x₀ s ((hD i).mul (hB _)) (zeta_meas_fut hW.2.1 s h j)
  have i1 : ∀ i j, Integrable (fun ω => D ω i * A ω (i, j) * ξ j ω) P := fun i j =>
    (indA i j).integrable_mul (iDA i j) ((hξL j).integrable one_le_two)
  have i2 : ∀ i j, Integrable (fun ω => D ω i * B ω (i, j) * ζ j ω) P := fun i j =>
    (indB i j).integrable_mul (iDB i j) ((hζm j).2.1.integrable one_le_two)
  have hsqK : ∀ x : ℝ, |x| ≤ K → x ^ 2 ≤ K ^ 2 := fun x hx => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have i3 : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 * ξ j ω ^ 2) P := fun i j =>
    ((hξL j).integrable_sq.const_mul (K ^ 2)).mono' (((aA _).pow 2).mul ((hξL j).1.pow 2))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hsqK _ (hAb ω _)) (sq_nonneg _))
  have i4 : ∀ i j, Integrable (fun ω => B ω (i, j) ^ 2 * ζ j ω ^ 2) P := fun i j =>
    ((hζm j).2.1.integrable_sq.const_mul (K ^ 2)).mono' (((aB _).pow 2).mul ((hζas j).pow 2))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hsqK _ (hBb ω _)) (sq_nonneg _))
  have iA2 : ∀ p, Integrable (fun ω => A ω p ^ 2) P := fun p =>
    (integrable_const (K ^ 2)).mono' ((aA p).pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqK _ (hAb ω p))
  have iB2 : ∀ p, Integrable (fun ω => B ω p ^ 2) P := fun p =>
    (integrable_const (K ^ 2)).mono' ((aB p).pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqK _ (hBb ω p))
  -- values
  have v1 : ∀ i j, ∫ ω, D ω i * A ω (i, j) * ξ j ω ∂P = 0 := fun i j =>
    integral_mul_increment_eq_zero hW x₀ s h j ((hD i).mul (hA _))
  have v2 : ∀ i j, ∫ ω, D ω i * B ω (i, j) * ζ j ω ∂P = 0 := fun i j => by
    rw [(indB i j).integral_fun_mul_eq_mul_integral (iDB i j).1 (hζas j), (hζm j).1, mul_zero]
  have v3 : ∀ i j, ∫ ω, A ω (i, j) ^ 2 * ξ j ω ^ 2 ∂P = (∫ ω, A ω (i, j) ^ 2 ∂P) * h := fun i j => by
    have := integral_sq_mul_increment_sq hW x₀ s h j (hA (i, j))
    simp only [mul_pow] at this
    exact this
  have v4 : ∀ i j, ∫ ω, B ω (i, j) ^ 2 * ζ j ω ^ 2 ∂P ≤ (∫ ω, B ω (i, j) ^ 2 ∂P) * h := fun i j => by
    have hi := indepFun_past_fut hW x₀ s ((hB (i, j)).pow_const 2)
      ((zeta_meas_fut hW.2.1 s h j).pow_const 2)
    rw [hi.integral_fun_mul_eq_mul_integral ((aB _).pow 2) ((hζas j).pow 2)]
    refine mul_le_mul_of_nonneg_left ((hζm j).2.2.trans (by linarith)) ?_
    exact integral_nonneg fun ω => sq_nonneg _
  have i12 : ∀ i j, Integrable (fun ω => D ω i * A ω (i, j) * ξ j ω +
      D ω i * B ω (i, j) * ζ j ω) P := fun i j => (i1 i j).add (i2 i j)
  have i34 : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 * ξ j ω ^ 2 +
      B ω (i, j) ^ 2 * ζ j ω ^ 2) P := fun i j => (i3 i j).add (i4 i j)
  have iAB : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 + B ω (i, j) ^ 2) P := fun i j =>
    (iA2 _).add (iB2 _)
  -- the pointwise bound, integrated
  set S1 : Ω → ℝ := fun ω => ∑ i, ∑ j, (D ω i * A ω (i, j) * ξ j ω +
      D ω i * B ω (i, j) * ζ j ω) with hS1d
  set S2 : Ω → ℝ := fun ω => ∑ i, ∑ j, (A ω (i, j) ^ 2 * ξ j ω ^ 2 + B ω (i, j) ^ 2 * ζ j ω ^ 2)
    with hS2d
  set T : Ω → ℝ := fun ω => ‖D ω‖ ^ 2 + 2 * S1 ω + 2 * d * S2 ω with hT
  have hpt : ∀ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ≤ T ω := fun ω =>
    cellNoise_pt (D ω) (fun i j => A ω (i, j)) (fun i j => B ω (i, j)) (fun j => ξ j ω)
      (fun j => ζ j ω)
  have iD2 : Integrable (fun ω => ‖D ω‖ ^ 2) P := by
    have : (fun ω => ‖D ω‖ ^ 2) = fun ω => ∑ i, D ω i ^ 2 := funext fun ω => state_norm_sq _
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hDL i).integrable_sq
  have iS1 : Integrable S1 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i12 i j
  have iS2 : Integrable S2 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i34 i j
  have iT : Integrable T P := (iD2.add (iS1.const_mul 2)).add (iS2.const_mul _)
  have hS1 : ∫ ω, S1 ω ∂P = 0 := by
    simp only [hS1d]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i12 i j]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => i12 i j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_add (i1 i j) (i2 i j), v1, v2, add_zero]
  have hS2 : ∫ ω, S2 ω ∂P = ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 * ξ j ω ^ 2 ∂P +
      ∫ ω, B ω (i, j) ^ 2 * ζ j ω ^ 2 ∂P) := by
    simp only [hS2d]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i34 i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => i34 i j]
    exact Finset.sum_congr rfl fun j _ => integral_add (i3 i j) (i4 i j)
  have hIT : ∫ ω, T ω ∂P = ∫ ω, ‖D ω‖ ^ 2 ∂P + 2 * ∫ ω, S1 ω ∂P + 2 * d * ∫ ω, S2 ω ∂P := by
    have e : T = (fun ω => ‖D ω‖ ^ 2) + (fun ω => 2 * S1 ω) + (fun ω => 2 * d * S2 ω) := rfl
    rw [e, integral_add' (iD2.add (iS1.const_mul 2)) (iS2.const_mul _),
      integral_add' iD2 (iS1.const_mul 2)]
    rw [integral_const_mul, integral_const_mul]
  have hAB : ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P =
      ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 ∂P + ∫ ω, B ω (i, j) ^ 2 ∂P) := by
    have : (fun ω => ‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) =
        fun ω => ∑ i, ∑ j, (A ω (i, j) ^ 2 + B ω (i, j) ^ 2) := funext fun ω => by
      rw [diff_norm_sq, diff_norm_sq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]
    rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iAB i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => iAB i j]
    exact Finset.sum_congr rfl fun j _ => integral_add (iA2 _) (iB2 _)
  calc ∫ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ∂P ≤ ∫ ω, T ω ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) iT
          (Eventually.of_forall hpt)
    _ ≤ ∫ ω, ‖D ω‖ ^ 2 ∂P + 2 * d * h * ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P := by
        have key : ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 * ξ j ω ^ 2 ∂P +
            ∫ ω, B ω (i, j) ^ 2 * ζ j ω ^ 2 ∂P) ≤
            (h : ℝ) * ∑ i, ∑ j, (∫ ω, A ω (i, j) ^ 2 ∂P + ∫ ω, B ω (i, j) ^ 2 ∂P) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [v3]
          linarith only [v4 i j]
        rw [hIT, hS1, hS2, hAB, mul_zero, add_zero]
        have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * d)
        linarith only [this]

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

theorem cellInc_eq {W : ℝ≥0 → Ω → SDEState d} (ω : Ω) (hWc : Continuous fun s => W s ω)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (a z : SDEState d) (k : ℕ) :
    cellInc s₁ b₁ (h : ℝ) (fun s => W s ω) a z k h =
      WithLp.toLp 2 (fun i => ∑ j, (s₁ a (i, j) * (W (((k : ℝ) * h).toNNReal + h) ω j -
          W ((k : ℝ) * h).toNNReal ω j) +
        (s₁ z (i, j) - s₁ a (i, j)) * cellZeta W ((k : ℝ) * h).toNNReal h j ω) +
        (h : ℝ) / 2 * (b₁ a i + b₁ z i)) := by
  set s : ℝ≥0 := ((k : ℝ) * h).toNNReal with hs
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) h.2
  have hadd : ∀ u : ℝ, 0 ≤ u → ((k : ℝ) * h + u).toNNReal = s + u.toNNReal := fun u hu => by
    rw [Real.toNNReal_add hk0 hu]
  have hw1 : ∀ j, wr (fun s => W s ω) j ((k : ℝ) * h + h) = W (s + h) ω j := fun j => by
    simp only [wr]; rw [hadd _ (NNReal.coe_nonneg h), Real.toNNReal_coe]
  have hw0 : ∀ j, wr (fun s => W s ω) j ((k : ℝ) * h) = W s ω j := fun j => rfl
  have hcont : ∀ j, Continuous fun u : ℝ => W (s + u.toNNReal) ω j := fun j =>
    (EuclideanSpace.proj j).continuous.comp
      (hWc.comp (continuous_const.add continuous_real_toNNReal))
  have hint : ∀ j, ∫ v in ((k : ℝ) * h)..((k : ℝ) * h + h), wr (fun s => W s ω) j v =
      ∫ u in (0 : ℝ)..h, W (s + u.toNNReal) ω j := fun j => by
    have e := intervalIntegral.integral_comp_add_left (fun v => wr (fun s => W s ω) j v)
      ((k : ℝ) * h) (a := 0) (b := h)
    simp only [add_zero] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by
      rcases Set.mem_uIcc.1 hu with h1 | h1
      · exact h1.1
      · exact (NNReal.coe_nonneg h).trans h1.1
    simp only [wr]; rw [hadd u hu0]
  have hz : ∀ j, cellZeta W s h j ω =
      (1 / (h : ℝ)) * ((h : ℝ) * W (s + h) ω j - ∫ u in (0 : ℝ)..h, W (s + u.toNNReal) ω j) :=
    fun j => by
      unfold cellZeta zetaF
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((hcont j).intervalIntegrable _ _), intervalIntegral.integral_const]
      simp [smul_eq_mul]
  unfold cellInc
  congr 1
  funext i
  have hsum : ∑ j, (s₁ a (i, j) * (wr (fun s => W s ω) j ((k : ℝ) * h + h) -
        wr (fun s => W s ω) j ((k : ℝ) * h)) + (s₁ z (i, j) - s₁ a (i, j)) / h *
        ((h : ℝ) * wr (fun s => W s ω) j ((k : ℝ) * h + h) -
          ∫ v in ((k : ℝ) * h)..((k : ℝ) * h + h), wr (fun s => W s ω) j v)) =
      ∑ j, (s₁ a (i, j) * (W (s + h) ω j - W s ω j) +
        (s₁ z (i, j) - s₁ a (i, j)) * cellZeta W s h j ω) :=
    Finset.sum_congr rfl fun j _ => by
      rw [hw1 j, hw0 j, hint j, hz j]; field_simp
  rw [hsum]
  field_simp
  ring

/-- A bounded, a.e.-strongly measurable factor keeps a real function in `L²`. -/
theorem memLp_two_bdd_mul [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {φ f : Ω → ℝ}
    {K : ℝ} (hφ : AEStronglyMeasurable φ P) (hK : ∀ ω, |φ ω| ≤ K) (hf : MemLp f 2 P) :
    MemLp (fun ω => φ ω * f ω) 2 P :=
  hf.mul' (p := ∞) (MemLp.of_bound hφ K (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hK ω))

theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

theorem coord_abs_le_diff (A : SDEDiffusion d) (p : Fin d × Fin d) : |A p| ≤ ‖A‖ := by
  have := PiLp.norm_apply_le A p; rwa [Real.norm_eq_abs] at this

/-- Grid values of the scheme driven by standard Brownian motion are in `L²`. -/
theorem eulerZZ_memLp [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hs : Continuous s₁) (hb : Continuous b₁) {S : ℝ}
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (a y : SDEState d) (k : ℕ) :
    (∀ i, MemLp (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 i) 2 P) ∧
      ∀ i, MemLp (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 i) 2 P := by
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hGm : Monotone (completedBrownianPast P W (fun _ => x₀)) :=
    fun s t hst => completedBrownianPast_mono P W _ hst
  induction k with
  | zero => simp only [eulerZZ]; exact ⟨fun i => memLp_const _, fun i => memLp_const _⟩
  | succ k ih =>
    refine ⟨fun i => ih.2 i, fun i => ?_⟩
    set s : ℝ≥0 := ((k : ℝ) * h).toNNReal with hsdef
    obtain ⟨m1, m2⟩ := eulerZZ_meas_G hG hGm hW.2.1 hh hs hb a y k
    have hsc : ∀ p, Measurable fun z : SDEState d => s₁ z p := fun p =>
      ((EuclideanSpace.proj p).continuous.comp hs).measurable
    have hbc : ∀ i, Measurable fun z : SDEState d => b₁ z i := fun i =>
      ((EuclideanSpace.proj i).continuous.comp hb).measurable
    have as1 : ∀ p, AEStronglyMeasurable
        (fun ω => s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 p) P := fun p =>
      aestronglyMeasurable_of_completedPast hW x₀ s ((hsc p).comp m1)
    have as2 : ∀ p, AEStronglyMeasurable
        (fun ω => s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 p) P := fun p =>
      aestronglyMeasurable_of_completedPast hW x₀ s ((hsc p).comp m2)
    have ab1 : ∀ i, AEStronglyMeasurable
        (fun ω => b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 i) P := fun i =>
      aestronglyMeasurable_of_completedPast hW x₀ s ((hbc i).comp m1)
    have ab2 : ∀ i, AEStronglyMeasurable
        (fun ω => b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 i) P := fun i =>
      aestronglyMeasurable_of_completedPast hW x₀ s ((hbc i).comp m2)
    have sb : ∀ x p, |s₁ x p| ≤ S := fun x p => (coord_abs_le_diff _ p).trans (hSg x).1
    have bb : ∀ x i, |b₁ x i| ≤ S := fun x i => (coord_abs_le_state _ i).trans (hSg x).2
    have hξ : ∀ j, MemLp (fun ω => W (s + h) ω j - W s ω j) 2 P := fun j =>
      (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
    have hζ : ∀ j, MemLp (cellZeta W s h j) 2 P := fun j => (cellZeta_moments hW s h hh j).2.1
    have e : (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y (k + 1)).2 i) = fun ω =>
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 i +
          ((∑ j, (s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 (i, j) *
              (W (s + h) ω j - W s ω j) +
            (s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 (i, j) -
              s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 (i, j)) * cellZeta W s h j ω)) +
            (h : ℝ) / 2 * (b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 i +
              b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 i)) := by
      funext ω
      simp only [eulerZZ]
      rw [PiLp.add_apply, cellInc_eq ω (hW.2.1 ω) hh]
    rw [e]
    have hS : MemLp (fun ω => ∑ j, (s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 (i, j) *
              (W (s + h) ω j - W s ω j) +
            (s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 (i, j) -
              s₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 (i, j)) * cellZeta W s h j ω)) 2 P := by
      refine memLp_finsetSum _ fun j _ => ?_
      refine (memLp_two_bdd_mul (as1 _) (fun ω => sb _ _) (hξ j)).add ?_
      exact memLp_two_bdd_mul ((as2 _).sub (as1 _))
        (fun ω => (abs_sub _ _).trans (add_le_add (sb _ _) (sb _ _))) (hζ j)
    have hD : MemLp (fun ω => (h : ℝ) / 2 * (b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 i +
              b₁ (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 i)) 2 P :=
      MemLp.of_bound (((ab1 i).add (ab2 i)).const_mul _) ((h : ℝ) / 2 * (S + S))
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (bb _ _) (bb _ _)))
            (by positivity))
    exact (ih.2 i).add (hS.add hD)

theorem integrable_norm_sq_of_coords [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → SDEState d}
    (hf : ∀ i, MemLp (fun ω => f ω i) 2 P) : Integrable (fun ω => ‖f ω‖ ^ 2) P := by
  simp_rw [state_norm_sq]
  exact integrable_finsetSum _ fun i _ => (hf i).integrable_sq

theorem memLp_coords_of_near [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f g : Ω → SDEState d} {K : ℝ} (hg : ∀ i, MemLp (fun ω => g ω i) 2 P)
    (hf : ∀ i, AEStronglyMeasurable (fun ω => f ω i) P) (hK : ∀ ω, ‖f ω - g ω‖ ≤ K) (i : Fin d) :
    MemLp (fun ω => f ω i) 2 P := by
  have e : (fun ω => f ω i) = fun ω => g ω i + (f ω i - g ω i) := funext fun ω => by ring
  rw [e]
  refine (hg i).add (MemLp.of_bound ((hf i).sub (hg i).1) K (ae_of_all _ fun ω => ?_))
  rw [Real.norm_eq_abs]
  have : f ω i - g ω i = (f ω - g ω) i := rfl
  rw [this]; exact (coord_abs_le_state _ i).trans (hK ω)

theorem sq_step_bound {h L p q v : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 ≤ L) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hv : v ≤ h / 2 * (L * (p + q))) (hv0 : 0 ≤ v) :
    (q + v) ^ 2 ≤ (1 + h) * q ^ 2 + h * L ^ 2 * (p ^ 2 + q ^ 2) := by
  have h0 : (q + v) ^ 2 ≤ (q + h / 2 * (L * (p + q))) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg hq hv0) (add_le_add le_rfl hv) 2
  have e : (1 + h) * q ^ 2 + h * L ^ 2 * (p ^ 2 + q ^ 2) - (q + h / 2 * (L * (p + q))) ^ 2 =
      h * (q - L * (p + q) / 2) ^ 2 + h * (1 - h) * (L * (p + q)) ^ 2 / 4 +
        h * (L * (p - q)) ^ 2 / 2 := by ring
  have hnn : 0 ≤ h * (q - L * (p + q) / 2) ^ 2 + h * (1 - h) * (L * (p + q)) ^ 2 / 4 +
      h * (L * (p - q)) ^ 2 / 2 :=
    add_nonneg (add_nonneg (mul_nonneg hh.le (sq_nonneg _))
      (div_nonneg (mul_nonneg (mul_nonneg hh.le (sub_nonneg.2 hh1)) (sq_nonneg _)) (by norm_num)))
      (div_nonneg (mul_nonneg hh.le (sq_nonneg _)) (by norm_num))
  rw [← e] at hnn
  exact h0.trans (sub_nonneg.1 hnn)

set_option maxHeartbeats 1000000 in
/-- One cell of the discrete L² stability of the scheme in its initial pair. -/
theorem euler_diff_step [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁) {S L : ℝ}
    (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (a y a' y' : SDEState d) (k : ℕ) :
    ∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y (k + 1)).2 -
        (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' (k + 1)).2‖ ^ 2 ∂P ≤
      (1 + (1 + 2 * L ^ 2 + 12 * d * L ^ 2) * h) *
        max (∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).1‖ ^ 2 ∂P)
          (∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2‖ ^ 2 ∂P) := by
  set s : ℝ≥0 := ((k : ℝ) * h).toNNReal with hsdef
  set Z1 : Ω → SDEState d := fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 with hZ1
  set Z2 : Ω → SDEState d := fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 with hZ2
  set Z1' : Ω → SDEState d := fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).1 with hZ1'
  set Z2' : Ω → SDEState d := fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2 with hZ2'
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hGm : Monotone (completedBrownianPast P W (fun _ => x₀)) :=
    fun s t hst => completedBrownianPast_mono P W _ hst
  obtain ⟨m1, m2⟩ := eulerZZ_meas_G hG hGm hW.2.1 hh hs hb a y k
  obtain ⟨m1', m2'⟩ := eulerZZ_meas_G hG hGm hW.2.1 hh hs hb a' y' k
  obtain ⟨L1, L2⟩ := eulerZZ_memLp hW x₀ hh hs hb hSg a y k
  obtain ⟨L1', L2'⟩ := eulerZZ_memLp hW x₀ hh hs hb hSg a' y' k
  have hS : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  set D : Ω → SDEState d := fun ω => (Z2 ω - Z2' ω) +
    ((h : ℝ) / 2) • ((b₁ (Z1 ω) + b₁ (Z2 ω)) - (b₁ (Z1' ω) + b₁ (Z2' ω))) with hD
  set A : Ω → SDEDiffusion d := fun ω => s₁ (Z1 ω) - s₁ (Z1' ω) with hA
  set B : Ω → SDEDiffusion d := fun ω => (s₁ (Z2 ω) - s₁ (Z1 ω)) - (s₁ (Z2' ω) - s₁ (Z1' ω))
    with hB
  have heq : ∀ ω, (eulerZZ s₁ b₁ h (fun s => W s ω) a y (k + 1)).2 -
      (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' (k + 1)).2 = D ω + cellNoise W s h A B ω := by
    intro ω
    simp only [eulerZZ]
    rw [cellInc_eq ω (hW.2.1 ω) hh, cellInc_eq ω (hW.2.1 ω) hh]
    ext i
    simp only [hD, hA, hB, cellNoise, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hsum : (∑ j, (s₁ (Z1 ω) (i, j) * (W (s + h) ω j - W s ω j) +
          (s₁ (Z2 ω) (i, j) - s₁ (Z1 ω) (i, j)) * cellZeta W s h j ω)) -
        (∑ j, (s₁ (Z1' ω) (i, j) * (W (s + h) ω j - W s ω j) +
          (s₁ (Z2' ω) (i, j) - s₁ (Z1' ω) (i, j)) * cellZeta W s h j ω)) =
        ∑ j, ((s₁ (Z1 ω) (i, j) - s₁ (Z1' ω) (i, j)) * (W (s + h) ω j - W s ω j) +
          (s₁ (Z2 ω) (i, j) - s₁ (Z1 ω) (i, j) - (s₁ (Z2' ω) (i, j) - s₁ (Z1' ω) (i, j))) *
            cellZeta W s h j ω) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    linear_combination hsum
  have hDm : Measurable[completedBrownianPast P W (fun _ => x₀) s] D := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
    have hg : Measurable fun ω => b₁ (Z1 ω) + b₁ (Z2 ω) - (b₁ (Z1' ω) + b₁ (Z2' ω)) :=
      ((hb.measurable.comp m1).add (hb.measurable.comp m2)).sub
        ((hb.measurable.comp m1').add (hb.measurable.comp m2'))
    have hg2 : Measurable fun ω => ((h : ℝ) / 2) • (b₁ (Z1 ω) + b₁ (Z2 ω) - (b₁ (Z1' ω) + b₁ (Z2' ω))) :=
      hg.const_smul ((h : ℝ) / 2)
    exact (m2.sub m2').add hg2
  have hAm : Measurable[completedBrownianPast P W (fun _ => x₀) s] A := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
    exact (hs.measurable.comp m1).sub (hs.measurable.comp m1')
  have hBm : Measurable[completedBrownianPast P W (fun _ => x₀) s] B := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
    exact ((hs.measurable.comp m2).sub (hs.measurable.comp m1)).sub
      ((hs.measurable.comp m2').sub (hs.measurable.comp m1'))
  have hDc : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => D ω i := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hDm
  have hAc : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p := fun p =>
    (EuclideanSpace.proj p).continuous.measurable.comp hAm
  have hBc : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p := fun p =>
    (EuclideanSpace.proj p).continuous.measurable.comp hBm
  have hAK : ∀ ω, ‖A ω‖ ≤ 4 * S := fun ω =>
    (norm_sub_le _ _).trans (by linarith [(hSg (Z1 ω)).1, (hSg (Z1' ω)).1])
  have hBK : ∀ ω, ‖B ω‖ ≤ 4 * S := fun ω =>
    ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))).trans
      (by linarith [(hSg (Z1 ω)).1, (hSg (Z1' ω)).1, (hSg (Z2 ω)).1, (hSg (Z2' ω)).1])
  have hg' : ∀ ω, ‖(b₁ (Z1 ω) + b₁ (Z2 ω)) - (b₁ (Z1' ω) + b₁ (Z2' ω))‖ ≤
      L * (‖Z1 ω - Z1' ω‖ + ‖Z2 ω - Z2' ω‖) := fun ω => by
    have e : (b₁ (Z1 ω) + b₁ (Z2 ω)) - (b₁ (Z1' ω) + b₁ (Z2' ω)) =
        (b₁ (Z1 ω) - b₁ (Z1' ω)) + (b₁ (Z2 ω) - b₁ (Z2' ω)) := by abel
    rw [e, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hLg _ _).2 (hLg _ _).2)
  have hv : ∀ ω, ‖((h : ℝ) / 2) • ((b₁ (Z1 ω) + b₁ (Z2 ω)) - (b₁ (Z1' ω) + b₁ (Z2' ω)))‖ ≤
      (h : ℝ) / 2 * (L * (‖Z1 ω - Z1' ω‖ + ‖Z2 ω - Z2' ω‖)) := fun ω => by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hg' ω) (by positivity)
  have hgS : ∀ ω, ‖((h : ℝ) / 2) • ((b₁ (Z1 ω) + b₁ (Z2 ω)) - (b₁ (Z1' ω) + b₁ (Z2' ω)))‖ ≤
      (h : ℝ) / 2 * (4 * S) := fun ω => by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) (norm_add_le _ _))).trans ?_) (by positivity)
    linarith [(hSg (Z1 ω)).2, (hSg (Z1' ω)).2, (hSg (Z2 ω)).2, (hSg (Z2' ω)).2]
  have hDL : ∀ i, MemLp (fun ω => D ω i) 2 P := fun i =>
    memLp_coords_of_near (g := fun ω => Z2 ω - Z2' ω) (fun i => (L2 i).sub (L2' i))
      (fun i => aestronglyMeasurable_of_completedPast hW x₀ s (hDc i))
      (fun ω => by rw [hD]; simp only [add_sub_cancel_left]; exact hgS ω) i
  have step := cellNoise_step hW x₀ s h hh (D := D) (A := A) (B := B) (K := 4 * S)
    hDc hDL hAc hBc hAK hBK
  have pD : ∀ ω, ‖D ω‖ ^ 2 ≤ (1 + h) * ‖Z2 ω - Z2' ω‖ ^ 2 +
      h * L ^ 2 * (‖Z1 ω - Z1' ω‖ ^ 2 + ‖Z2 ω - Z2' ω‖ ^ 2) := fun ω =>
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
      (sq_step_bound hh hh1 hL (norm_nonneg _) (norm_nonneg _) (hv ω) (norm_nonneg _))
  have pAB : ∀ ω, ‖A ω‖ ^ 2 + ‖B ω‖ ^ 2 ≤
      3 * L ^ 2 * (‖Z1 ω - Z1' ω‖ ^ 2 + ‖Z2 ω - Z2' ω‖ ^ 2) := fun ω => by
    have hA' : ‖A ω‖ ≤ L * ‖Z1 ω - Z1' ω‖ := (hLg _ _).1
    have hB' : ‖B ω‖ ≤ L * ‖Z2 ω - Z2' ω‖ + L * ‖Z1 ω - Z1' ω‖ := by
      have e : B ω = (s₁ (Z2 ω) - s₁ (Z2' ω)) - (s₁ (Z1 ω) - s₁ (Z1' ω)) := by rw [hB]; abel
      rw [e]; exact (norm_sub_le _ _).trans (add_le_add (hLg _ _).1 (hLg _ _).1)
    have a2 := pow_le_pow_left₀ (norm_nonneg _) hA' 2
    have b2 := pow_le_pow_left₀ (norm_nonneg _) hB' 2
    linarith only [a2, b2, sq_nonneg (L * ‖Z2 ω - Z2' ω‖ - L * ‖Z1 ω - Z1' ω‖),
      sq_nonneg (L * ‖Z2 ω - Z2' ω‖)]
  have Ip : Integrable (fun ω => ‖Z1 ω - Z1' ω‖ ^ 2) P :=
    integrable_norm_sq_of_coords fun i => (L1 i).sub (L1' i)
  have Iq : Integrable (fun ω => ‖Z2 ω - Z2' ω‖ ^ 2) P :=
    integrable_norm_sq_of_coords fun i => (L2 i).sub (L2' i)
  have Ipq : Integrable (fun ω => ‖Z1 ω - Z1' ω‖ ^ 2 + ‖Z2 ω - Z2' ω‖ ^ 2) P := Ip.add Iq
  set m1 := ∫ ω, ‖Z1 ω - Z1' ω‖ ^ 2 ∂P with hm1
  set m2 := ∫ ω, ‖Z2 ω - Z2' ω‖ ^ 2 ∂P with hm2
  have e1 : ∫ ω, ((1 + h) * ‖Z2 ω - Z2' ω‖ ^ 2 +
      h * L ^ 2 * (‖Z1 ω - Z1' ω‖ ^ 2 + ‖Z2 ω - Z2' ω‖ ^ 2)) ∂P =
      (1 + h) * m2 + h * L ^ 2 * (m1 + m2) := by
    rw [integral_add (Iq.const_mul _) (Ipq.const_mul _), integral_const_mul,
      integral_const_mul, integral_add Ip Iq]
  have e2 : ∫ ω, 3 * L ^ 2 * (‖Z1 ω - Z1' ω‖ ^ 2 + ‖Z2 ω - Z2' ω‖ ^ 2) ∂P =
      3 * L ^ 2 * (m1 + m2) := by
    rw [integral_const_mul, integral_add Ip Iq]
  have i1 : ∫ ω, ‖D ω‖ ^ 2 ∂P ≤ (1 + h) * m2 + h * L ^ 2 * (m1 + m2) := by
    rw [← e1]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
      ((Iq.const_mul _).add (Ipq.const_mul _)) (ae_of_all _ pD)
  have i2 : ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P ≤ 3 * L ^ 2 * (m1 + m2) := by
    rw [← e2]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
      (Ipq.const_mul _) (ae_of_all _ pAB)
  have hm1n : 0 ≤ m1 := integral_nonneg fun ω => sq_nonneg _
  have hm2n : 0 ≤ m2 := integral_nonneg fun ω => sq_nonneg _
  have hM1 : m1 ≤ max m1 m2 := le_max_left _ _
  have hM2 : m2 ≤ max m1 m2 := le_max_right _ _
  have hlhs : ∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y (k + 1)).2 -
      (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' (k + 1)).2‖ ^ 2 ∂P =
      ∫ ω, ‖D ω + cellNoise W s h A B ω‖ ^ 2 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [heq ω])
  rw [hlhs]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hhL : 0 ≤ (h : ℝ) * L ^ 2 := by positivity
  have k1 : (1 + (h : ℝ)) * m2 ≤ (1 + h) * max m1 m2 := mul_le_mul_of_nonneg_left hM2 (by positivity)
  have k2 : (h : ℝ) * L ^ 2 * (m1 + m2) ≤ h * L ^ 2 * (2 * max m1 m2) :=
    mul_le_mul_of_nonneg_left (by linarith) hhL
  have k3 : 2 * d * (h : ℝ) * (3 * L ^ 2 * (m1 + m2)) ≤ 2 * d * h * (3 * L ^ 2 * (2 * max m1 m2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      (by positivity)
  have k4 : 2 * d * (h : ℝ) * ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P ≤
      2 * d * h * (3 * L ^ 2 * (m1 + m2)) := mul_le_mul_of_nonneg_left i2 (by positivity)
  linarith only [step, i1, k1, k2, k3, k4]

/-- Discrete L² stability of the scheme in its initial pair (`b5`). -/
theorem euler_stab [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁) {S L : ℝ}
    (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (a y a' y' : SDEState d) (k : ℕ) :
    max (∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).1‖ ^ 2 ∂P)
        (∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2‖ ^ 2 ∂P) ≤
      (1 + (1 + 2 * L ^ 2 + 12 * d * L ^ 2) * h) ^ k * max (‖a - a'‖ ^ 2) (‖y - y'‖ ^ 2) := by
  set C : ℝ := 1 + 2 * L ^ 2 + 12 * d * L ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  induction k with
  | zero => simp [eulerZZ]
  | succ k ih =>
    have hstep := euler_diff_step hW x₀ hh hh1 hs hb hL hSg hLg a y a' y' k
    have hfst : ∀ ω, (eulerZZ s₁ b₁ h (fun s => W s ω) a y (k + 1)).1 -
        (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' (k + 1)).1 =
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 -
        (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2 := fun ω => rfl
    simp only [hfst]
    set M := max (∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).1‖ ^ 2 ∂P)
        (∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2‖ ^ 2 ∂P) with hM
    have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (le_max_left _ _)
    have h1 : 1 ≤ 1 + C * h := le_add_of_nonneg_right (mul_nonneg hC0 (NNReal.coe_nonneg h))
    have hA : ∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 -
        (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2‖ ^ 2 ∂P ≤ (1 + C * h) * M :=
      (le_max_right _ _).trans (le_mul_of_one_le_left hM0 h1)
    rw [pow_succ, mul_comm _ (1 + C * h), mul_assoc]
    exact max_le (hA.trans (mul_le_mul_of_nonneg_left ih (zero_le_one.trans h1)))
      (hstep.trans (mul_le_mul_of_nonneg_left ih (zero_le_one.trans h1)))

theorem euler_stab_exp [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁) {S L : ℝ}
    (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (a y a' y' : SDEState d) (k : ℕ) :
    ∫ ω, ‖(eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 -
            (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2‖ ^ 2 ∂P ≤
      Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * (k * h)) * max (‖a - a'‖ ^ 2) (‖y - y'‖ ^ 2) := by
  refine (le_max_right _ _).trans ((euler_stab hW x₀ hh hh1 hs hb hL hSg hLg a y a' y' k).trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ ((sq_nonneg _).trans (le_max_left _ _))
  have hx : 0 ≤ (1 + 2 * L ^ 2 + 12 * d * L ^ 2) * (h : ℝ) := by positivity
  calc (1 + (1 + 2 * L ^ 2 + 12 * d * L ^ 2) * h) ^ k
      ≤ Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * h) ^ k := by
        refine pow_le_pow_left₀ (by linarith) ?_ k
        have := Real.add_one_le_exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * (h : ℝ)); linarith
    _ = Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * (k * h)) := by
        rw [← Real.exp_nat_mul]; ring_nf

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

/-- Noise of one cell: `(ξ, ζ)`. -/
abbrev Noise (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ)

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

/-- One step of the scheme in noise form. -/
noncomputable def zstep (p : SDEState d × SDEState d) (n : Noise d) : SDEState d :=
  p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * n.1 j +
    (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * n.2 j) + h / 2 * (b₁ p.1 i + b₁ p.2 i))

/-- The scheme as a recursion on pairs driven by a noise sequence. -/
noncomputable def zrec (N : ℕ → Noise d) : ℕ → SDEState d × SDEState d → SDEState d × SDEState d
  | 0, p => p
  | k + 1, p => ((zrec N k p).2, zstep s₁ b₁ h (zrec N k p) (N k))

variable {s₁ b₁ h}

theorem zstep_continuous (hs : Continuous s₁) (hb : Continuous b₁) :
    Continuous fun q : (SDEState d × SDEState d) × Noise d => zstep s₁ b₁ h q.1 q.2 := by
  have hp1 : Continuous fun q : (SDEState d × SDEState d) × Noise d => q.1.1 :=
    continuous_fst.comp continuous_fst
  have hp2 : Continuous fun q : (SDEState d × SDEState d) × Noise d => q.1.2 :=
    continuous_snd.comp continuous_fst
  have hsc : ∀ p : Fin d × Fin d, ∀ {g : (SDEState d × SDEState d) × Noise d → SDEState d},
      Continuous g → Continuous fun q => s₁ (g q) p := fun p g hg =>
    (EuclideanSpace.proj p).continuous.comp (hs.comp hg)
  have hbc : ∀ i : Fin d, ∀ {g : (SDEState d × SDEState d) × Noise d → SDEState d},
      Continuous g → Continuous fun q => b₁ (g q) i := fun i g hg =>
    (EuclideanSpace.proj i).continuous.comp (hb.comp hg)
  have hn1 : ∀ j : Fin d, Continuous fun q : (SDEState d × SDEState d) × Noise d => q.2.1 j :=
    fun j => (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  have hn2 : ∀ j : Fin d, Continuous fun q : (SDEState d × SDEState d) × Noise d => q.2.2 j :=
    fun j => (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  refine hp2.add ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_))
  refine (continuous_finsetSum _ fun j _ => ?_).add
    (continuous_const.mul ((hbc i hp1).add (hbc i hp2)))
  have e1 : Continuous fun q : (SDEState d × SDEState d) × Noise d => s₁ q.1.1 (i, j) :=
    hsc (i, j) hp1
  have e2 : Continuous fun q : (SDEState d × SDEState d) × Noise d => s₁ q.1.2 (i, j) :=
    hsc (i, j) hp2
  exact (e1.mul (hn1 j)).add ((e2.sub e1).mul (hn2 j))

theorem zrec_continuous (hs : Continuous s₁) (hb : Continuous b₁) (k : ℕ) :
    Continuous fun q : (ℕ → Noise d) × (SDEState d × SDEState d) => zrec s₁ b₁ h q.1 k q.2 := by
  induction k with
  | zero => exact continuous_snd
  | succ k ih =>
    show Continuous fun q : (ℕ → Noise d) × (SDEState d × SDEState d) =>
      ((zrec s₁ b₁ h q.1 k q.2).2, zstep s₁ b₁ h (zrec s₁ b₁ h q.1 k q.2) (q.1 k))
    exact ih.snd.prodMk ((zstep_continuous hs hb).comp
      (ih.prodMk ((continuous_apply k).comp continuous_fst)))

theorem zrec_congr {N N' : ℕ → Noise d} (k : ℕ) (hN : ∀ l < k, N l = N' l)
    (p : SDEState d × SDEState d) : zrec s₁ b₁ h N k p = zrec s₁ b₁ h N' k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun l hl => hN l (Nat.lt_succ_of_lt hl)
    show ((zrec s₁ b₁ h N k p).2, zstep s₁ b₁ h (zrec s₁ b₁ h N k p) (N k)) =
      ((zrec s₁ b₁ h N' k p).2, zstep s₁ b₁ h (zrec s₁ b₁ h N' k p) (N' k))
    rw [ih', hN k (Nat.lt_succ_self k)]

/-- Extension of a finite noise block by zeros. -/
noncomputable def extN {k : ℕ} (v : Fin k → Noise d) (l : ℕ) : Noise d :=
  if hl : l < k then v ⟨l, hl⟩ else 0

theorem extN_continuous (k : ℕ) : Continuous fun v : Fin k → Noise d => extN v := by
  refine continuous_pi fun l => ?_
  unfold extN
  by_cases hl : l < k
  · simp only [hl, dite_true]; exact continuous_apply _
  · simp only [hl, dite_false]; exact continuous_const

theorem zrec_extN (N : ℕ → Noise d) (k : ℕ) (p : SDEState d × SDEState d) :
    zrec s₁ b₁ h N k p = zrec s₁ b₁ h (extN fun l : Fin k => N l) k p :=
  zrec_congr k (fun l hl => by simp [extN, hl]) p

/-- Noises of the cells `m, m+1, ...` of the scheme driven by `W`. -/
noncomputable def noiseAt (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (m : ℕ) (ω : Ω) (l : ℕ) : Noise d :=
  (fun j => W ((((m + l : ℕ) : ℝ) * h).toNNReal + h) ω j - W (((m + l : ℕ) : ℝ) * h).toNNReal ω j,
    fun j => cellZeta W (((m + l : ℕ) : ℝ) * h).toNNReal h j ω)

theorem eulerZZ_eq_zrec {W : ℝ≥0 → Ω → SDEState d} (ω : Ω) (hWc : Continuous fun s => W s ω)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (a y : SDEState d) (m k : ℕ) :
    eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k) =
      zrec s₁ b₁ h (noiseAt W h m ω) k (eulerZZ s₁ b₁ h (fun s => W s ω) a y m) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2,
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2 +
          cellInc s₁ b₁ h (fun s => W s ω) (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).1
            (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2 (m + k) h) = _
    rw [cellInc_eq ω hWc hh, ih]
    rfl

theorem futBrownian_mono [MeasurableSpace Ω] (W : ℝ≥0 → Ω → SDEState d) {s s' : ℝ≥0}
    (hss : s ≤ s') : futBrownian W s' ≤ futBrownian W s := by
  refine Measurable.comap_le ?_
  refine @measurable_pi_lambda Ω _ _ (futBrownian W s) _ _ fun p => ?_
  have e : (fun ω => W (s' + p.1) ω p.2 - W s' ω p.2) = fun ω =>
      (W (s + (s' - s + p.1)) ω p.2 - W s ω p.2) - (W (s + (s' - s)) ω p.2 - W s ω p.2) := by
    funext ω; rw [← add_assoc, add_tsub_cancel_of_le hss]; ring
  rw [e]
  exact (incr_meas_fut W s _ p.2).sub (incr_meas_fut W s _ p.2)

theorem noiseAt_meas_fut [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    (hWc : ∀ ω, Continuous fun s => W s ω) (h : ℝ≥0) (m l : ℕ) :
    Measurable[futBrownian W ((m : ℝ) * h).toNNReal] fun ω => noiseAt W h m ω l := by
  set t₀ : ℝ≥0 := ((m : ℝ) * h).toNNReal
  set sl : ℝ≥0 := (((m + l : ℕ) : ℝ) * h).toNNReal
  have hle : t₀ ≤ sl := Real.toNNReal_le_toNNReal (by
    push_cast; nlinarith [NNReal.coe_nonneg h, (Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
  have hmono := futBrownian_mono W hle
  refine Measurable.prodMk ?_ ?_
  · refine @measurable_pi_lambda Ω _ _ (futBrownian W t₀) _ _ fun j => ?_
    have e : (fun ω => W (sl + h) ω j - W sl ω j) = fun ω => W (sl + h) ω j - W sl ω j := rfl
    exact (incr_meas_fut W sl h j).mono hmono le_rfl
  · refine @measurable_pi_lambda Ω _ _ (futBrownian W t₀) _ _ fun j => ?_
    exact (zeta_meas_fut hWc sl h j).mono hmono le_rfl

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

theorem integral_indep_fubini [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {V : Ω → β}
    (hU : Measurable U) (hV : Measurable V) (hind : IndepFun U V P) {F : α → β → ℝ}
    (hF : Measurable (Function.uncurry F)) {K : ℝ} (hK : ∀ a b, |F a b| ≤ K) :
    ∫ ω, F (U ω) (V ω) ∂P = ∫ ω, (∫ ω', F (U ω) (V ω') ∂P) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hind
  have h1 : ∫ ω, F (U ω) (V ω) ∂P =
      ∫ z, Function.uncurry F z ∂(P.map fun ω => (U ω, V ω)) := by
    rw [integral_map (hU.prodMk hV).aemeasurable hF.aestronglyMeasurable]; rfl
  have hint : Integrable (Function.uncurry F) ((P.map U).prod (P.map V)) :=
    memLp_one_iff_integrable.1 (MemLp.of_bound hF.aestronglyMeasurable K
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hK z.1 z.2))
  rw [h1, hmap, integral_prod _ hint]
  have hin : ∀ u, ∫ v, Function.uncurry F (u, v) ∂(P.map V) = ∫ ω', F u (V ω') ∂P := fun u => by
    have hFu : AEStronglyMeasurable (fun v => Function.uncurry F (u, v)) (P.map V) :=
      (hF.comp measurable_prodMk_left).aestronglyMeasurable
    rw [integral_map hV.aemeasurable hFu]; rfl
  simp_rw [hin]
  have hsm : StronglyMeasurable fun u => ∫ v, Function.uncurry F (u, v) ∂(P.map V) :=
    hF.stronglyMeasurable.integral_prod_right'
  simp_rw [hin] at hsm
  rw [integral_map hU.aemeasurable hsm.aestronglyMeasurable]

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem euler_restart [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hs : Continuous s₁) (hb : Continuous b₁) {f : SDEState d → ℝ}
    (hf : Measurable f) {K : ℝ} (hfK : ∀ x, |f x| ≤ K) (a y : SDEState d) (m k : ℕ) :
    ∫ ω, f (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2 ∂P =
      ∫ ω, (∫ ω', f (zrec s₁ b₁ h (noiseAt W h m ω') k
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y m)).2 ∂P) ∂P := by
  set t₀ : ℝ≥0 := ((m : ℝ) * h).toNNReal with ht₀
  set U : Ω → SDEState d × SDEState d := fun ω => eulerZZ s₁ b₁ h (fun s => W s ω) a y m with hUdef
  set V : Ω → (Fin k → Noise d) := fun ω l => noiseAt W h m ω l with hVdef
  set F : SDEState d × SDEState d → (Fin k → Noise d) → ℝ :=
    fun u v => f (zrec s₁ b₁ h (extN v) k u).2 with hFdef
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hGm : Monotone (completedBrownianPast P W (fun _ => x₀)) :=
    fun s t hst => completedBrownianPast_mono P W _ hst
  have hG' : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[(fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) t]
      fun ω => W r ω j :=
    fun r _ _ j => (EuclideanSpace.proj j).continuous.measurable.comp (hW.1 r)
  obtain ⟨p1, p2⟩ := eulerZZ_meas_G hG hGm hW.2.1 hh hs hb a y m
  obtain ⟨a1, a2⟩ := eulerZZ_meas_G hG' monotone_const hW.2.1 hh hs hb a y m
  have hUp : Measurable[completedBrownianPast P W (fun _ => x₀) t₀] U := p1.prodMk p2
  have hU : Measurable U := a1.prodMk a2
  have hVf : Measurable[futBrownian W t₀] V :=
    @measurable_pi_lambda Ω _ _ (futBrownian W t₀) _ _ fun l => noiseAt_meas_fut hW.2.1 h m l
  have hV : Measurable V := hVf.mono (futBrownian_le hW t₀) le_rfl
  have hind : IndepFun U V P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left
      (stdBrownian_indep_completedPast hW x₀ t₀) hUp.comap_le) hVf.comap_le
  have hFm : Measurable (Function.uncurry F) := by
    have hz : Continuous fun q : (SDEState d × SDEState d) × (Fin k → Noise d) =>
        zrec s₁ b₁ h (extN q.2) k q.1 :=
      (zrec_continuous hs hb k).comp (((extN_continuous k).comp continuous_snd).prodMk
        continuous_fst)
    exact hf.comp hz.snd.measurable
  have hK : ∀ u v, |F u v| ≤ K := fun u v => hfK _
  have key := integral_indep_fubini hU hV hind hFm hK
  have e1 : (fun ω => f (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2) =
      fun ω => F (U ω) (V ω) := funext fun ω => by
    simp only [hFdef, hUdef, hVdef]; rw [eulerZZ_eq_zrec ω (hW.2.1 ω) hh, zrec_extN]
  rw [e1, key]
  congr 1; funext ω; congr 1; funext ω'
  simp only [hFdef, hVdef]; rw [← zrec_extN]

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

/-- Brownian motion restarted at `t₀`. -/
def shiftBM (W : ℝ≥0 → Ω → SDEState d) (t₀ : ℝ≥0) : ℝ≥0 → Ω → SDEState d :=
  fun t ω => W (t₀ + t) ω - W t₀ ω

theorem shiftBM_std {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) :
    IsStandardBrownian P (shiftBM W t₀) := by
  refine ⟨fun t => (hW.1 _).sub (hW.1 _), fun ω =>
    ((hW.2.1 ω).comp (continuous_const.add continuous_id)).sub continuous_const,
    fun i => (hW.2.2.1 i).shift t₀, ?_⟩
  exact hW.2.2.2.comp (fun _ (x : ℝ≥0 → ℝ) t => x (t₀ + t) - x t₀)
    (fun _ => measurable_pi_lambda _ fun t => (measurable_pi_apply _).sub (measurable_pi_apply _))

theorem noiseAt_shift (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (m : ℕ) (ω : Ω) (l : ℕ) :
    noiseAt W h m ω l = noiseAt (shiftBM W ((m : ℝ) * h).toNNReal) h 0 ω l := by
  have hsl : (((m + l : ℕ) : ℝ) * h).toNNReal =
      ((m : ℝ) * h).toNNReal + (((0 + l : ℕ) : ℝ) * h).toNNReal := by
    rw [zero_add, Nat.cast_add, add_mul, Real.toNNReal_add (by positivity) (by positivity)]
  unfold noiseAt
  rw [hsl]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp only [shiftBM, PiLp.sub_apply, add_assoc, sub_sub_sub_cancel_right]
  · simp only [cellZeta, zetaF, shiftBM, PiLp.sub_apply, add_assoc, sub_sub_sub_cancel_right]

/-- Any two standard Brownian motions have the same finite-dimensional laws. -/
theorem stdBM_fd_law [IsProbabilityMeasure P] {W W' : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (hW' : IsStandardBrownian P W') {ι : Type*} [Fintype ι]
    (T : ι → ℝ≥0) :
    P.map (fun ω (j : Fin d) (q : ι) => W (T q) ω j) =
      P.map (fun ω (j : Fin d) (q : ι) => W' (T q) ω j) := by
  classical
  set I : Finset ℝ≥0 := Finset.univ.image T with hI
  set g : (I → ℝ) → (ι → ℝ) := fun x q => x ⟨T q, Finset.mem_image_of_mem T (Finset.mem_univ q)⟩
    with hgdef
  have hg : Measurable g := measurable_pi_lambda _ fun q => measurable_pi_apply _
  have key : ∀ {V : ℝ≥0 → Ω → SDEState d}, IsStandardBrownian P V →
      P.map (fun ω (j : Fin d) (q : ι) => V (T q) ω j) =
        Measure.pi (fun _ : Fin d => (BrownianReal.projectiveFamily I).map g) := by
    intro V hV
    have hm : ∀ j, Measurable fun ω (q : ι) => V (T q) ω j := fun j =>
      measurable_pi_lambda _ fun q => stdBrownian_coord_measurable hV _ _
    have hind : iIndepFun (fun j ω (q : ι) => V (T q) ω j) P :=
      hV.2.2.2.comp (fun _ (x : ℝ≥0 → ℝ) (q : ι) => x (T q))
        (fun _ => measurable_pi_lambda _ fun q => measurable_pi_apply _)
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun j => (hm j).aemeasurable).1 hind]
    congr 1; funext j
    have hl := ((hV.2.2.1 j).hasLaw I).map_eq
    have hr : Measurable fun ω => I.restrict (fun t => V t ω j) :=
      measurable_pi_lambda _ fun i => stdBrownian_coord_measurable hV _ _
    have e : (fun ω (q : ι) => V (T q) ω j) = g ∘ (fun ω => I.restrict (fun t => V t ω j)) := rfl
    rw [e, ← Measure.map_map hg hr, hl]
  rw [key hW, key hW']

/-- The first `k` cell noises. -/
noncomputable def noiseV (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (k : ℕ) (ω : Ω) : Fin k → Noise d :=
  fun l => noiseAt W h 0 ω l

/-- Sampling times of the `n`-th approximation of the first `k` noises. -/
noncomputable def apxT (h : ℝ≥0) (k n : ℕ) (q : Fin k × Option (Fin (2 ^ n))) : ℝ≥0 :=
  (((0 + (q.1 : ℕ) : ℕ) : ℝ) * h).toNNReal + q.2.elim h fun r => dyTime h n r

/-- The `n`-th approximation of the noises from the sampled values (Riemann sums for `ζ`). -/
noncomputable def apxPsi (h : ℝ≥0) (k n : ℕ) (x : Fin d → Fin k × Option (Fin (2 ^ n)) → ℝ) :
    Fin k → Noise d :=
  fun l => (fun j => x j (l, none) - x j (l, some ⟨0, Nat.two_pow_pos n⟩),
    fun j => (1 / (h : ℝ)) * ((∑ r : Fin (2 ^ n), (x j (l, none) - x j (l, some r))) *
      ((h / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)))

theorem apxPsi_continuous (h : ℝ≥0) (k n : ℕ) :
    Continuous fun x : Fin d → Fin k × Option (Fin (2 ^ n)) → ℝ => apxPsi h k n x := by
  have hc : ∀ (j : Fin d) (q : Fin k × Option (Fin (2 ^ n))),
      Continuous fun x : Fin d → Fin k × Option (Fin (2 ^ n)) → ℝ => x j q :=
    fun j q => (continuous_apply q).comp (continuous_apply j)
  refine continuous_pi fun l => Continuous.prodMk (continuous_pi fun j => ?_)
    (continuous_pi fun j => ?_)
  · exact (hc j _).sub (hc j _)
  · exact continuous_const.mul ((continuous_finsetSum _ fun r _ => (hc j _).sub (hc j _)).mul
      continuous_const)

theorem apx_tendsto {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (h : ℝ≥0) (k : ℕ) (ω : Ω) :
    Tendsto (fun n => apxPsi h k n (fun j q => W (apxT h k n q) ω j)) atTop
      (𝓝 (noiseV W h k ω)) := by
  refine tendsto_pi_nhds.2 fun l => Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun j => ?_)
    (tendsto_pi_nhds.2 fun j => ?_)
  · refine tendsto_const_nhds.congr fun n => ?_
    simp [apxPsi, apxT, noiseV, noiseAt, dyTime]
  · set sl : ℝ≥0 := (((0 + (l : ℕ) : ℕ) : ℝ) * h).toNNReal with hsl
    have hH : ∀ ω, Continuous fun u : ℝ≥0 => W (sl + h) ω j - W (sl + u) ω j := fun ω =>
      continuous_const.sub ((EuclideanSpace.proj j).continuous.comp
        ((hWc ω).comp (continuous_const.add continuous_id)))
    have hR := (riemann_tendsto hH h ω).const_mul (1 / (h : ℝ))
    refine hR.congr' (Eventually.of_forall fun n => ?_) |>.trans (le_of_eq ?_)
    · simp only [apxPsi, apxT, Option.elim]
      rw [Fin.sum_univ_eq_sum_range (fun r => W (sl + h) ω j - W (sl + dyTime h n r) ω j)]
    · simp [noiseV, noiseAt, cellZeta, zetaF, hsl]

theorem noiseV_measurable {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0)
    (k : ℕ) : Measurable (noiseV W h k) :=
  measurable_pi_lambda _ fun l =>
    (noiseAt_meas_fut hW.2.1 h 0 l).mono (futBrownian_le hW _) le_rfl

/-- The first `k` cell noises of any two standard Brownian motions have the same law. -/
theorem noiseV_law [IsProbabilityMeasure P] {W W' : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (hW' : IsStandardBrownian P W') (h : ℝ≥0) (k : ℕ) :
    P.map (noiseV W h k) = P.map (noiseV W' h k) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun Φ => ?_
  rw [integral_map (noiseV_measurable hW h k).aemeasurable Φ.continuous.aestronglyMeasurable,
    integral_map (noiseV_measurable hW' h k).aemeasurable Φ.continuous.aestronglyMeasurable]
  have lim : ∀ {V : ℝ≥0 → Ω → SDEState d}, IsStandardBrownian P V →
      Tendsto (fun n => ∫ ω, Φ (apxPsi h k n (fun j q => V (apxT h k n q) ω j)) ∂P) atTop
        (𝓝 (∫ ω, Φ (noiseV V h k ω) ∂P)) := by
    intro V hV
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖Φ‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => Φ.norm_coe_le_norm _)
      (Eventually.of_forall fun ω => (Φ.continuous.tendsto _).comp (apx_tendsto hV.2.1 h k ω))
    have hm : Measurable fun ω (j : Fin d) (q : Fin k × Option (Fin (2 ^ n))) =>
        V (apxT h k n q) ω j :=
      measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun q =>
        stdBrownian_coord_measurable hV _ _
    exact (Φ.continuous.comp (apxPsi_continuous h k n)).measurable.comp hm |>.aestronglyMeasurable
  have heq : ∀ n, ∫ ω, Φ (apxPsi h k n (fun j q => W (apxT h k n q) ω j)) ∂P =
      ∫ ω, Φ (apxPsi h k n (fun j q => W' (apxT h k n q) ω j)) ∂P := fun n => by
    have hc := (Φ.continuous.comp (apxPsi_continuous h k n (d := d))).aestronglyMeasurable
      (μ := P.map fun ω (j : Fin d) (q : Fin k × Option (Fin (2 ^ n))) => W (apxT h k n q) ω j)
    have hm : ∀ {V : ℝ≥0 → Ω → SDEState d}, IsStandardBrownian P V →
        Measurable fun ω (j : Fin d) (q : Fin k × Option (Fin (2 ^ n))) =>
          V (apxT h k n q) ω j := fun hV =>
      measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun q =>
        stdBrownian_coord_measurable hV _ _
    have e1 := integral_map (hm hW).aemeasurable hc
    rw [stdBM_fd_law hW hW' (apxT h k n)] at hc e1
    rw [integral_map (hm hW').aemeasurable hc] at e1
    exact e1.symm
  exact tendsto_nhds_unique ((lim hW).congr heq) (lim hW')

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem euler_restart_law [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0} (hh : 0 < (h : ℝ))
    (hs : Continuous s₁) (hb : Continuous b₁) {f : SDEState d → ℝ} (hf : Measurable f) {K : ℝ}
    (hfK : ∀ x, |f x| ≤ K) (a y : SDEState d) (m k : ℕ) :
    ∫ ω, f (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2 ∂P =
      ∫ ω, (∫ ω', f (eulerZZ s₁ b₁ h (fun s => W s ω')
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y m).1
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y m).2 k).2 ∂P) ∂P := by
  rw [euler_restart hW x₀ hh hs hb hf hfK a y m k]
  congr 1; funext ω
  set p := eulerZZ s₁ b₁ h (fun s => W s ω) a y m with hp
  set W'' := shiftBM W ((m : ℝ) * h).toNNReal with hW''
  set Fp : (Fin k → Noise d) → ℝ := fun v => f (zrec s₁ b₁ h (extN v) k p).2 with hFp
  have hFm : Measurable Fp := by
    have hz : Continuous fun v : Fin k → Noise d => zrec s₁ b₁ h (extN v) k p :=
      (zrec_continuous hs hb k).comp ((extN_continuous k).prodMk continuous_const)
    exact hf.comp hz.snd.measurable
  have e1 : (fun ω' => f (zrec s₁ b₁ h (noiseAt W h m ω') k p).2) =
      fun ω' => Fp (noiseV W'' h k ω') := funext fun ω' => by
    have hv : (fun l : Fin k => noiseAt W h m ω' l) = noiseV W'' h k ω' :=
      funext fun l => noiseAt_shift W h m ω' l
    simp only [hFp]
    rw [zrec_extN, hv]
  have e2 : (fun ω' => f (eulerZZ s₁ b₁ h (fun s => W s ω') p.1 p.2 k).2) =
      fun ω' => Fp (noiseV W h k ω') := funext fun ω' => by
    have := eulerZZ_eq_zrec (s₁ := s₁) (b₁ := b₁) ω' (hW.2.1 ω') hh p.1 p.2 0 k
    rw [zero_add] at this
    simp only [hFp]
    rw [this, zrec_extN]
    rfl
  rw [e1, e2, ← integral_map (noiseV_measurable (shiftBM_std hW _) h k).aemeasurable
      hFm.aestronglyMeasurable,
    ← integral_map (noiseV_measurable hW h k).aemeasurable hFm.aestronglyMeasurable,
    noiseV_law (shiftBM_std hW _) hW h k]

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

theorem integral_le_sqrt_sq [IsProbabilityMeasure P] {g : Ω → ℝ} (hg : MemLp g 2 P) :
    ∫ ω, g ω ∂P ≤ Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hv := variance_nonneg g P
  rw [variance_eq_sub hg] at hv
  simp only [Pi.pow_apply] at hv
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

theorem euler_G_lip [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁) {S L : ℝ}
    (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K) (hLf : 0 ≤ Lf)
    (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) (a y a' y' : SDEState d) (k : ℕ) :
    |∫ ω, f (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 ∂P -
        ∫ ω, f (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2 ∂P| ≤
      Lf * Real.sqrt (Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * (k * h)) *
        max (‖a - a'‖ ^ 2) (‖y - y'‖ ^ 2)) := by
  set Z : Ω → SDEState d := fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 with hZ
  set Z' : Ω → SDEState d := fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a' y' k).2 with hZ'
  have hG' : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[(fun _ : ℝ≥0 => ‹MeasurableSpace Ω›) t]
      fun ω => W r ω j :=
    fun r _ _ j => (EuclideanSpace.proj j).continuous.measurable.comp (hW.1 r)
  have mZ : Measurable Z := (eulerZZ_meas_G hG' monotone_const hW.2.1 hh hs hb a y k).2
  have mZ' : Measurable Z' := (eulerZZ_meas_G hG' monotone_const hW.2.1 hh hs hb a' y' k).2
  have iF : ∀ {V : Ω → SDEState d}, Measurable V → Integrable (fun ω => f (V ω)) P := fun hV =>
    memLp_one_iff_integrable.1 (MemLp.of_bound (hf.comp hV).aestronglyMeasurable K
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfK _))
  have hsq : Integrable (fun ω => ‖Z ω - Z' ω‖ ^ 2) P :=
    integrable_norm_sq_of_coords fun i =>
      ((eulerZZ_memLp hW x₀ hh hs hb hSg a y k).2 i).sub ((eulerZZ_memLp hW x₀ hh hs hb hSg a' y' k).2 i)
  have hn : MemLp (fun ω => ‖Z ω - Z' ω‖) 2 P :=
    (memLp_two_iff_integrable_sq (continuous_norm.measurable.comp (mZ.sub mZ')).aestronglyMeasurable).2 hsq
  rw [← integral_sub (iF mZ) (iF mZ')]
  calc |∫ ω, (f (Z ω) - f (Z' ω)) ∂P| ≤ ∫ ω, |f (Z ω) - f (Z' ω)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, Lf * ‖Z ω - Z' ω‖ ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
          ((hn.integrable one_le_two).const_mul _) (ae_of_all _ fun ω => hfL _ _)
    _ = Lf * ∫ ω, ‖Z ω - Z' ω‖ ∂P := integral_const_mul _ _
    _ ≤ Lf * Real.sqrt (∫ ω, ‖Z ω - Z' ω‖ ^ 2 ∂P) :=
        mul_le_mul_of_nonneg_left (integral_le_sqrt_sq hn) hLf
    _ ≤ _ := by
        gcongr
        exact euler_stab_exp hW x₀ hh hh1 hs hb hL hSg hLg a y a' y' k

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

variable [MeasurableSpace Ω]

theorem stay_eq {X : ℝ≥0 → Ω → SDEState d} (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0)
    (R : ℝ) :
    {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R} = ⋂ q : ℚ, {ω | ‖X (min (q : ℝ).toNNReal T) ω‖ ≤ R} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · exact fun H q => H _ (min_le_right _ _)
  · intro H s hs
    have hg : Continuous fun r : ℝ => ‖X (min r.toNNReal T) ω‖ :=
      continuous_norm.comp ((hc ω).comp (continuous_real_toNNReal.min continuous_const))
    have hcl : IsClosed {r : ℝ | ‖X (min r.toNNReal T) ω‖ ≤ R} := isClosed_le hg continuous_const
    have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {r : ℝ | ‖X (min r.toNNReal T) ω‖ ≤ R} := by
      rintro _ ⟨q, rfl⟩; exact H q
    have := hcl.closure_subset_iff.2 hsub (hd.closure_eq ▸ Set.mem_univ (s : ℝ))
    simpa [Real.toNNReal_coe, min_eq_left hs] using this

theorem stay_measurableSet {X : ℝ≥0 → Ω → SDEState d} (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0) (R : ℝ) :
    MeasurableSet {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R} := by
  rw [stay_eq hc T R]
  exact MeasurableSet.iInter fun q =>
    measurableSet_le (continuous_norm.measurable.comp (hm _)) measurable_const

theorem exit_tendsto {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → SDEState d}
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0) :
    Tendsto (fun R : ℕ => P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ) atTop (𝓝 0) := by
  have hmono : Antitone fun R : ℕ => {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ := by
    intro R R' hR
    refine Set.compl_subset_compl.2 fun ω hω s hs => (hω s hs).trans (by exact_mod_cast hR)
  have hemp : ⋂ R : ℕ, {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    rw [Set.mem_iInter] at hω
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hc ω).continuousOn
    obtain ⟨R, hR⟩ := exists_nat_ge C
    exact hω R fun s hs => (hC s ⟨zero_le, hs⟩).trans hR
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun R : ℕ => (stay_measurableSet hm hc T (R : ℝ)).compl.nullMeasurableSet) hmono
    ⟨0, measure_ne_top _ _⟩
  rwa [hemp, measure_empty] at this

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
  exact EthierKurtz.euler_scheme_approx hW x₀ hσ hb hX hs₁ hb₁ hR hL hSg hLg hag hpos hlim T j hj φ hΛ
    hφK hφL hη (fun n ω k => eulerZZ s₁ b₁ (hn n) (fun s => W s ω) x₀ x₀ k) (fun n ω => rfl) (fun n ω k => rfl)
end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

theorem ck_limit {P : Measure Ω} [IsProbabilityMeasure P] {v : Ω → ℝ} (hv : Measurable v)
    {u : ℕ → ℕ → Ω → ℝ} (hu : ∀ R n, Measurable (u R n)) {K : ℝ} (hvK : ∀ ω, |v ω| ≤ K)
    (huK : ∀ R n ω, |u R n ω| ≤ K) {a : ℝ} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (h1 : ∀ R, ∀ η > 0, ∀ᶠ n in atTop, |a - ∫ ω, u R n ω ∂P| ≤ c R + η)
    (h2 : ∀ᵐ ω ∂P, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ R, ∀ η > 0, ∀ᶠ n in atTop, |v ω - u R n ω| ≤ e R + η) :
    a = ∫ ω, v ω ∂P := by
  set D : ℕ → Ω → ℝ≥0∞ := fun R ω => limsup (fun n => ENNReal.ofReal |v ω - u R n ω|) atTop
    with hD
  have mF : ∀ R n, Measurable fun ω => ENNReal.ofReal |v ω - u R n ω| := fun R n =>
    ENNReal.measurable_ofReal.comp (hv.sub (hu R n)).abs
  have mD : ∀ R, Measurable (D R) := fun R => Measurable.limsup fun n => mF R n
  have hFK : ∀ R n ω, ENNReal.ofReal |v ω - u R n ω| ≤ ENNReal.ofReal (2 * K) := fun R n ω =>
    ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans (by linarith only [hvK ω, huK R n ω]))
  have hDK : ∀ R ω, D R ω ≤ ENNReal.ofReal (2 * K) := fun R ω =>
    limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => hFK R n ω)
  have hD0 : ∀ᵐ ω ∂P, Tendsto (fun R => D R ω) atTop (𝓝 0) := by
    filter_upwards [h2] with ω ⟨e, he, H⟩
    have hle : ∀ R, D R ω ≤ ENNReal.ofReal (e R) := fun R => by
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [H R η hη] with n hn
      calc ENNReal.ofReal |v ω - u R n ω| ≤ ENNReal.ofReal (e R + η) := ENNReal.ofReal_le_ofReal hn
        _ ≤ ENNReal.ofReal (e R) + ENNReal.ofReal η := ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (e R) + η := by rw [ENNReal.ofReal_coe_nnreal]
    have he' : Tendsto (fun R => ENNReal.ofReal (e R)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp he
      rw [ENNReal.ofReal_zero] at this; exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he' (fun R => bot_le) hle
  have hfin : ∫⁻ _ : Ω, ENNReal.ofReal (2 * K) ∂P ≠ ∞ := by
    rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hDint : Tendsto (fun R => ∫⁻ ω, D R ω ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (2 * K)) mD
      (fun R => ae_of_all _ (hDK R)) hfin hD0
    simpa using this
  have hfat : ∀ R, limsup (fun n => ∫⁻ ω, ENNReal.ofReal |v ω - u R n ω| ∂P) atTop ≤
      ∫⁻ ω, D R ω ∂P := fun R =>
    limsup_lintegral_le (fun _ => ENNReal.ofReal (2 * K)) (fun n => mF R n)
      (fun n => ae_of_all _ (hFK R n)) hfin
  have iB : ∀ {f : Ω → ℝ}, Measurable f → (∀ ω, |f ω| ≤ K) → Integrable f P := fun hf hfK =>
    memLp_one_iff_integrable.1 (MemLp.of_bound hf.aestronglyMeasurable K
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfK ω))
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hη : 0 < ε / 3 := by positivity
  obtain ⟨R, hR1, hR2⟩ := ((hc.eventually (ge_mem_nhds hη)).and
    (hDint.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη)))).exists
  have hev := eventually_lt_of_limsup_lt ((hfat R).trans_lt hR2)
  obtain ⟨n, hn1, hn2⟩ := ((h1 R (ε / 3) hη).and hev).exists
  have hint : ∫ ω, |v ω - u R n ω| ∂P ≤ ε / 3 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => abs_nonneg _)
      (f := fun ω => |v ω - u R n ω|) (hv.sub (hu R n)).abs.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hη.le hn2.le
  have hdiff : |∫ ω, u R n ω ∂P - ∫ ω, v ω ∂P| ≤ ε / 3 := by
    rw [← integral_sub (iB (hu R n) (huK R n)) (iB hv hvK)]
    calc |∫ ω, (u R n ω - v ω) ∂P| ≤ ∫ ω, |u R n ω - v ω| ∂P := abs_integral_le_integral_abs
      _ = ∫ ω, |v ω - u R n ω| ∂P := by congr 1; funext ω; exact abs_sub_comm _ _
      _ ≤ ε / 3 := hint
  rw [Real.dist_eq]
  calc |a - ∫ ω, v ω ∂P| ≤ |a - ∫ ω, u R n ω ∂P| + |∫ ω, u R n ω ∂P - ∫ ω, v ω ∂P| :=
        abs_sub_le _ _ _
    _ ≤ ε := by linarith

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

theorem limsup_near {u : ℕ → ℝ} {K c e : ℝ} (hK : ∀ n, |u n| ≤ K)
    (h : ∀ η > 0, ∀ᶠ n in atTop, |u n - c| ≤ e + η) : |limsup u atTop - c| ≤ e := by
  have hb : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of ⟨K, fun n => (abs_le.1 (hK n)).2⟩
  have hcb : IsCoboundedUnder (· ≤ ·) atTop u :=
    isCoboundedUnder_le_of_le atTop fun n => (abs_le.1 (hK n)).1
  rw [abs_le]; constructor
  · refine le_of_forall_pos_le_add fun η hη => ?_
    have : c - e - η ≤ limsup u atTop := le_limsup_of_frequently_le
      ((h η hη).mono fun n hn => by linarith [(abs_le.1 hn).1]).frequently hb
    linarith
  · refine le_of_forall_pos_le_add fun η hη => ?_
    have : limsup u atTop ≤ c + e + η :=
      limsup_le_of_le hcb ((h η hη).mono fun n hn => by linarith [(abs_le.1 hn).2])
    linarith

variable [MeasurableSpace Ω]

/-- The restart function `G(a, y) = E f(Z_k)` of the Euler scheme started from `(a, y)`. -/
noncomputable def eulerG (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (f : SDEState d → ℝ)
    (h : ℝ) (k : ℕ) (a y : SDEState d) : ℝ :=
  ∫ ω, f (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 ∂P

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem eulerG_bound [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    {f : SDEState d → ℝ} {K : ℝ} (hfK : ∀ x, |f x| ≤ K) (h : ℝ) (k : ℕ) (a y : SDEState d) :
    |eulerG P W s₁ b₁ f h k a y| ≤ K := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfK _)).trans ?_
  simp

theorem eulerG_lip [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁) {S L : ℝ}
    (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K) (hLf : 0 ≤ Lf)
    (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) {k : ℕ} {t : ℝ} (hkt : (k : ℝ) * h ≤ t)
    (a y a' y' : SDEState d) :
    |eulerG P W s₁ b₁ f h k a y - eulerG P W s₁ b₁ f h k a' y'| ≤
      Lf * Real.sqrt (Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * t)) *
        (‖a - a'‖ + ‖y - y'‖) := by
  refine (euler_G_lip hW 0 hh hh1 hs hb hL hSg hLg hf hfK hLf hfL a y a' y' k).trans ?_
  have hC : 0 ≤ 1 + 2 * L ^ 2 + 12 * d * L ^ 2 := by positivity
  rw [Real.sqrt_mul (Real.exp_pos _).le]
  have h2 : Real.sqrt (Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * (k * h))) ≤
      Real.sqrt (Real.exp ((1 + 2 * L ^ 2 + 12 * d * L ^ 2) * t)) :=
    Real.sqrt_le_sqrt (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hkt hC))
  have h3 : Real.sqrt (max (‖a - a'‖ ^ 2) (‖y - y'‖ ^ 2)) ≤ ‖a - a'‖ + ‖y - y'‖ := by
    have hM : max (‖a - a'‖ ^ 2) (‖y - y'‖ ^ 2) ≤ (‖a - a'‖ + ‖y - y'‖) ^ 2 :=
      max_le (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _)) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) 2)
    exact (Real.sqrt_le_sqrt hM).trans (Real.sqrt_sq (by positivity)).le
  exact (mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    hLf).trans_eq (by ring)

theorem eulerG_cont [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁) {S L : ℝ}
    (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K) (hLf : 0 ≤ Lf)
    (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) (k : ℕ) :
    Continuous fun p : SDEState d × SDEState d => eulerG P W s₁ b₁ f h k p.1 p.2 :=
  cont_of_lip2 (by positivity)
    (eulerG_lip hW hh hh1 hs hb hL hSg hLg hf hfK hLf hfL (t := (k : ℝ) * h) le_rfl)

theorem g_apx [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (y : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) X)
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {f : SDEState d → ℝ} {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K) (hLf : 0 ≤ Lf)
    (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) (t : ℝ≥0)
    {hn : ℕ → ℝ} (hpos : ∀ n, 0 < hn n) (hle : ∀ n, hn n ≤ t) (hlim : Tendsto hn atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, |eulerG P W s₁ b₁ f (hn n) ⌊(t : ℝ) / hn n⌋₊ y y - ∫ ω, f (X t ω) ∂P| ≤
      2 * K * (P {ω | ∀ s ≤ t, ‖X s ω‖ ≤ R}ᶜ).toReal + η := by
  have hj : ∀ n, 1 ≤ ⌊(t : ℝ) / hn n⌋₊ ∧ (⌊(t : ℝ) / hn n⌋₊ : ℝ) * hn n ≤ t ∧
      (t : ℝ) ≤ ⌊(t : ℝ) / hn n⌋₊ * hn n + hn n := fun n => by
    have hm := floor_mem_cell (hpos n) t.2
    refine ⟨Nat.le_floor ?_, hm.1, by have := hm.2; rw [add_mul, one_mul] at this; exact this⟩
    rw [Nat.cast_one, le_div_iff₀ (hpos n), one_mul]; exact hle n
  have := euler_apx hW y hσ hb hX hs₁ hb₁ hR hL hSg hLg hag hpos hlim t
    (fun n => ⌊(t : ℝ) / hn n⌋₊) hj (fun _ _ z => f z) hLf (fun _ _ z => hfK z)
    (fun _ a z a' z' => (hfL z z').trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hLf)) hη
  filter_upwards [this] with n hn
  exact hn

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

theorem mesh_seq {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ hN : ℕ → ℝ≥0, (∀ n, (hN n : ℝ) = c / (n + N + 1)) ∧ (∀ n, 0 < (hN n : ℝ)) ∧
      (∀ n, (hN n : ℝ) ≤ c / (N + 1)) ∧ Tendsto (fun n => (hN n : ℝ)) atTop (𝓝 0) := by
  have he : ∀ n : ℕ, ((Real.toNNReal (c / (n + N + 1)) : ℝ≥0) : ℝ) = c / (n + N + 1) :=
    fun n => Real.coe_toNNReal _ (by positivity)
  refine ⟨fun n => Real.toNNReal (c / (n + N + 1)), he, fun n => by rw [he]; positivity,
    fun n => by rw [he]; gcongr; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], ?_⟩
  have := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat (N + 1))
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, he]
  push_cast; ring_nf

theorem exitR_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → SDEState d}
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0) (c : ℝ) :
    Tendsto (fun R : ℕ => c * (P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ).toReal) atTop (𝓝 0) := by
  have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (exit_tendsto (P := P) hm hc T)).const_mul c
  simpa using this

theorem limsup_abs_le {u : ℕ → ℝ} {K : ℝ} (hK : ∀ n, |u n| ≤ K) : |limsup u atTop| ≤ K := by
  have := limsup_near (c := 0) (e := K) hK fun η hη =>
    Eventually.of_forall fun n => by rw [sub_zero]; linarith [hK n]
  rwa [sub_zero] at this

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem markov_core [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d) (S L : ℕ → ℝ)
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL : ∀ R, 0 ≤ L R)
    (hSg : ∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R)
    (hLg : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖)
    (hag : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {D : Set (SDEState d)} {X : SDEState d → ℝ≥0 → Ω → SDEState d}
    (hX : ∀ y ∈ D, SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) (X y))
    (t : ℝ≥0) {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K)
    (hLf : 0 ≤ Lf) (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) :
    ∃ g : SDEState d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ K) ∧
      (∀ y ∈ D, g y = ∫ ω, f (X y t ω) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∫ ω, f (X x (s + t) ω) ∂P = ∫ ω, g (X x s ω) ∂P := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hfK 0)
  have hX0 : ∀ y ∈ D, ∀ {φ : SDEState d → ℝ}, ∫ ω, φ (X y 0 ω) ∂P = φ y := fun y hy φ => by
    rw [integral_congr_ae ((hX y hy).2.2.2.1.mono fun ω hω => by
      show φ (X y 0 ω) = (fun _ => φ y) ω; rw [hω])]
    simp
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    refine ⟨f, hf, hfK, fun y hy => (hX0 y hy).symm, fun x hx s _ => by rw [add_zero]⟩
  have htr : 0 < (t : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  set C : ℕ → ℝ := fun R => 1 + 2 * L R ^ 2 + 12 * d * L R ^ 2 with hCdef
  -- the measurable version g̃
  obtain ⟨hg, hg_eq, hg_pos, hg_le, hg_lim⟩ := mesh_seq (lt_min htr one_pos) 0
  have hg_le' : ∀ n, (hg n : ℝ) ≤ min (t : ℝ) 1 := fun n =>
    (hg_le n).trans (by rw [Nat.cast_zero, zero_add, div_one])
  set gR : ℕ → ℕ → SDEState d → ℝ := fun R n y =>
    eulerG P W (s₁ R) (b₁ R) f (hg n) ⌊(t : ℝ) / hg n⌋₊ y y with hgR
  have mgR : ∀ R n, Measurable (gR R n) := fun R n =>
    (eulerG_cont hW (hg_pos n) ((hg_le' n).trans (min_le_right _ _)) (hs₁ R) (hb₁ R) (hL R)
      (hSg R) (hLg R) hf hfK hLf hfL _).measurable.comp (measurable_id.prodMk measurable_id)
  set gt : SDEState d → ℝ := fun y => limsup (fun R => limsup (fun n => gR R n y) atTop) atTop
    with hgt
  have mgt : Measurable gt := Measurable.limsup fun R => Measurable.limsup fun n => mgR R n
  have gRK : ∀ R n y, |gR R n y| ≤ K := fun R n y => eulerG_bound hfK _ _ _ _
  have gtK : ∀ y, |gt y| ≤ K := fun y =>
    limsup_abs_le fun R => limsup_abs_le fun n => gRK R n y
  -- approximation at a point of `D`, for any admissible mesh
  have happ : ∀ y ∈ D, ∀ (R : ℕ) {hn : ℕ → ℝ≥0}, (∀ n, 0 < (hn n : ℝ)) → (∀ n, (hn n : ℝ) ≤ t) →
      Tendsto (fun n => (hn n : ℝ)) atTop (𝓝 0) → ∀ η > 0, ∀ᶠ n in atTop,
        |eulerG P W (s₁ R) (b₁ R) f (hn n) ⌊(t : ℝ) / hn n⌋₊ y y - ∫ ω, f (X y t ω) ∂P| ≤
          2 * K * (P {ω | ∀ s ≤ t, ‖X y s ω‖ ≤ (R : ℝ)}ᶜ).toReal + η :=
    fun y hy R hn hpos hle hlim η hη =>
      g_apx (hn := fun n => (hn n : ℝ)) hW y hσ hb (hX y hy) (hs₁ R) (hb₁ R) (Nat.cast_nonneg R)
        (hL R) (hSg R) (hLg R) (hag R) hfK hLf hfL t hpos hle hlim hη
  have hgtD : ∀ y ∈ D, gt y = ∫ ω, f (X y t ω) ∂P := fun y hy => by
    have hR : ∀ R : ℕ, |limsup (fun n => gR R n y) atTop - ∫ ω, f (X y t ω) ∂P| ≤
        2 * K * (P {ω | ∀ s ≤ t, ‖X y s ω‖ ≤ (R : ℝ)}ᶜ).toReal := fun R =>
      limsup_near (fun n => gRK R n y) (happ y hy R hg_pos
        (fun n => (hg_le' n).trans (min_le_left _ _)) hg_lim)
    have hT : Tendsto (fun R => limsup (fun n => gR R n y) atTop) atTop
        (𝓝 (∫ ω, f (X y t ω) ∂P)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun R => dist_nonneg) (fun R => by rw [Real.dist_eq]; exact hR R)
        (exitR_tendsto (P := P) (hX y hy).1 (hX y hy).2.1 t (2 * K))
    exact hT.limsup_eq
  refine ⟨gt, mgt, gtK, hgtD, fun x hx s hD => ?_⟩
  have hXx := hX x hx
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    rw [zero_add, hX0 x hx (φ := gt), hgtD x hx]
  have hsr : 0 < (s : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  -- the restart mesh: `s` is a grid point
  set N : ℕ := ⌈(s : ℝ) / min (t : ℝ) 1⌉₊ with hN
  obtain ⟨hc, hc_eq, hc_pos, hc_le, hc_lim⟩ := mesh_seq hsr N
  have hmin : 0 < min (t : ℝ) 1 := lt_min htr one_pos
  have hc_le' : ∀ n, (hc n : ℝ) ≤ min (t : ℝ) 1 := fun n => (hc_le n).trans (by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (s : ℝ) / min (t : ℝ) 1 ≤ N := Nat.le_ceil _
    rw [div_le_iff₀ hmin] at h1
    linarith only [h1, hmin])
  have hc_t : ∀ n, (hc n : ℝ) ≤ t := fun n => (hc_le' n).trans (min_le_left _ _)
  have hc_1 : ∀ n, (hc n : ℝ) ≤ 1 := fun n => (hc_le' n).trans (min_le_right _ _)
  set m : ℕ → ℕ := fun n => n + N + 1 with hm
  have hms : ∀ n, (m n : ℝ) * hc n = s := fun n => by
    rw [hc_eq n]; simp only [hm]; push_cast
    field_simp
  set k : ℕ → ℕ := fun n => ⌊(t : ℝ) / hc n⌋₊ with hk
  have hkc : ∀ n, (k n : ℝ) * hc n ≤ t ∧ (t : ℝ) ≤ k n * hc n + hc n := fun n => by
    have hmc := floor_mem_cell (hc_pos n) t.2
    exact ⟨hmc.1, by have := hmc.2; rw [add_mul, one_mul] at this; exact this⟩
  have mXs : Measurable (X x s) := hXx.1 s
  refine ck_limit (u := fun R n ω => eulerG P W (s₁ R) (b₁ R) f (hc n) (k n) (X x s ω) (X x s ω))
    (mgt.comp mXs) (fun R n => (eulerG_cont hW (hc_pos n) (hc_1 n) (hs₁ R) (hb₁ R) (hL R)
      (hSg R) (hLg R) hf hfK hLf hfL _).measurable.comp (mXs.prodMk mXs))
    (fun ω => gtK _) (fun R n ω => eulerG_bound hfK _ _ _ _)
    (exitR_tendsto (P := P) hXx.1 hXx.2.1 (s + t) (4 * K)) ?_ ?_
  · -- the CK chain at fixed truncation
    intro R η hη
    have hjA : ∀ n, 1 ≤ m n + k n ∧ ((m n + k n : ℕ) : ℝ) * hc n ≤ ((s + t : ℝ≥0) : ℝ) ∧
        ((s + t : ℝ≥0) : ℝ) ≤ ((m n + k n : ℕ) : ℝ) * hc n + hc n := fun n => by
      refine ⟨by simp only [hm]; omega, ?_, ?_⟩
      · push_cast; rw [add_mul, hms n]; linarith [(hkc n).1]
      · push_cast; rw [add_mul, hms n]; linarith [(hkc n).2]
    have hA := euler_apx (hn := fun n => (hc n : ℝ)) hW x hσ hb hXx (hs₁ R) (hb₁ R)
      (Nat.cast_nonneg R) (hL R) (hSg R) (hLg R) (hag R) hc_pos hc_lim (s + t)
      (fun n => m n + k n) hjA (fun _ _ z => f z) hLf (fun _ _ z => hfK z)
      (fun _ a z a' z' => (hfL z z').trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hLf)) (half_pos hη)
    have hjB : ∀ n, 1 ≤ m n ∧ (m n : ℝ) * hc n ≤ s ∧ (s : ℝ) ≤ m n * hc n + hc n := fun n =>
      ⟨by simp only [hm]; omega, (hms n).le, by rw [hms n]; linarith [hc_pos n]⟩
    have hB := euler_apx (hn := fun n => (hc n : ℝ)) hW x hσ hb hXx (hs₁ R) (hb₁ R)
      (Nat.cast_nonneg R) (hL R) (hSg R) (hLg R) (hag R) hc_pos hc_lim s m hjB
      (fun n a z => eulerG P W (s₁ R) (b₁ R) f (hc n) (k n) a z)
      (Λ := Lf * Real.sqrt (Real.exp (C R * t))) (by positivity)
      (fun n a z => eulerG_bound hfK _ _ _ _)
      (fun n => eulerG_lip hW (hc_pos n) (hc_1 n) (hs₁ R) (hb₁ R) (hL R) (hSg R) (hLg R) hf hfK
        hLf hfL (hkc n).1) (half_pos hη)
    filter_upwards [hA, hB] with n hAn hBn
    have hres := euler_restart_law (h := hc n) hW x (hc_pos n) (hs₁ R) (hb₁ R) hf hfK x x (m n) (k n)
    have hsub : P {ω | ∀ u ≤ s, ‖X x u ω‖ ≤ (R : ℝ)}ᶜ ≤ P {ω | ∀ u ≤ s + t, ‖X x u ω‖ ≤ (R : ℝ)}ᶜ :=
      measure_mono (Set.compl_subset_compl.2 fun ω hω u hu => hω u (hu.trans le_self_add))
    have hsub' := ENNReal.toReal_mono (measure_ne_top _ _) hsub
    rw [hres] at hAn
    have e1 : ∀ ω, eulerG P W (s₁ R) (b₁ R) f (hc n) (k n)
        (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).1
        (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).2 =
        ∫ ω', f (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω')
          (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).1
          (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).2 (k n)).2 ∂P := fun ω => rfl
    simp only [e1] at hBn
    rw [abs_sub_comm] at hAn
    calc |∫ ω, f (X x (s + t) ω) ∂P - ∫ ω, eulerG P W (s₁ R) (b₁ R) f (hc n) (k n) (X x s ω)
          (X x s ω) ∂P|
        ≤ |∫ ω, f (X x (s + t) ω) ∂P - ∫ ω, (∫ ω', f (eulerZZ (s₁ R) (b₁ R) (hc n)
            (fun s => W s ω') (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).1
            (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).2 (k n)).2 ∂P) ∂P| +
          |∫ ω, (∫ ω', f (eulerZZ (s₁ R) (b₁ R) (hc n)
            (fun s => W s ω') (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).1
            (eulerZZ (s₁ R) (b₁ R) (hc n) (fun s => W s ω) x x (m n)).2 (k n)).2 ∂P) ∂P -
            ∫ ω, eulerG P W (s₁ R) (b₁ R) f (hc n) (k n) (X x s ω) (X x s ω) ∂P| :=
          abs_sub_le _ _ _
      _ ≤ 4 * K * (P {ω | ∀ u ≤ s + t, ‖X x u ω‖ ≤ (R : ℝ)}ᶜ).toReal + η := by
          have h2K := mul_le_mul_of_nonneg_left hsub' (by linarith only [hK] : (0 : ℝ) ≤ 2 * K)
          linarith only [hAn, hBn, h2K]
  · -- pointwise approximation of g̃ along the restart mesh
    filter_upwards [hD] with ω hω
    refine ⟨fun R => 2 * K * (P {ω' | ∀ u ≤ t, ‖X (X x s ω) u ω'‖ ≤ (R : ℝ)}ᶜ).toReal,
      exitR_tendsto (P := P) (hX _ hω).1 (hX _ hω).2.1 t (2 * K), fun R η hη => ?_⟩
    filter_upwards [happ _ hω R hc_pos hc_t hc_lim η hη] with n hn
    rw [Function.comp_apply, hgtD _ hω, abs_sub_comm]
    exact hn

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
    (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d) (S L : ℕ → ℝ)
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL : ∀ R, 0 ≤ L R)
    (hSg : ∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R)
    (hLg : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖)
    (hag : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {D : Set (SDEState d)} {X : SDEState d → ℝ≥0 → Ω → SDEState d}
    (hX : ∀ y ∈ D, SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) (X y))
    (t : ℝ≥0) {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K)
    (hLf : 0 ≤ Lf) (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) :
    ∃ g : SDEState d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ K) ∧
      (∀ y ∈ D, g y = ∫ ω, f (X y t ω) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∫ ω, f (X x (s + t) ω) ∂P = ∫ ω, g (X x s ω) ∂P := by
  exact ItoLib.markov_core hW hσ hb s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX t hf hfK hLf hfL
