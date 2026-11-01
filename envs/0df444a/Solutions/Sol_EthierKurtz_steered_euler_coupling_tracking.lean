-- Prove2me | solution 1 for EthierKurtz.steered_euler_coupling_tracking
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:20:57.559896+00:00
-- url     : https://prove2.me/submissions/67eda0e8-40e5-4cef-b15f-ac580fa224fc

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
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
    nlinarith
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  linarith

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
    rw [div_le_iff₀ ht]; nlinarith [hu.2]
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith
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
      linarith
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
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
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      nlinarith [pow_pos (two_pos (α := ℝ)) m]
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
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs_ge m])]
      have : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by ring
      have := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith
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
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith
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
  nlinarith [mul_nonneg hε.le ht]

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

variable {s₁ b₁ h w}

end M10b2s


section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

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
  exact Measurable.sub (G := ℝ) (stdBrownian_coord_measurable hW _ _) (stdBrownian_coord_measurable hW _ _)

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
  have h1 : 0 ≤ J - m * I := by linarith
  nlinarith [mul_nonneg hh.le h1]

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
          nlinarith [abs_nonneg (zetaF W s h j u ω), sq_abs (zetaF W s h j u ω)]
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
    nlinarith [sq_nonneg (a i j * ξ j - b i j * ζ j)]
  have e : (D + WithLp.toLp 2 (fun i => ∑ j, (a i j * ξ j + b i j * ζ j))) i =
      D i + ∑ j, (a i j * ξ j + b i j * ζ j) := rfl
  rw [e, ← Finset.mul_sum] at *
  have e2 : ∑ j, (D i * a i j * ξ j + D i * b i j * ζ j) = D i * ∑ j, (a i j * ξ j + b i j * ζ j) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [e2]
  nlinarith [hN]

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
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at this
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
          nlinarith [v4 i j]
        rw [hIT, hS1, hS2, hAB, mul_zero, add_zero]
        have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * d)
        nlinarith [this]

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

/-- Noises of the cells `m, m+1, ...` of the scheme driven by `W`. -/
noncomputable def noiseAt (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (m : ℕ) (ω : Ω) (l : ℕ) : Noise d :=
  (fun j => W ((((m + l : ℕ) : ℝ) * h).toNNReal + h) ω j - W (((m + l : ℕ) : ℝ) * h).toNNReal ω j,
    fun j => cellZeta W (((m + l : ℕ) : ℝ) * h).toNNReal h j ω)

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

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

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



-- ===== F41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41
/-! F41 (eq_4_1 work, 986b9ae0, 2026-10-30): zero coordinates stay zero; per-time face invariance. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end F41
end ItoLib

-- ===== HA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HA (Harris route, s29): abstract Hairer-Mattingly contraction ("Yet another look at Harris'
ergodic theorem", Thm 3.1) in function form. Drift `QV ≤ γ V + K` plus pairwise overlap
`tvDist (Q x) (Q y) ≤ 1 - α` on `{V x + V y ≤ R}` (`R > 2K/(1-γ)`) make `Q` a strict contraction
for the weighted oscillation `|φ x - φ y| ≤ M (2 + β V x + β V y)`. -/

section HA
variable {X : Type*} [MeasurableSpace X]

end HA
end ItoLib

-- ===== F41b =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! F41b (eq_4_1 work, 986b9ae0, 2026-10-30): uniqueness of invariant probability measures from a
local overlap (Doeblin-on-compacts) condition, via the Jordan parts of `μ - ν`. Pure measure theory. -/

section F41b
variable {X : Type*} [MeasurableSpace X]

end F41b
end ItoLib

-- ===== U =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

-- ===== Y =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a


section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12b

end ItoLib

-- ===== Z =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12c

end ItoLib

-- ===== F41c =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41c
/-! F41c (eq_4_1 work, 986b9ae0, 2026-10-30): boundary ergodic measures live on one open face (E5);
invariant measures on one open face are unique given face overlap (E4 concrete); finiteness of M (E6). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end F41c
end ItoLib

-- ===== X41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

end ItoLib

-- ===== F41d =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41d
/-! F41d (eq_4_1 work, 986b9ae0, 2026-10-30): eq_4_1 from the face overlap property. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end F41d
end ItoLib

-- ===== CB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

-- ===== CC =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

-- ===== CD =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

-- ===== CE =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

/-- Average diffusion matrix of a pair applied to `u`. -/
noncomputable def avgApply (p : SDEState d × SDEState d) (u : Fin d → ℝ) : SDEState d :=
  WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * u j)

theorem zstep_shift (p : SDEState d × SDEState d) (n : Noise d) (u : Fin d → ℝ) :
    zstep s₁ b₁ h p (n + (u, fun j => u j / 2)) = zstep s₁ b₁ h p n + avgApply s₁ p u := by
  ext i
  simp only [zstep, avgApply, Prod.fst_add, Prod.snd_add, Pi.add_apply, PiLp.add_apply,
    PiLp.toLp_apply]
  have e : ∀ j, s₁ p.1 (i, j) * (n.1 j + u j) + (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * (n.2 j + u j / 2) =
      (s₁ p.1 (i, j) * n.1 j + (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * n.2 j) +
        (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * u j := fun j => by ring
  simp_rw [e, Finset.sum_add_distrib]
  ring

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

/-- Steering drift at step `l` from the coupled state `q = (X pair, Ŷ pair)`. -/
noncomputable def steer (l : ℕ) (q : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    Fin d → ℝ :=
  if l < m then J q.2 ((1 / ((m : ℝ) - l)) • (q.1.2 - q.2.2)) else 0

/-- One coupled step. -/
noncomputable def cstep (l : ℕ) (q : (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (n : Noise d) : (SDEState d × SDEState d) × (SDEState d × SDEState d) :=
  ((q.1.2, zstep s₁ b₁ h q.1 n),
    (q.2.2, zstep s₁ b₁ h q.2 (n + (steer J m l q, fun j => steer J m l q j / 2))))

/-- The coupled recursion. -/
noncomputable def crec (N : ℕ → Noise d) :
    ℕ → (SDEState d × SDEState d) × (SDEState d × SDEState d) →
      (SDEState d × SDEState d) × (SDEState d × SDEState d)
  | 0, q => q
  | k + 1, q => cstep s₁ b₁ h J m k (crec N k q) (N k)

variable {s₁ b₁ h J m}

theorem crec_congr {N N' : ℕ → Noise d} (k : ℕ) (hN : ∀ l < k, N l = N' l)
    (q : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    crec s₁ b₁ h J m N k q = crec s₁ b₁ h J m N' k q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun l hl => hN l (Nat.lt_succ_of_lt hl)
    show cstep s₁ b₁ h J m k (crec s₁ b₁ h J m N k q) (N k) =
      cstep s₁ b₁ h J m k (crec s₁ b₁ h J m N' k q) (N' k)
    rw [ih', hN k (Nat.lt_succ_self k)]

theorem cstep_steer (hJ : ∀ p v, avgApply s₁ p (J p v) = v) {l : ℕ} (hl : l < m)
    (q : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (n : Noise d) :
    (cstep s₁ b₁ h J m l q n).2.2 =
      zstep s₁ b₁ h q.2 n + (1 / ((m : ℝ) - l)) • (q.1.2 - q.2.2) := by
  simp only [cstep]
  rw [zstep_shift]
  simp only [steer, hl, if_true]
  rw [hJ]

theorem crec_measurable (hs : Continuous s₁) (hb : Continuous b₁)
    (hJ : Measurable (Function.uncurry J)) (k : ℕ)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    Measurable fun N : ℕ → Noise d => crec s₁ b₁ h J m N k q₀ := by
  have hz := (zstep_continuous (s₁ := s₁) (b₁ := b₁) (h := h) hs hb).measurable
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hst : Measurable fun N : ℕ → Noise d => steer J m k (crec s₁ b₁ h J m N k q₀) := by
      unfold steer
      by_cases hk : k < m
      · simp only [hk, if_true]
        have h2 : Measurable fun N : ℕ → Noise d => (crec s₁ b₁ h J m N k q₀).2 :=
          measurable_snd.comp ih
        have h12 : Measurable fun N : ℕ → Noise d => (crec s₁ b₁ h J m N k q₀).1.2 :=
          measurable_snd.comp (measurable_fst.comp ih)
        have h22 : Measurable fun N : ℕ → Noise d => (crec s₁ b₁ h J m N k q₀).2.2 :=
          measurable_snd.comp h2
        exact hJ.comp (h2.prodMk ((h12.sub h22).const_smul (1 / ((m : ℝ) - k))))
      · simp only [hk, if_false]
        exact measurable_const
    have hNk : Measurable fun N : ℕ → Noise d => N k := measurable_pi_apply k
    show Measurable fun N : ℕ → Noise d => cstep s₁ b₁ h J m k (crec s₁ b₁ h J m N k q₀) (N k)
    unfold cstep
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) (Measurable.prodMk ?_ ?_)
    · exact measurable_snd.comp (measurable_fst.comp ih)
    · exact hz.comp ((measurable_fst.comp ih).prodMk hNk)
    · exact measurable_snd.comp (measurable_snd.comp ih)
    · exact hz.comp ((measurable_snd.comp ih).prodMk (hNk.add (hst.prodMk
        (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp hst).div_const _))))

end C4a

end ItoLib

-- ===== CF =====
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

theorem steer_rec {m : ℕ} (hm : 0 < m) {c h G : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (hG : 0 ≤ G)
    (e e' : ℕ → ℝ) (h0 : e 0 ≤ G) (he'0 : e' 0 ≤ G) (he' : ∀ k, e' (k + 1) = e k)
    (hrec : ∀ k, k < m → e (k + 1) ≤ (1 - 1 / ((m : ℝ) - k)) ^ 2 * e k + c * h * (e k + e' k)) :
    ∀ k, k < m → e k ≤ G * (((m : ℝ) - k) / m) ^ 2 * (1 + 13 * c * h) ^ k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hch : 0 ≤ c * h := mul_nonneg hc hh
  set ρ : ℝ := 1 + 13 * c * h with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith
  have hρ0 : 0 ≤ ρ := by linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
      rw [div_self hmR.ne', one_pow, mul_one]
      exact h0
    · have hk' : k < m := by omega
      have hA := ih k (by omega) hk'
      have hB : e' k ≤ G * (((m : ℝ) - k + 1) / m) ^ 2 * ρ ^ k := by
        rcases k with _ | k
        · simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
          have h1 : (1 : ℝ) ≤ (((m : ℝ) + 1) / m) ^ 2 := by
            have : (1 : ℝ) ≤ ((m : ℝ) + 1) / m := by rw [le_div_iff₀ hmR]; linarith
            exact one_le_pow₀ this
          calc e' 0 ≤ G := he'0
            _ = G * 1 := (mul_one G).symm
            _ ≤ G * (((m : ℝ) + 1) / m) ^ 2 := mul_le_mul_of_nonneg_left h1 hG
        · rw [he']
          have hk2 := ih k (by omega) (by omega)
          have e1 : ((m : ℝ) - ((k + 1 : ℕ) : ℝ) + 1) = (m : ℝ) - k := by push_cast; ring
          rw [e1]
          calc e k ≤ G * (((m : ℝ) - k) / m) ^ 2 * ρ ^ k := hk2
            _ ≤ G * (((m : ℝ) - k) / m) ^ 2 * ρ ^ (k + 1) := by
              refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1 (Nat.le_succ k)) ?_
              exact mul_nonneg hG (sq_nonneg _)
      have hkm : ((k : ℝ) + 2) ≤ m := by exact_mod_cast (show k + 2 ≤ m by omega)
      set j : ℝ := (m : ℝ) - k - 1 with hj
      have hj1 : 1 ≤ j := by rw [hj]; linarith
      have hmk : (m : ℝ) - k = j + 1 := by rw [hj]; ring
      have hmk2 : (m : ℝ) - k + 1 = j + 2 := by rw [hj]; ring
      have hmk3 : (m : ℝ) - ((k + 1 : ℕ) : ℝ) = j := by rw [hj]; push_cast; ring
      rw [hmk] at hA
      rw [hmk2] at hB
      rw [hmk3]
      have hrk := hrec k hk'
      rw [hmk] at hrk
      set q : ℝ := (1 - 1 / (j + 1)) ^ 2 with hq
      set a : ℝ := ((j + 1) / m) ^ 2 with ha
      set b : ℝ := ((j + 2) / m) ^ 2 with hb
      have hqa : q * a = (j / m) ^ 2 := by
        rw [hq, ha]
        have : j + 1 ≠ 0 := by linarith
        field_simp
        ring
      have hab : a + b ≤ 13 * (j / m) ^ 2 := by
        rw [ha, hb, div_pow, div_pow, div_pow, ← add_div, mul_div_assoc']
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith only [hj1]
      have key : q * a + c * h * (a + b) ≤ (j / m) ^ 2 * ρ := by
        rw [hqa, hρ]
        linarith only [mul_le_mul_of_nonneg_left hab hch]
      have hGr : 0 ≤ G * ρ ^ k := mul_nonneg hG (pow_nonneg hρ0 k)
      calc e (k + 1) ≤ q * e k + c * h * (e k + e' k) := hrk
        _ ≤ q * (G * a * ρ ^ k) + c * h * (G * a * ρ ^ k + G * b * ρ ^ k) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (sq_nonneg _))
            (mul_le_mul_of_nonneg_left (add_le_add hA hB) hch)
        _ = G * ρ ^ k * (q * a + c * h * (a + b)) := by ring
        _ ≤ G * ρ ^ k * ((j / m) ^ 2 * ρ) := mul_le_mul_of_nonneg_left key hGr
        _ = G * (j / m) ^ 2 * ρ ^ (k + 1) := by ring

theorem steer_rec_last {m : ℕ} (hm : 0 < m) {c h G : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (hG : 0 ≤ G)
    (e e' : ℕ → ℝ) (h0 : e 0 ≤ G) (he'0 : e' 0 ≤ G) (he' : ∀ k, e' (k + 1) = e k)
    (hrec : ∀ k, k < m → e (k + 1) ≤ (1 - 1 / ((m : ℝ) - k)) ^ 2 * e k + c * h * (e k + e' k)) :
    e m ≤ 5 * c * h * G * (1 + 13 * c * h) ^ m / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hch : 0 ≤ c * h := mul_nonneg hc hh
  set ρ : ℝ := 1 + 13 * c * h with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hS := steer_rec hm hc hh hG e e' h0 he'0 he' hrec
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hr := hrec n (by omega)
  have e1 : (1 - 1 / (((n + 1 : ℕ) : ℝ) - n)) = 0 := by push_cast; ring_nf
  rw [e1] at hr
  have hA : e n ≤ G * (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 * ρ ^ n := by
    have := hS n (by omega)
    have e2 : (((n + 1 : ℕ) : ℝ) - n) = 1 := by push_cast; ring
    rwa [e2] at this
  have hB : e' n ≤ G * (2 / ((n + 1 : ℕ) : ℝ)) ^ 2 * ρ ^ n := by
    rcases n with _ | n
    · simp only [Nat.cast_one, zero_add, pow_zero, mul_one]
      norm_num; linarith
    · rw [he']
      have := hS n (by omega)
      have e2 : (((n + 1 + 1 : ℕ) : ℝ) - n) = 2 := by push_cast; ring
      rw [e2] at this
      calc e n ≤ G * (2 / ((n + 1 + 1 : ℕ) : ℝ)) ^ 2 * ρ ^ n := this
        _ ≤ G * (2 / ((n + 1 + 1 : ℕ) : ℝ)) ^ 2 * ρ ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1 (Nat.le_succ n))
            (mul_nonneg hG (sq_nonneg _))
  have hρn : ρ ^ n ≤ ρ ^ (n + 1) := pow_le_pow_right₀ hρ1 (Nat.le_succ n)
  set M : ℝ := ((n + 1 : ℕ) : ℝ) with hM
  have hMp : 0 < M := hmR
  calc e (n + 1) ≤ 0 ^ 2 * e n + c * h * (e n + e' n) := hr
    _ = c * h * (e n + e' n) := by ring
    _ ≤ c * h * (G * (1 / M) ^ 2 * ρ ^ n + G * (2 / M) ^ 2 * ρ ^ n) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hch
    _ = 5 * c * h * G * ρ ^ n / M ^ 2 := by field_simp; ring
    _ ≤ 5 * c * h * G * ρ ^ (n + 1) / M ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : 0 ≤ 5 * c * h * G := by have := mul_nonneg hch hG; linarith
        exact mul_le_mul_of_nonneg_left hρn this

theorem steer_rec_sum {m : ℕ} (hm : 0 < m) {c h G : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (hG : 0 ≤ G)
    (e e' : ℕ → ℝ) (h0 : e 0 ≤ G) (he'0 : e' 0 ≤ G) (he' : ∀ k, e' (k + 1) = e k)
    (hrec : ∀ k, k < m → e (k + 1) ≤ (1 - 1 / ((m : ℝ) - k)) ^ 2 * e k + c * h * (e k + e' k)) :
    ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2 ≤ G * (1 + 13 * c * h) ^ m / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hch : 0 ≤ c * h := mul_nonneg hc hh
  set ρ : ℝ := 1 + 13 * c * h with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith
  have hS := steer_rec hm hc hh hG e e' h0 he'0 he' hrec
  calc ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2
      ≤ ∑ _k ∈ Finset.range m, G * ρ ^ m / (m : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < m := Finset.mem_range.mp hk
        have hpos : (0 : ℝ) < (m : ℝ) - k := by
          have : (k : ℝ) < m := by exact_mod_cast hk'
          linarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : e k * (m : ℝ) ^ 2 ≤ G * ((m : ℝ) - k) ^ 2 * ρ ^ k := by
          have h1a := hS k hk'
          have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
          calc e k * (m : ℝ) ^ 2 ≤ (G * (((m : ℝ) - k) / m) ^ 2 * ρ ^ k) * (m : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right h1a hm2.le
            _ = G * ((m : ℝ) - k) ^ 2 * ρ ^ k := by field_simp
        have h2 : G * ((m : ℝ) - k) ^ 2 * ρ ^ k ≤ G * ((m : ℝ) - k) ^ 2 * ρ ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1 hk'.le)
            (mul_nonneg hG (sq_nonneg _))
        linarith only [h1, h2]
    _ = G * ρ ^ m / m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end ItoLib

-- ===== CG =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

theorem cellZeta_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (s h : ℝ≥0) {t : ℝ≥0} (ht : s + h ≤ t) (j : Fin d) :
    Measurable[G t] (cellZeta W s h j) := by
  have hI := measurable_intervalIntegral_of_continuous (G t)
    (H := fun r ω => W (s + h) ω j - W (s + r) ω j) h
    (fun r hr => (hG _ _ ht j).sub (hG _ _ ((add_le_add le_rfl hr).trans ht) j))
    (fun ω => continuous_const.sub ((EuclideanSpace.proj j).continuous.comp
      ((hWc ω).comp (continuous_const.add continuous_id))))
  unfold cellZeta zetaF
  exact hI.const_mul _

theorem noiseAt_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (h : ℝ≥0) (l : ℕ) {t : ℝ≥0}
    (ht : (((l : ℝ) + 1) * h).toNNReal ≤ t) :
    Measurable[G t] fun ω => noiseAt W h 0 ω l := by
  set sl : ℝ≥0 := (((0 + l : ℕ) : ℝ) * h).toNNReal with hsl
  have e : (((l : ℝ) + 1) * h).toNNReal = sl + h := by
    rw [hsl, show ((l : ℝ) + 1) * h = ((0 + l : ℕ) : ℝ) * h + (h : ℝ) by push_cast; ring,
      Real.toNNReal_add (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg h))
        (NNReal.coe_nonneg h), Real.toNNReal_coe]
  have hsh : sl + h ≤ t := e ▸ ht
  unfold noiseAt
  refine Measurable.prodMk ?_ ?_
  · refine @measurable_pi_lambda Ω _ _ (G t) _ _ fun j => ?_
    exact (hG _ _ hsh j).sub (hG _ _ (le_self_add.trans hsh) j)
  · refine @measurable_pi_lambda Ω _ _ (G t) _ _ fun j => ?_
    exact cellZeta_meas_G hG hWc sl h hsh j

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

theorem crec_noise_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJ : Measurable (Function.uncurry J)) (h : ℝ≥0) (k : ℕ)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    Measurable[G ((k : ℝ) * h).toNNReal]
      fun ω => crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀ := by
  let _ : MeasurableSpace Ω := G ((k : ℝ) * h).toNNReal
  have e : (fun ω => crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀) =
      (fun N => crec s₁ b₁ (h : ℝ) J m N k q₀) ∘
        (fun ω l => if l < k then noiseAt W h 0 ω l else 0) := by
    funext ω
    exact crec_congr k (fun l hl => by simp [hl]) q₀
  rw [e]
  refine (crec_measurable hs hb hJ k q₀).comp (measurable_pi_lambda _ fun l => ?_)
  by_cases hl : l < k
  · simp only [hl, if_true]
    exact noiseAt_meas_G hG hWc h l (Real.toNNReal_le_toNNReal (by
      have : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      nlinarith [h.2]))
  · simp only [hl, if_false]
    exact measurable_const

/-- The one-step identity of the steered difference. -/
theorem crec_diff_succ (hJ : ∀ p v, avgApply s₁ p (J p v) = v) (W : ℝ≥0 → Ω → SDEState d)
    (h : ℝ≥0) (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) {k : ℕ} (hk : k < m)
    (ω : Ω) :
    (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) (k + 1) q₀).1.2 -
        (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) (k + 1) q₀).2.2 =
      ((1 - 1 / ((m : ℝ) - k)) • ((crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).1.2 -
          (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).2.2) +
        ((h : ℝ) / 2) • ((b₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).1.1 +
            b₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).1.2) -
          (b₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).2.1 +
            b₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).2.2))) +
      cellNoise W ((k : ℝ) * h).toNNReal h
        (fun ω => s₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).1.1 -
          s₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).2.1)
        (fun ω => (s₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).1.2 -
            s₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).1.1) -
          (s₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).2.2 -
            s₁ (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀).2.1)) ω := by
  set q := crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀ with hq
  set n := noiseAt W h 0 ω k with hn
  have hX : (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) (k + 1) q₀).1.2 = zstep s₁ b₁ h q.1 n := rfl
  have hY : (crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) (k + 1) q₀).2.2 =
      zstep s₁ b₁ h q.2 n + (1 / ((m : ℝ) - k)) • (q.1.2 - q.2.2) :=
    cstep_steer hJ hk q n
  rw [hX, hY]
  have hn1 : ∀ j, n.1 j = W (((k : ℝ) * h).toNNReal + h) ω j - W ((k : ℝ) * h).toNNReal ω j :=
    fun j => by simp [hn, noiseAt]
  have hn2 : ∀ j, n.2 j = cellZeta W ((k : ℝ) * h).toNNReal h j ω := fun j => by
    simp [hn, noiseAt]
  ext i
  simp only [zstep, cellNoise, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    hn1, hn2]
  have hsum : (∑ j, (s₁ q.1.1 (i, j) * (W (((k : ℝ) * h).toNNReal + h) ω j -
          W ((k : ℝ) * h).toNNReal ω j) +
        (s₁ q.1.2 (i, j) - s₁ q.1.1 (i, j)) * cellZeta W ((k : ℝ) * h).toNNReal h j ω)) -
      (∑ j, (s₁ q.2.1 (i, j) * (W (((k : ℝ) * h).toNNReal + h) ω j -
          W ((k : ℝ) * h).toNNReal ω j) +
        (s₁ q.2.2 (i, j) - s₁ q.2.1 (i, j)) * cellZeta W ((k : ℝ) * h).toNNReal h j ω)) =
      ∑ j, ((s₁ q.1.1 (i, j) - s₁ q.2.1 (i, j)) * (W (((k : ℝ) * h).toNNReal + h) ω j -
          W ((k : ℝ) * h).toNNReal ω j) +
        (s₁ q.1.2 (i, j) - s₁ q.1.1 (i, j) - (s₁ q.2.2 (i, j) - s₁ q.2.1 (i, j))) *
          cellZeta W ((k : ℝ) * h).toNNReal h j ω) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  linear_combination hsum

theorem sq_step_bound2 {θ h L a p v : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hp : 0 ≤ p) (hv0 : 0 ≤ v) (hv : v ≤ h / 2 * (L * (p + a))) :
    (θ * a + v) ^ 2 ≤ θ ^ 2 * a ^ 2 + (2 * L + L ^ 2) * h * (a ^ 2 + p ^ 2) := by
  have h2 : 2 * (θ * a) * v ≤ 2 * a * v := by linarith only [mul_nonneg (mul_nonneg ha hv0) (sub_nonneg.2 hθ1)]
  have h3 : 2 * a * v ≤ h * L * (a * p + a ^ 2) := by
    have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 2 * a)
    linarith only [this]
  have h4 : a * p + a ^ 2 ≤ 2 * (a ^ 2 + p ^ 2) := by linarith only [sq_nonneg (a - p), sq_nonneg a, sq_nonneg p]
  have h4' : h * L * (a * p + a ^ 2) ≤ h * L * (2 * (a ^ 2 + p ^ 2)) :=
    mul_le_mul_of_nonneg_left h4 (mul_nonneg hh hL)
  have h5 : v ^ 2 ≤ (h / 2 * (L * (p + a))) ^ 2 := pow_le_pow_left₀ hv0 hv 2
  have h6 : (h / 2 * (L * (p + a))) ^ 2 ≤ h * L ^ 2 * (a ^ 2 + p ^ 2) := by
    have e1 : (p + a) ^ 2 ≤ 2 * (a ^ 2 + p ^ 2) := by linarith only [sq_nonneg (p - a)]
    have hh2 : h ^ 2 ≤ h := by linarith only [mul_nonneg hh (sub_nonneg.2 hh1)]
    have e2 : (h / 2 * (L * (p + a))) ^ 2 = h ^ 2 * (L ^ 2 * (p + a) ^ 2) / 4 := by ring
    rw [e2]
    have e3 : h ^ 2 * (L ^ 2 * (p + a) ^ 2) ≤ h * (L ^ 2 * (2 * (a ^ 2 + p ^ 2))) :=
      mul_le_mul hh2 (mul_le_mul_of_nonneg_left e1 (sq_nonneg L)) (by positivity) hh
    linarith only [e3, mul_nonneg hh (mul_nonneg (sq_nonneg L) (add_nonneg (sq_nonneg a) (sq_nonneg p)))]
  have e : (θ * a + v) ^ 2 = θ ^ 2 * a ^ 2 + 2 * (θ * a) * v + v ^ 2 := by ring
  rw [e]
  linarith only [h2, h3, h4', h5, h6]

variable (s₁ b₁ J m) in
/-- The coupled chain driven by the cells `0, 1, ...` of `W`. -/
noncomputable def cq (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (k : ℕ) (ω : Ω) :
    (SDEState d × SDEState d) × (SDEState d × SDEState d) :=
  crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀

theorem cq_fst_succ (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (k : ℕ) (ω : Ω) :
    (cq s₁ b₁ J m W h q₀ (k + 1) ω).1.1 - (cq s₁ b₁ J m W h q₀ (k + 1) ω).2.1 =
      (cq s₁ b₁ J m W h q₀ k ω).1.2 - (cq s₁ b₁ J m W h q₀ k ω).2.2 := rfl

set_option maxHeartbeats 1000000 in
/-- One cell of the steered second-moment recursion (C4c). -/
theorem crec_diff_step [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) {k : ℕ} (hk : k < m)
    (hD1 : ∀ i, MemLp (fun ω => ((cq s₁ b₁ J m W h q₀ k ω).1.1 -
      (cq s₁ b₁ J m W h q₀ k ω).2.1) i) 2 P)
    (hD2 : ∀ i, MemLp (fun ω => ((cq s₁ b₁ J m W h q₀ k ω).1.2 -
      (cq s₁ b₁ J m W h q₀ k ω).2.2) i) 2 P) :
    (∀ i, MemLp (fun ω => ((cq s₁ b₁ J m W h q₀ (k + 1) ω).1.2 -
      (cq s₁ b₁ J m W h q₀ (k + 1) ω).2.2) i) 2 P) ∧
    ∫ ω, ‖(cq s₁ b₁ J m W h q₀ (k + 1) ω).1.2 - (cq s₁ b₁ J m W h q₀ (k + 1) ω).2.2‖ ^ 2 ∂P ≤
      (1 - 1 / ((m : ℝ) - k)) ^ 2 *
          ∫ ω, ‖(cq s₁ b₁ J m W h q₀ k ω).1.2 - (cq s₁ b₁ J m W h q₀ k ω).2.2‖ ^ 2 ∂P +
        (2 * L + L ^ 2 + 6 * d * L ^ 2) * h *
          (∫ ω, ‖(cq s₁ b₁ J m W h q₀ k ω).1.2 - (cq s₁ b₁ J m W h q₀ k ω).2.2‖ ^ 2 ∂P +
            ∫ ω, ‖(cq s₁ b₁ J m W h q₀ k ω).1.1 - (cq s₁ b₁ J m W h q₀ k ω).2.1‖ ^ 2 ∂P) := by
  set sk : ℝ≥0 := ((k : ℝ) * h).toNNReal with hsk
  set Q : Ω → (SDEState d × SDEState d) × (SDEState d × SDEState d) :=
    fun ω => cq s₁ b₁ J m W h q₀ k ω with hQ
  set θ : ℝ := 1 - 1 / ((m : ℝ) - k) with hθ
  have hmk : (1 : ℝ) ≤ (m : ℝ) - k := by
    have : ((k + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hk
    push_cast at this; linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_one (by linarith)]; exact hmk
  have hθ1 : θ ≤ 1 := by
    rw [hθ]; have : 0 ≤ 1 / ((m : ℝ) - k) := by positivity
    linarith
  set D : Ω → SDEState d := fun ω => θ • ((Q ω).1.2 - (Q ω).2.2) +
    ((h : ℝ) / 2) • ((b₁ (Q ω).1.1 + b₁ (Q ω).1.2) - (b₁ (Q ω).2.1 + b₁ (Q ω).2.2)) with hD
  set A : Ω → SDEDiffusion d := fun ω => s₁ (Q ω).1.1 - s₁ (Q ω).2.1 with hA
  set B : Ω → SDEDiffusion d := fun ω => (s₁ (Q ω).1.2 - s₁ (Q ω).1.1) -
    (s₁ (Q ω).2.2 - s₁ (Q ω).2.1) with hB
  have heq : ∀ ω, (cq s₁ b₁ J m W h q₀ (k + 1) ω).1.2 - (cq s₁ b₁ J m W h q₀ (k + 1) ω).2.2 =
      D ω + cellNoise W sk h A B ω := fun ω => crec_diff_succ hJ W h q₀ hk ω
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hQm : Measurable[completedBrownianPast P W (fun _ => x₀) sk] Q :=
    crec_noise_meas_G hG hW.2.1 hs hb hJm h k q₀
  have m11 : Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => (Q ω).1.1 :=
    measurable_fst.comp (measurable_fst.comp hQm)
  have m12 : Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => (Q ω).1.2 :=
    measurable_snd.comp (measurable_fst.comp hQm)
  have m21 : Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => (Q ω).2.1 :=
    measurable_fst.comp (measurable_snd.comp hQm)
  have m22 : Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => (Q ω).2.2 :=
    measurable_snd.comp (measurable_snd.comp hQm)
  have hDm : Measurable[completedBrownianPast P W (fun _ => x₀) sk] D := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) sk
    have hg : Measurable fun ω => (b₁ (Q ω).1.1 + b₁ (Q ω).1.2) - (b₁ (Q ω).2.1 + b₁ (Q ω).2.2) :=
      ((hb.measurable.comp m11).add (hb.measurable.comp m12)).sub
        ((hb.measurable.comp m21).add (hb.measurable.comp m22))
    have hg2 : Measurable fun ω => ((h : ℝ) / 2) •
        ((b₁ (Q ω).1.1 + b₁ (Q ω).1.2) - (b₁ (Q ω).2.1 + b₁ (Q ω).2.2)) :=
      hg.const_smul ((h : ℝ) / 2)
    have hg1 : Measurable fun ω => θ • ((Q ω).1.2 - (Q ω).2.2) := (m12.sub m22).const_smul θ
    exact hg1.add hg2
  have hAm : Measurable[completedBrownianPast P W (fun _ => x₀) sk] A := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) sk
    exact (hs.measurable.comp m11).sub (hs.measurable.comp m21)
  have hBm : Measurable[completedBrownianPast P W (fun _ => x₀) sk] B := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) sk
    exact ((hs.measurable.comp m12).sub (hs.measurable.comp m11)).sub
      ((hs.measurable.comp m22).sub (hs.measurable.comp m21))
  have hDc : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => D ω i := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hDm
  have hAc : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => A ω p := fun p =>
    (EuclideanSpace.proj p).continuous.measurable.comp hAm
  have hBc : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) sk] fun ω => B ω p := fun p =>
    (EuclideanSpace.proj p).continuous.measurable.comp hBm
  have hS : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  have hAK : ∀ ω, ‖A ω‖ ≤ 4 * S := fun ω =>
    (norm_sub_le _ _).trans (by linarith [(hSg (Q ω).1.1).1, (hSg (Q ω).2.1).1])
  have hBK : ∀ ω, ‖B ω‖ ≤ 4 * S := fun ω =>
    ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))).trans
      (by linarith [(hSg (Q ω).1.1).1, (hSg (Q ω).2.1).1, (hSg (Q ω).1.2).1, (hSg (Q ω).2.2).1])
  have hgS : ∀ ω, ‖D ω - θ • ((Q ω).1.2 - (Q ω).2.2)‖ ≤ (h : ℝ) / 2 * (4 * S) := fun ω => by
    rw [hD]; simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) (norm_add_le _ _))).trans ?_) (by positivity)
    linarith [(hSg (Q ω).1.1).2, (hSg (Q ω).2.1).2, (hSg (Q ω).1.2).2, (hSg (Q ω).2.2).2]
  have hθL : ∀ i, MemLp (fun ω => (θ • ((Q ω).1.2 - (Q ω).2.2)) i) 2 P := fun i =>
    (hD2 i).const_mul θ
  have hDL : ∀ i, MemLp (fun ω => D ω i) 2 P := fun i =>
    memLp_coords_of_near hθL
      (fun i => aestronglyMeasurable_of_completedPast hW x₀ sk (hDc i)) hgS i
  have step := cellNoise_step hW x₀ sk h hh (D := D) (A := A) (B := B) (K := 4 * S)
    hDc hDL hAc hBc hAK hBK
  -- L² of the new difference
  have hNL : ∀ i, MemLp (fun ω => (cellNoise W sk h A B ω) i) 2 P := by
    intro i
    have hb4 : ∀ (F : Ω → SDEDiffusion d), (∀ ω, ‖F ω‖ ≤ 4 * S) → ∀ ω p, |F ω p| ≤ 4 * S :=
      fun F hF ω p => (coord_abs_le_diff _ p).trans (hF ω)
    show MemLp (fun ω => ∑ j, (A ω (i, j) * (W (sk + h) ω j - W sk ω j) +
      B ω (i, j) * cellZeta W sk h j ω)) 2 P
    refine memLp_finsetSum _ fun j _ => ?_
    refine (memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ sk (hAc (i, j)))
      (fun ω => hb4 A hAK ω (i, j))
      ((stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j))).add ?_
    exact memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ sk (hBc (i, j)))
      (fun ω => hb4 B hBK ω (i, j)) (cellZeta_moments hW sk h hh j).2.1
  refine ⟨fun i => ?_, ?_⟩
  · have e : (fun ω => ((cq s₁ b₁ J m W h q₀ (k + 1) ω).1.2 -
        (cq s₁ b₁ J m W h q₀ (k + 1) ω).2.2) i) =
        fun ω => D ω i + (cellNoise W sk h A B ω) i := funext fun ω => by rw [heq ω]; rfl
    rw [e]
    exact (hDL i).add (hNL i)
  -- the second-moment bound
  have hv : ∀ ω, ‖((h : ℝ) / 2) • ((b₁ (Q ω).1.1 + b₁ (Q ω).1.2) - (b₁ (Q ω).2.1 + b₁ (Q ω).2.2))‖ ≤
      (h : ℝ) / 2 * (L * (‖(Q ω).1.1 - (Q ω).2.1‖ + ‖(Q ω).1.2 - (Q ω).2.2‖)) := fun ω => by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : (b₁ (Q ω).1.1 + b₁ (Q ω).1.2) - (b₁ (Q ω).2.1 + b₁ (Q ω).2.2) =
        (b₁ (Q ω).1.1 - b₁ (Q ω).2.1) + (b₁ (Q ω).1.2 - b₁ (Q ω).2.2) := by abel
    rw [e, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hLg _ _).2 (hLg _ _).2)
  have pD : ∀ ω, ‖D ω‖ ^ 2 ≤ θ ^ 2 * ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2 +
      (2 * L + L ^ 2) * h * (‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2 + ‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2) := by
    intro ω
    have h1 : ‖D ω‖ ≤ θ * ‖(Q ω).1.2 - (Q ω).2.2‖ +
        ‖((h : ℝ) / 2) • ((b₁ (Q ω).1.1 + b₁ (Q ω).1.2) - (b₁ (Q ω).2.1 + b₁ (Q ω).2.2))‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, Real.norm_of_nonneg hθ0]
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    exact sq_step_bound2 hθ0 hθ1 hh.le hh1 hL (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (hv ω)
  have pAB : ∀ ω, ‖A ω‖ ^ 2 + ‖B ω‖ ^ 2 ≤
      3 * L ^ 2 * (‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2 + ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2) := fun ω => by
    have hA' : ‖A ω‖ ≤ L * ‖(Q ω).1.1 - (Q ω).2.1‖ := (hLg _ _).1
    have hB' : ‖B ω‖ ≤ L * ‖(Q ω).1.2 - (Q ω).2.2‖ + L * ‖(Q ω).1.1 - (Q ω).2.1‖ := by
      have e : B ω = (s₁ (Q ω).1.2 - s₁ (Q ω).2.2) - (s₁ (Q ω).1.1 - s₁ (Q ω).2.1) := by
        rw [hB]; abel
      rw [e]; exact (norm_sub_le _ _).trans (add_le_add (hLg _ _).1 (hLg _ _).1)
    have a2 := pow_le_pow_left₀ (norm_nonneg _) hA' 2
    have b2 := pow_le_pow_left₀ (norm_nonneg _) hB' 2
    linarith only [a2, b2, sq_nonneg (L * ‖(Q ω).1.2 - (Q ω).2.2‖ - L * ‖(Q ω).1.1 - (Q ω).2.1‖),
      sq_nonneg (L * ‖(Q ω).1.2 - (Q ω).2.2‖)]
  have Ip : Integrable (fun ω => ‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2) P :=
    integrable_norm_sq_of_coords hD1
  have Iq : Integrable (fun ω => ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2) P :=
    integrable_norm_sq_of_coords hD2
  have Iqp : Integrable (fun ω => ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2 + ‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2) P :=
    Iq.add Ip
  have Ipq : Integrable (fun ω => ‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2 + ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2) P :=
    Ip.add Iq
  set m1 := ∫ ω, ‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2 ∂P with hm1
  set m2 := ∫ ω, ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2 ∂P with hm2
  have i1 : ∫ ω, ‖D ω‖ ^ 2 ∂P ≤ θ ^ 2 * m2 + (2 * L + L ^ 2) * h * (m2 + m1) := by
    have e1 : ∫ ω, (θ ^ 2 * ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2 + (2 * L + L ^ 2) * h *
        (‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2 + ‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2)) ∂P =
        θ ^ 2 * m2 + (2 * L + L ^ 2) * h * (m2 + m1) := by
      rw [integral_add (Iq.const_mul _) (Iqp.const_mul _), integral_const_mul,
        integral_const_mul, integral_add Iq Ip]
    rw [← e1]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
      ((Iq.const_mul _).add (Iqp.const_mul _)) (ae_of_all _ pD)
  have i2 : ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P ≤ 3 * L ^ 2 * (m1 + m2) := by
    have e2 : ∫ ω, 3 * L ^ 2 * (‖(Q ω).1.1 - (Q ω).2.1‖ ^ 2 + ‖(Q ω).1.2 - (Q ω).2.2‖ ^ 2) ∂P =
        3 * L ^ 2 * (m1 + m2) := by
      rw [integral_const_mul, integral_add Ip Iq]
    rw [← e2]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
      (Ipq.const_mul _) (ae_of_all _ pAB)
  have hlhs : ∫ ω, ‖(cq s₁ b₁ J m W h q₀ (k + 1) ω).1.2 -
      (cq s₁ b₁ J m W h q₀ (k + 1) ω).2.2‖ ^ 2 ∂P =
      ∫ ω, ‖D ω + cellNoise W sk h A B ω‖ ^ 2 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [heq ω])
  rw [hlhs]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have k4 : 2 * d * (h : ℝ) * ∫ ω, (‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) ∂P ≤
      2 * d * h * (3 * L ^ 2 * (m1 + m2)) := mul_le_mul_of_nonneg_left i2 (by positivity)
  show _ ≤ θ ^ 2 * m2 + (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * (m2 + m1)
  linarith

/-- L² of the steered differences up to the horizon. -/
theorem crec_diff_memLp [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    ∀ k, k ≤ m → (∀ i, MemLp (fun ω => ((cq s₁ b₁ J m W h q₀ k ω).1.1 -
      (cq s₁ b₁ J m W h q₀ k ω).2.1) i) 2 P) ∧
      (∀ i, MemLp (fun ω => ((cq s₁ b₁ J m W h q₀ k ω).1.2 -
        (cq s₁ b₁ J m W h q₀ k ω).2.2) i) 2 P) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun i => by simp only [cq, crec]; exact memLp_const _,
      fun i => by simp only [cq, crec]; exact memLp_const _⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨fun i => ?_, (crec_diff_step hW x₀ hh hh1 hs hb hJm hJ hL hSg hLg q₀ (by omega)
      h1 h2).1⟩
    simp_rw [cq_fst_succ]
    exact h2 i

/-- C4c: the steered second moments obey the recursion of `steer_rec`; hence the terminal
second moment is `O(h)` and the weighted sum is bounded. -/
theorem crec_diff_bounds [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hm : 0 < m) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G) :
    ∫ ω, ‖(cq s₁ b₁ J m W h q₀ m ω).1.2 - (cq s₁ b₁ J m W h q₀ m ω).2.2‖ ^ 2 ∂P ≤
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 ∧
      ∑ k ∈ Finset.range m, (∫ ω, ‖(cq s₁ b₁ J m W h q₀ k ω).1.2 -
          (cq s₁ b₁ J m W h q₀ k ω).2.2‖ ^ 2 ∂P) / ((m : ℝ) - k) ^ 2 ≤
        G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m := by
  set c : ℝ := 2 * L + L ^ 2 + 6 * d * L ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hG : 0 ≤ G := (sq_nonneg _).trans hG1
  set e : ℕ → ℝ := fun k => ∫ ω, ‖(cq s₁ b₁ J m W h q₀ k ω).1.2 -
    (cq s₁ b₁ J m W h q₀ k ω).2.2‖ ^ 2 ∂P with he
  set e' : ℕ → ℝ := fun k => ∫ ω, ‖(cq s₁ b₁ J m W h q₀ k ω).1.1 -
    (cq s₁ b₁ J m W h q₀ k ω).2.1‖ ^ 2 ∂P with he'
  have h0 : e 0 ≤ G := by
    simp only [he, cq, crec, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact hG2
  have h0' : e' 0 ≤ G := by
    simp only [he', cq, crec, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact hG1
  have hsucc : ∀ k, e' (k + 1) = e k := fun k => by
    simp only [he, he']
    simp_rw [cq_fst_succ]
  have hrec : ∀ k, k < m → e (k + 1) ≤ (1 - 1 / ((m : ℝ) - k)) ^ 2 * e k +
      c * h * (e k + e' k) := fun k hk => by
    obtain ⟨h1, h2⟩ := crec_diff_memLp hW x₀ hh hh1 hs hb hJm hJ hL hSg hLg q₀ k hk.le
    exact (crec_diff_step hW x₀ hh hh1 hs hb hJm hJ hL hSg hLg q₀ hk h1 h2).2
  exact ⟨steer_rec_last hm hc0 hh.le hG e e' h0 h0' hsucc hrec,
    steer_rec_sum hm hc0 hh.le hG e e' h0 h0' hsucc hrec⟩

end C4c

end ItoLib

-- ===== CH =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

open EthierKurtz in
/-- A past-measurable factor times a future Brownian increment has mean zero. -/
theorem past_incr_mean_zero [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (j : Fin d) {u : Ω → ℝ} (hu : Measurable[completedBrownianPast P W (fun _ => x₀) s] u) :
    ∫ ω, u ω * (W (s + h) ω j - W s ω j) ∂P = 0 := by
  have hind := indepFun_past_fut hW x₀ s hu (incr_meas_fut W s h j)
  have hm := stdBrownian_coord_measurable hW
  have e := hind.integral_mul_eq_mul_integral (aestronglyMeasurable_of_completedPast hW x₀ s hu)
    (((hm _ j).sub (hm _ j)).aestronglyMeasurable)
  have e2 : (u * fun ω => W (s + h) ω j - W s ω j) = fun ω => u ω * (W (s + h) ω j - W s ω j) :=
    rfl
  rw [e2] at e
  rw [e, stdBrownian_integral_increment hW s h j, mul_zero]

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

-- ===== CI =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

/-- The event that `‖M k‖` reaches `λ` for the first time at step `k`. -/
def firstHit (M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (k : ℕ) : Set Ω :=
  {ω | lam ≤ ‖M k ω‖ ∧ ∀ j < k, ‖M j ω‖ < lam}

theorem firstHit_measurable [MeasurableSpace Ω] {M : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hM : ∀ k, Measurable (M k)) (lam : ℝ) (k : ℕ) : MeasurableSet (firstHit M lam k) := by
  have h1 : MeasurableSet {ω | lam ≤ ‖M k ω‖} :=
    measurableSet_le measurable_const (hM k).norm
  have h2 : MeasurableSet {ω | ∀ j < k, ‖M j ω‖ < lam} := by
    have : {ω | ∀ j < k, ‖M j ω‖ < lam} = ⋂ j ∈ Finset.range k, {ω | ‖M j ω‖ < lam} := by
      ext ω; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ => measurableSet_lt (hM j).norm measurable_const
  exact h1.inter h2

theorem firstHit_disjoint (M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : ℝ) {k k' : ℕ}
    (hkk : k ≠ k') : Disjoint (firstHit M lam k) (firstHit M lam k') := by
  rw [Set.disjoint_left]
  rintro ω ⟨h1, h2⟩ ⟨h1', h2'⟩
  rcases lt_or_gt_of_ne hkk with h | h
  · exact absurd h1 (not_le.2 (h2' k h))
  · exact absurd h1' (not_le.2 (h2 k' h))

theorem exists_hit_eq_iUnion (M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (m : ℕ) :
    {ω | ∃ k ≤ m, lam ≤ ‖M k ω‖} = ⋃ k ∈ Finset.range (m + 1), firstHit M lam k := by
  ext ω
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range, exists_prop, firstHit]
  constructor
  · rintro ⟨k, hk, hl⟩
    classical
    have hex : ∃ k, lam ≤ ‖M k ω‖ := ⟨k, hl⟩
    refine ⟨Nat.find hex, by have := Nat.find_min' hex hl; omega, Nat.find_spec hex,
      fun j hj => not_le.1 (Nat.find_min hex hj)⟩
  · rintro ⟨k, hk, hl, -⟩
    exact ⟨k, by omega, hl⟩

/-- Kolmogorov's maximal inequality. -/
theorem kolmogorov_max [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {M : ℕ → Ω → EuclideanSpace ℝ (Fin d)} (hM : ∀ k, Measurable (M k)) (m : ℕ)
    (hint : ∀ k ≤ m, Integrable (fun ω => ‖M k ω‖ ^ 2) μ) {lam : ℝ} (hlam : 0 < lam)
    (hort : ∀ k ≤ m, ∫ ω in firstHit M lam k, ⟪M k ω, M m ω - M k ω⟫ ∂μ = 0) :
    lam ^ 2 * μ.real {ω | ∃ k ≤ m, lam ≤ ‖M k ω‖} ≤ ∫ ω, ‖M m ω‖ ^ 2 ∂μ := by
  rw [exists_hit_eq_iUnion]
  have hFm := firstHit_measurable hM lam
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m + 1))) (firstHit M lam) :=
    fun k _ k' _ hkk => firstHit_disjoint M lam hkk
  rw [measureReal_biUnion_finset hdisj (fun k _ => hFm k), Finset.mul_sum]
  have hmi := hint m le_rfl
  have hkey : ∀ k ∈ Finset.range (m + 1),
      lam ^ 2 * μ.real (firstHit M lam k) ≤ ∫ ω in firstHit M lam k, ‖M m ω‖ ^ 2 ∂μ := by
    intro k hk
    have hk' : k ≤ m := by have := Finset.mem_range.1 hk; omega
    have hki := hint k hk'
    have hin : Integrable (fun ω => ⟪M k ω, M m ω - M k ω⟫) μ := by
      refine Integrable.mono' ((hki.add hmi).const_mul 2)
        ((hM k).inner ((hM m).sub (hM k))).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      show ‖M k ω‖ * ‖M m ω - M k ω‖ ≤ 2 * (‖M k ω‖ ^ 2 + ‖M m ω‖ ^ 2)
      have h1 := norm_sub_le (M m ω) (M k ω)
      have h2 := norm_nonneg (M m ω)
      have h3 := norm_nonneg (M k ω)
      have h4 := norm_nonneg (M m ω - M k ω)
      have h5 := mul_le_mul_of_nonneg_left (h1.trans (le_of_eq (add_comm _ _))) h3
      nlinarith [sq_nonneg (‖M m ω‖ - ‖M k ω‖)]
    have hpt : ∀ ω, ‖M k ω‖ ^ 2 + 2 * ⟪M k ω, M m ω - M k ω⟫ ≤ ‖M m ω‖ ^ 2 := fun ω => by
      have e : M m ω = M k ω + (M m ω - M k ω) := by abel
      have := norm_add_sq_real (M k ω) (M m ω - M k ω)
      rw [← e] at this
      nlinarith [sq_nonneg ‖M m ω - M k ω‖]
    have i1 : lam ^ 2 * μ.real (firstHit M lam k) ≤ ∫ ω in firstHit M lam k, ‖M k ω‖ ^ 2 ∂μ := by
      have := setIntegral_mono_on (integrableOn_const (μ := μ) (s := firstHit M lam k)
        (C := lam ^ 2) (measure_ne_top _ _)) hki.integrableOn (hFm k)
        (fun ω hω => pow_le_pow_left₀ hlam.le hω.1 2)
      rw [setIntegral_const, smul_eq_mul, mul_comm] at this
      exact this
    have i2 : ∫ ω in firstHit M lam k, ‖M k ω‖ ^ 2 ∂μ ≤
        ∫ ω in firstHit M lam k, ‖M m ω‖ ^ 2 ∂μ := by
      have e2 : ∫ ω in firstHit M lam k, (‖M k ω‖ ^ 2 + 2 * ⟪M k ω, M m ω - M k ω⟫) ∂μ =
          ∫ ω in firstHit M lam k, ‖M k ω‖ ^ 2 ∂μ := by
        rw [integral_add hki.integrableOn (hin.const_mul 2).integrableOn, integral_const_mul,
          hort k hk', mul_zero, add_zero]
      rw [← e2]
      exact setIntegral_mono_on (hki.add (hin.const_mul 2)).integrableOn hmi.integrableOn (hFm k)
        (fun ω _ => hpt ω)
    exact i1.trans i2
  refine (Finset.sum_le_sum hkey).trans ?_
  rw [← integral_biUnion_finset _ (fun k _ => hFm k) hdisj (fun k _ => hmi.integrableOn)]
  exact setIntegral_le_integral hmi (ae_of_all _ fun ω => sq_nonneg _)

end C5a

end ItoLib

-- ===== CK =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem past_zeta_mean_zero [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) (j : Fin d) {u : Ω → ℝ}
    (hu : Measurable[completedBrownianPast P W (fun _ => x₀) s] u) :
    ∫ ω, u ω * cellZeta W s h j ω ∂P = 0 := by
  have hind := indepFun_past_fut hW x₀ s hu (zeta_meas_fut hW.2.1 s h j)
  have e := hind.integral_mul_eq_mul_integral (aestronglyMeasurable_of_completedPast hW x₀ s hu)
    ((cellZeta_moments hW s h hh j).2.1.aestronglyMeasurable)
  have e2 : (u * cellZeta W s h j) = fun ω => u ω * cellZeta W s h j ω := rfl
  rw [e2] at e
  rw [e, (cellZeta_moments hW s h hh j).1, mul_zero]

theorem inner_cellNoise (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (A B : Ω → SDEDiffusion d)
    (Y : Ω → SDEState d) (ω : Ω) :
    ⟪Y ω, cellNoise W s h A B ω⟫_ℝ = ∑ i, ∑ j, ((A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
      (B ω (i, j) * Y ω i) * cellZeta W s h j ω) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cellNoise, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring

/-- Orthogonality of a past-measurable `L²` vector to the next cell's martingale increment. -/
theorem cell_orth [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) {Y : Ω → SDEState d} {A B : Ω → SDEDiffusion d} {K : ℝ}
    (hY : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => Y ω i)
    (hYL : ∀ i, MemLp (fun ω => Y ω i) 2 P)
    (hA : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p)
    (hB : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p)
    (hAK : ∀ ω, ‖A ω‖ ≤ K) (hBK : ∀ ω, ‖B ω‖ ≤ K) :
    Integrable (fun ω => ⟪Y ω, cellNoise W s h A B ω⟫_ℝ) P ∧
      ∫ ω, ⟪Y ω, cellNoise W s h A B ω⟫_ℝ ∂P = 0 := by
  have hu : ∀ (F : Ω → SDEDiffusion d), (∀ p, Measurable[completedBrownianPast P W
      (fun _ => x₀) s] fun ω => F ω p) → (∀ ω, ‖F ω‖ ≤ K) → ∀ i j,
      Measurable[completedBrownianPast P W (fun _ => x₀) s] (fun ω => F ω (i, j) * Y ω i) ∧
      MemLp (fun ω => F ω (i, j) * Y ω i) 2 P := by
    intro F hF hFK i j
    have hm : Measurable[completedBrownianPast P W (fun _ => x₀) s]
        (fun ω => F ω (i, j) * Y ω i) := by
      let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) s
      exact (hF (i, j)).mul (hY i)
    exact ⟨hm, memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ s (hF (i, j)))
      (fun ω => (coord_abs_le_diff _ (i, j)).trans (hFK ω)) (hYL i)⟩
  have hξL : ∀ j, MemLp (fun ω => W (s + h) ω j - W s ω j) 2 P := fun j =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have hζL : ∀ j, MemLp (fun ω => cellZeta W s h j ω) 2 P := fun j =>
    (cellZeta_moments hW s h hh j).2.1
  have i1 : ∀ i j, Integrable (fun ω => (A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j)) P :=
    fun i j => (hu A hA hAK i j).2.integrable_mul (hξL j)
  have i2 : ∀ i j, Integrable (fun ω => (B ω (i, j) * Y ω i) * cellZeta W s h j ω) P :=
    fun i j => (hu B hB hBK i j).2.integrable_mul (hζL j)
  have i3 : ∀ i j, Integrable (fun ω => (A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
      (B ω (i, j) * Y ω i) * cellZeta W s h j ω) P := fun i j => (i1 i j).add (i2 i j)
  have i4 : ∀ i, Integrable (fun ω => ∑ j, ((A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
      (B ω (i, j) * Y ω i) * cellZeta W s h j ω)) P := fun i =>
    integrable_finsetSum _ fun j _ => i3 i j
  have e : (fun ω => ⟪Y ω, cellNoise W s h A B ω⟫_ℝ) = fun ω => ∑ i, ∑ j,
      ((A ω (i, j) * Y ω i) * (W (s + h) ω j - W s ω j) +
        (B ω (i, j) * Y ω i) * cellZeta W s h j ω) := funext fun ω => inner_cellNoise W s h A B Y ω
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => i4 i, ?_⟩
  rw [integral_finsetSum _ fun i _ => i4 i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => i3 i j]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_add (i1 i j) (i2 i j), past_incr_mean_zero hW x₀ s h j (hu A hA hAK i j).1,
    past_zeta_mean_zero hW x₀ s h hh j (hu B hB hBK i j).1, add_zero]


theorem cellNoise_memLp [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (s h : ℝ≥0)
    (hh : 0 < (h : ℝ)) {A B : Ω → SDEDiffusion d} {K : ℝ}
    (hA : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => A ω p)
    (hB : ∀ p, Measurable[completedBrownianPast P W (fun _ => x₀) s] fun ω => B ω p)
    (hAK : ∀ ω, ‖A ω‖ ≤ K) (hBK : ∀ ω, ‖B ω‖ ≤ K) (i : Fin d) :
    MemLp (fun ω => (cellNoise W s h A B ω) i) 2 P := by
  have hb4 : ∀ (F : Ω → SDEDiffusion d), (∀ ω, ‖F ω‖ ≤ K) → ∀ ω p, |F ω p| ≤ K :=
    fun F hF ω p => (coord_abs_le_diff _ p).trans (hF ω)
  show MemLp (fun ω => ∑ j, (A ω (i, j) * (W (s + h) ω j - W s ω j) +
    B ω (i, j) * cellZeta W s h j ω)) 2 P
  refine memLp_finsetSum _ fun j _ => ?_
  refine (memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ s (hA (i, j)))
    (fun ω => hb4 A hAK ω (i, j))
    ((stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j))).add ?_
  exact memLp_two_bdd_mul (aestronglyMeasurable_of_completedPast hW x₀ s (hB (i, j)))
    (fun ω => hb4 B hBK ω (i, j)) (cellZeta_moments hW s h hh j).2.1

theorem firstHit_meas_le [MeasurableSpace Ω] {M : ℕ → Ω → SDEState d} {k : ℕ}
    (hM : ∀ j ≤ k, Measurable (M j)) (lam : ℝ) : MeasurableSet (firstHit M lam k) := by
  have h1 : MeasurableSet {ω | lam ≤ ‖M k ω‖} :=
    measurableSet_le measurable_const (hM k le_rfl).norm
  have h2 : MeasurableSet {ω | ∀ j < k, ‖M j ω‖ < lam} := by
    have : {ω | ∀ j < k, ‖M j ω‖ < lam} = ⋂ j ∈ Finset.range k, {ω | ‖M j ω‖ < lam} := by
      ext ω; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun j hj =>
      measurableSet_lt (hM j (Finset.mem_range.1 hj).le).norm measurable_const
  exact h1.inter h2

end C5c
end ItoLib

-- ===== CL =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

-- ===== CM =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

open StochKolmogorov.Persist

end C5dK
end ItoLib

-- ===== CN =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

/-- Discrete martingale with cell coefficients `A l`, `B l`. -/
noncomputable def gmart (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (A B : ℕ → Ω → SDEDiffusion d)
    (k : ℕ) (ω : Ω) : SDEState d :=
  ∑ l ∈ Finset.range k, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω

theorem tnn_succ (h : ℝ≥0) (l : ℕ) :
    (((l + 1 : ℕ) : ℝ) * h).toNNReal = ((l : ℝ) * h).toNNReal + h := by
  rw [show ((l + 1 : ℕ) : ℝ) * h = (l : ℝ) * h + (h : ℝ) by push_cast; ring,
    Real.toNNReal_add (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg h))
      (NNReal.coe_nonneg h), Real.toNNReal_coe]

theorem tnn_mono (h : ℝ≥0) {l k : ℕ} (hlk : l ≤ k) :
    ((l : ℝ) * h).toNNReal ≤ ((k : ℝ) * h).toNNReal :=
  Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hlk) h.2)

theorem cellNoise_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (s h : ℝ≥0) {t : ℝ≥0} (ht : s + h ≤ t)
    {A B : Ω → SDEDiffusion d} (hA : ∀ p, Measurable[G t] fun ω => A ω p)
    (hB : ∀ p, Measurable[G t] fun ω => B ω p) :
    Measurable[G t] (cellNoise W s h A B) := by
  let _ : MeasurableSpace Ω := G t
  have hc : Measurable fun ω => (fun i => ∑ j, (A ω (i, j) * (W (s + h) ω j - W s ω j) +
      B ω (i, j) * cellZeta W s h j ω) : Fin d → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hA (i, j)).mul ((hG _ _ ht j).sub (hG _ _ (le_self_add.trans ht) j))).add
      ((hB (i, j)).mul (cellZeta_meas_G hG hWc s h ht j))
  exact (PiLp.continuous_toLp 2 _).measurable.comp hc

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

theorem gmart_meas_G {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j) (hGm : Monotone G)
    (hWc : ∀ ω, Continuous fun s => W s ω)
    (hA : ∀ (l : ℕ) p, Measurable[G ((l : ℝ) * h).toNNReal] fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[G ((l : ℝ) * h).toNNReal] fun ω => B l ω p) (k : ℕ) :
    Measurable[G ((k : ℝ) * h).toNNReal] (gmart W h A B k) := by
  let _ : MeasurableSpace Ω := G ((k : ℝ) * h).toNNReal
  unfold gmart
  refine Finset.measurable_sum _ fun l hl => ?_
  have hlk : l + 1 ≤ k := Finset.mem_range.1 hl
  have ht : ((l : ℝ) * h).toNNReal + h ≤ ((k : ℝ) * h).toNNReal := by
    rw [← tnn_succ]; exact tnn_mono h hlk
  have hmono := hGm (tnn_mono h (Nat.le_of_succ_le hlk))
  exact cellNoise_meas_G hG hWc _ h ht (fun p => (hA l p).mono hmono le_rfl)
    (fun p => (hB l p).mono hmono le_rfl)

theorem gmart_meas (x₀ : SDEState d) (hWc : ∀ ω, Continuous fun s => W s ω)
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) (k : ℕ) :
    Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
      (gmart W h A B k) :=
  gmart_meas_G (fun r t hrt j => coord_measurable_completedPast P W _ hrt j)
    (fun _ _ hst => completedBrownianPast_mono P W _ hst) hWc hA hB k

theorem gmart_meas_amb (hW : IsStandardBrownian P W)
    (hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p) (hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p)
    (k : ℕ) : Measurable (gmart W h A B k) :=
  gmart_meas_G (G := fun _ => ‹MeasurableSpace Ω›)
    (fun r _ _ j => stdBrownian_coord_measurable hW r j) (fun _ _ _ => le_rfl) hW.2.1 hAa hBa k

theorem gmart_moment (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < (h : ℝ))
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) {K : ℝ} (hAK : ∀ l ω, ‖A l ω‖ ≤ K) (hBK : ∀ l ω, ‖B l ω‖ ≤ K)
    (k : ℕ) :
    (∀ i, MemLp (fun ω => gmart W h A B k ω i) 2 P) ∧
      ∫ ω, ‖gmart W h A B k ω‖ ^ 2 ∂P ≤
        ∑ l ∈ Finset.range k, 2 * d * h * ∫ ω, (‖A l ω‖ ^ 2 + ‖B l ω‖ ^ 2) ∂P := by
  induction k with
  | zero => refine ⟨fun i => ?_, ?_⟩ <;> simp [gmart]
  | succ k ih =>
    obtain ⟨ihL, ihB⟩ := ih
    have hDm := gmart_meas (P := P) x₀ hW.2.1 hA hB k
    have hDc : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
        fun ω => gmart W h A B k ω i := fun i =>
      (EuclideanSpace.proj i).continuous.measurable.comp hDm
    have step := cellNoise_step hW x₀ _ h hh hDc ihL (hA k) (hB k) (hAK k) (hBK k)
    have hNL := cellNoise_memLp hW x₀ _ h hh (hA k) (hB k) (hAK k) (hBK k)
    have e : ∀ ω, gmart W h A B (k + 1) ω = gmart W h A B k ω +
        cellNoise W ((k : ℝ) * h).toNNReal h (A k) (B k) ω := fun ω => by
      simp only [gmart, Finset.sum_range_succ]
    simp_rw [e]
    refine ⟨fun i => (ihL i).add (hNL i), ?_⟩
    rw [Finset.sum_range_succ]
    linarith

/-- The orthogonality hypothesis of `kolmogorov_max` for `gmart`. -/
theorem gmart_orth (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < (h : ℝ))
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) {K : ℝ} (hAK : ∀ l ω, ‖A l ω‖ ≤ K) (hBK : ∀ l ω, ‖B l ω‖ ≤ K)
    (hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p) (hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p)
    (lam : ℝ) {k m : ℕ} (hkm : k ≤ m) :
    ∫ ω in firstHit (gmart W h A B) lam k,
      ⟪gmart W h A B k ω, gmart W h A B m ω - gmart W h A B k ω⟫_ℝ ∂P = 0 := by
  set M : ℕ → Ω → SDEState d := gmart W h A B with hMdef
  set F := firstHit M lam k with hFdef
  have hMa : ∀ j, Measurable (M j) := gmart_meas_amb hW hAa hBa
  have hF : MeasurableSet F := firstHit_measurable hMa lam k
  set tk : ℝ≥0 := ((k : ℝ) * h).toNNReal with htk
  have hFG : MeasurableSet[completedBrownianPast P W (fun _ => x₀) tk] F := by
    have hj' : ∀ j ≤ k, Measurable[completedBrownianPast P W (fun _ => x₀) tk] (M j) :=
      fun j hj => (gmart_meas (P := P) x₀ hW.2.1 hA hB j).mono
        (completedBrownianPast_mono P W _ (tnn_mono h hj)) le_rfl
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) tk
    exact firstHit_meas_le hj' lam
  set Y : Ω → SDEState d := F.indicator (M k) with hYdef
  have hYm : Measurable[completedBrownianPast P W (fun _ => x₀) tk] Y := by
    have hk := gmart_meas (P := P) x₀ hW.2.1 hA hB k
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) tk
    exact hk.indicator hFG
  have hML := (gmart_moment hW x₀ hh hA hB hAK hBK k).1
  have hYc : ∀ i, (fun ω => Y ω i) = F.indicator (fun ω => M k ω i) := fun i => by
    funext ω; by_cases hω : ω ∈ F <;> simp [hYdef, hω]
  have hYL : ∀ i, MemLp (fun ω => Y ω i) 2 P := fun i => by
    rw [hYc i]; exact (hML i).indicator hF
  have hdiff : ∀ ω, M m ω - M k ω = ∑ l ∈ Finset.Ico k m,
      cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω := by
    intro ω
    simp only [hMdef, gmart]
    rw [← Finset.sum_Ico_eq_sub _ hkm]
  have hind : ∀ ω, F.indicator (fun ω => ⟪M k ω, M m ω - M k ω⟫_ℝ) ω =
      ∑ l ∈ Finset.Ico k m, ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω⟫_ℝ := by
    intro ω
    rw [← inner_sum, ← hdiff ω]
    by_cases hω : ω ∈ F <;> simp [hYdef, hω]
  have hl : ∀ l ∈ Finset.Ico k m,
      Integrable (fun ω => ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω⟫_ℝ) P ∧
      ∫ ω, ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h (A l) (B l) ω⟫_ℝ ∂P = 0 := fun l hl' => by
    have hkl : k ≤ l := (Finset.mem_Ico.1 hl').1
    have hmono := completedBrownianPast_mono P W (fun _ => x₀) (tnn_mono h hkl)
    refine cell_orth hW x₀ _ h hh (fun i => ?_) hYL (hA l) (hB l) (hAK l) (hBK l)
    exact ((EuclideanSpace.proj i).continuous.measurable.comp hYm).mono hmono le_rfl
  rw [← integral_indicator hF, integral_congr_ae (ae_of_all _ hind),
    integral_finsetSum _ fun l hl' => (hl l hl').1]
  exact Finset.sum_eq_zero fun l hl' => (hl l hl').2

/-- Kolmogorov's maximal inequality for `gmart`. -/
theorem gmart_max (hW : IsStandardBrownian P W) (x₀ : SDEState d) (hh : 0 < (h : ℝ))
    (hA : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => A l ω p)
    (hB : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal]
      fun ω => B l ω p) {K : ℝ} (hAK : ∀ l ω, ‖A l ω‖ ≤ K) (hBK : ∀ l ω, ‖B l ω‖ ≤ K)
    (hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p) (hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p)
    (m : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ k ≤ m, lam ≤ ‖gmart W h A B k ω‖} ≤
      ∑ l ∈ Finset.range m, 2 * d * h * ∫ ω, (‖A l ω‖ ^ 2 + ‖B l ω‖ ^ 2) ∂P := by
  have hMa : ∀ j, Measurable (gmart W h A B j) := gmart_meas_amb hW hAa hBa
  have hK := kolmogorov_max (μ := P) hMa m
    (fun k _ => integrable_norm_sq_of_coords (gmart_moment hW x₀ hh hA hB hAK hBK k).1)
    hlam (fun k hk => gmart_orth hW x₀ hh hA hB hAK hBK hAa hBa lam hk)
  exact hK.trans (gmart_moment hW x₀ hh hA hB hAK hBK m).2

end C5g
end ItoLib

-- ===== CO =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5t
/-! CORE route, s27: tracking estimate for the steered coupling. With `D_k = X_k - Ŷ_k`,
`D_k - ((m-k)/m) D_0 = (m-k) (Σ_{l<k} w_l Δb_l + gmart_k)` (weights `w_l = 1/(m-l-1)`), so a
maximal inequality on `gmart` plus a second-moment bound on the drift sum control
`max_{k ≤ m-1} ‖D_k - ((m-k)/m) D_0‖`. -/

/-- Weight `1/(m-l-1)` (zero once `l + 1 ≥ m`). -/
noncomputable def tw (m l : ℕ) : ℝ := if l + 1 < m then 1 / ((m : ℝ) - l - 1) else 0

theorem tw_nonneg (m l : ℕ) : 0 ≤ tw m l := by
  unfold tw; split_ifs with hl
  · have : (l : ℝ) + 1 < m := by exact_mod_cast hl
    exact (one_div_pos.2 (by linarith)).le
  · exact le_rfl

theorem tw_le_one (m l : ℕ) : tw m l ≤ 1 := by
  unfold tw; split_ifs with hl
  · have : (l : ℝ) + 1 + 1 ≤ m := by exact_mod_cast hl
    rw [div_le_one (by linarith)]; linarith
  · exact zero_le_one

theorem tw_mul {m l : ℕ} (hl : l + 1 < m) : ((m : ℝ) - l - 1) * tw m l = 1 := by
  have : (l : ℝ) + 1 < m := by exact_mod_cast hl
  rw [tw, if_pos hl, mul_one_div]; exact div_self (by linarith)

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
  (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)
  (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
  (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))

/-- Current difference `X_k - Ŷ_k`. -/
noncomputable def tD (k : ℕ) (ω : Ω) : SDEState d :=
  (cq s₁ b₁ J m W h q₀ k ω).1.2 - (cq s₁ b₁ J m W h q₀ k ω).2.2

/-- Previous difference `X_{k-1} - Ŷ_{k-1}`. -/
noncomputable def tD' (k : ℕ) (ω : Ω) : SDEState d :=
  (cq s₁ b₁ J m W h q₀ k ω).1.1 - (cq s₁ b₁ J m W h q₀ k ω).2.1

/-- Weighted first cell coefficient. -/
noncomputable def tA (l : ℕ) (ω : Ω) : SDEDiffusion d :=
  tw m l • (s₁ (cq s₁ b₁ J m W h q₀ l ω).1.1 - s₁ (cq s₁ b₁ J m W h q₀ l ω).2.1)

/-- Weighted second cell coefficient. -/
noncomputable def tB (l : ℕ) (ω : Ω) : SDEDiffusion d :=
  tw m l • ((s₁ (cq s₁ b₁ J m W h q₀ l ω).1.2 - s₁ (cq s₁ b₁ J m W h q₀ l ω).1.1) -
    (s₁ (cq s₁ b₁ J m W h q₀ l ω).2.2 - s₁ (cq s₁ b₁ J m W h q₀ l ω).2.1))

/-- Drift difference of one cell. -/
noncomputable def tdr (l : ℕ) (ω : Ω) : SDEState d :=
  ((h : ℝ) / 2) • ((b₁ (cq s₁ b₁ J m W h q₀ l ω).1.1 + b₁ (cq s₁ b₁ J m W h q₀ l ω).1.2) -
    (b₁ (cq s₁ b₁ J m W h q₀ l ω).2.1 + b₁ (cq s₁ b₁ J m W h q₀ l ω).2.2))

/-- Weighted drift sum. -/
noncomputable def tS (k : ℕ) (ω : Ω) : SDEState d :=
  ∑ l ∈ Finset.range k, tw m l • tdr s₁ b₁ J m W h q₀ l ω

theorem cellNoise_smul (s h' : ℝ≥0) (c : ℝ) (A B : Ω → SDEDiffusion d) (ω : Ω) :
    cellNoise W s h' (fun ω => c • A ω) (fun ω => c • B ω) ω = c • cellNoise W s h' A B ω := by
  ext i
  simp only [cellNoise, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {s₁ b₁ J m}

/-- The tracking identity. -/
theorem track_identity (hJ : ∀ p v, avgApply s₁ p (J p v) = v) (ω : Ω) :
    ∀ k, k + 1 ≤ m → tD s₁ b₁ J m W h q₀ k ω =
      (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω +
        ((m : ℝ) - k) • (tS s₁ b₁ J m W h q₀ k ω +
          gmart W h (tA s₁ b₁ J m W h q₀) (tB s₁ b₁ J m W h q₀) k ω) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [Nat.cast_zero, sub_zero, div_self hm, one_smul, tS, gmart, Finset.range_zero,
      Finset.sum_empty, add_zero, smul_zero]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hkm : k < m := by omega
    have hs := crec_diff_succ (b₁ := b₁) hJ W h q₀ hkm ω
    have e1 : tD s₁ b₁ J m W h q₀ (k + 1) ω =
        ((1 - 1 / ((m : ℝ) - k)) • tD s₁ b₁ J m W h q₀ k ω + tdr s₁ b₁ J m W h q₀ k ω) +
          cellNoise W ((k : ℝ) * h).toNNReal h
            (fun ω => s₁ (cq s₁ b₁ J m W h q₀ k ω).1.1 - s₁ (cq s₁ b₁ J m W h q₀ k ω).2.1)
            (fun ω => (s₁ (cq s₁ b₁ J m W h q₀ k ω).1.2 - s₁ (cq s₁ b₁ J m W h q₀ k ω).1.1) -
              (s₁ (cq s₁ b₁ J m W h q₀ k ω).2.2 - s₁ (cq s₁ b₁ J m W h q₀ k ω).2.1)) ω := hs
    have hkm1 : k + 1 < m := by omega
    have hc := tw_mul hkm1
    have eN : cellNoise W ((k : ℝ) * h).toNNReal h
        (fun ω => s₁ (cq s₁ b₁ J m W h q₀ k ω).1.1 - s₁ (cq s₁ b₁ J m W h q₀ k ω).2.1)
        (fun ω => (s₁ (cq s₁ b₁ J m W h q₀ k ω).1.2 - s₁ (cq s₁ b₁ J m W h q₀ k ω).1.1) -
          (s₁ (cq s₁ b₁ J m W h q₀ k ω).2.2 - s₁ (cq s₁ b₁ J m W h q₀ k ω).2.1)) ω =
        ((m : ℝ) - k - 1) • cellNoise W ((k : ℝ) * h).toNNReal h
          (tA s₁ b₁ J m W h q₀ k) (tB s₁ b₁ J m W h q₀ k) ω := by
      rw [show tA s₁ b₁ J m W h q₀ k = fun ω => tw m k •
          (s₁ (cq s₁ b₁ J m W h q₀ k ω).1.1 - s₁ (cq s₁ b₁ J m W h q₀ k ω).2.1) from rfl,
        show tB s₁ b₁ J m W h q₀ k = fun ω => tw m k •
          ((s₁ (cq s₁ b₁ J m W h q₀ k ω).1.2 - s₁ (cq s₁ b₁ J m W h q₀ k ω).1.1) -
            (s₁ (cq s₁ b₁ J m W h q₀ k ω).2.2 - s₁ (cq s₁ b₁ J m W h q₀ k ω).2.1)) from rfl,
        cellNoise_smul, smul_smul, hc, one_smul]
    have eS : tS s₁ b₁ J m W h q₀ (k + 1) ω = tS s₁ b₁ J m W h q₀ k ω +
        tw m k • tdr s₁ b₁ J m W h q₀ k ω := by
      simp only [tS, Finset.sum_range_succ]
    have eG : gmart W h (tA s₁ b₁ J m W h q₀) (tB s₁ b₁ J m W h q₀) (k + 1) ω =
        gmart W h (tA s₁ b₁ J m W h q₀) (tB s₁ b₁ J m W h q₀) k ω +
          cellNoise W ((k : ℝ) * h).toNNReal h
            (tA s₁ b₁ J m W h q₀ k) (tB s₁ b₁ J m W h q₀ k) ω := by
      simp only [gmart, Finset.sum_range_succ]
    rw [e1, eN, ih', eS, eG]
    have hmk : (m : ℝ) - k ≠ 0 := by
      have : (k : ℝ) + 1 < m := by exact_mod_cast hkm1
      linarith
    have hm0 : (m : ℝ) ≠ 0 := by
      have : (k : ℝ) + 1 < m := by exact_mod_cast hkm1
      linarith
    have k1 : (1 - 1 / ((m : ℝ) - k)) * (((m : ℝ) - k) / m) = ((m : ℝ) - ((k + 1 : ℕ) : ℝ)) / m := by
      push_cast; field_simp; ring
    have k2 : (1 - 1 / ((m : ℝ) - k)) * ((m : ℝ) - k) = (m : ℝ) - ((k + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    have k3 : (m : ℝ) - ((k + 1 : ℕ) : ℝ) = (m : ℝ) - k - 1 := by push_cast; ring
    rw [smul_add, smul_smul, smul_smul, k1, k2, k3]
    simp only [smul_add, smul_smul, hc, one_smul]
    abel

theorem tAB_sq_le {L : ℝ} (hL : 0 ≤ L)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖) (l : ℕ) (ω : Ω) :
    ‖tA s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tB s₁ b₁ J m W h q₀ l ω‖ ^ 2 ≤
      3 * tw m l ^ 2 * L ^ 2 * (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) := by
  set q := cq s₁ b₁ J m W h q₀ l ω with hq
  have hw := tw_nonneg m l
  have e1 : ‖tA s₁ b₁ J m W h q₀ l ω‖ = tw m l * ‖s₁ q.1.1 - s₁ q.2.1‖ := by
    rw [tA, norm_smul, Real.norm_of_nonneg hw]
  have e2 : ‖tB s₁ b₁ J m W h q₀ l ω‖ =
      tw m l * ‖(s₁ q.1.2 - s₁ q.2.2) - (s₁ q.1.1 - s₁ q.2.1)‖ := by
    rw [tB, norm_smul, Real.norm_of_nonneg hw]
    congr 2; abel
  have a1 : ‖s₁ q.1.1 - s₁ q.2.1‖ ≤ L * ‖tD' s₁ b₁ J m W h q₀ l ω‖ := (hLg _ _).1
  have a2 : ‖s₁ q.1.2 - s₁ q.2.2‖ ≤ L * ‖tD s₁ b₁ J m W h q₀ l ω‖ := (hLg _ _).1
  have a3 := norm_sub_le (s₁ q.1.2 - s₁ q.2.2) (s₁ q.1.1 - s₁ q.2.1)
  rw [e1, e2]
  have n1 := norm_nonneg (s₁ q.1.1 - s₁ q.2.1)
  have n3 := norm_nonneg ((s₁ q.1.2 - s₁ q.2.2) - (s₁ q.1.1 - s₁ q.2.1))
  have nD := norm_nonneg (tD s₁ b₁ J m W h q₀ l ω)
  have nD' := norm_nonneg (tD' s₁ b₁ J m W h q₀ l ω)
  have b1 : ‖s₁ q.1.1 - s₁ q.2.1‖ ^ 2 ≤ L ^ 2 * ‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ n1 a1 2
  have b3 : ‖(s₁ q.1.2 - s₁ q.2.2) - (s₁ q.1.1 - s₁ q.2.1)‖ ^ 2 ≤
      2 * L ^ 2 * ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2 + 2 * L ^ 2 * ‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 := by
    have c1 : ‖(s₁ q.1.2 - s₁ q.2.2) - (s₁ q.1.1 - s₁ q.2.1)‖ ≤
        L * ‖tD s₁ b₁ J m W h q₀ l ω‖ + L * ‖tD' s₁ b₁ J m W h q₀ l ω‖ := by linarith only [a1, a2, a3]
    have c2 := pow_le_pow_left₀ n3 c1 2
    linarith only [c2, sq_nonneg (L * ‖tD s₁ b₁ J m W h q₀ l ω‖ - L * ‖tD' s₁ b₁ J m W h q₀ l ω‖)]
  have hw2 : 0 ≤ tw m l ^ 2 := sq_nonneg _
  rw [mul_pow, mul_pow]
  linarith only [mul_le_mul_of_nonneg_left b1 hw2, mul_le_mul_of_nonneg_left b3 hw2,
    mul_nonneg hw2 (mul_nonneg (sq_nonneg L) (sq_nonneg ‖tD' s₁ b₁ J m W h q₀ l ω‖)),
    mul_nonneg hw2 (mul_nonneg (sq_nonneg L) (sq_nonneg ‖tD s₁ b₁ J m W h q₀ l ω‖))]

theorem tdr_sq_le {L : ℝ} (hL : 0 ≤ L)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖) (l : ℕ) (ω : Ω) :
    ‖tw m l • tdr s₁ b₁ J m W h q₀ l ω‖ ^ 2 ≤
      tw m l ^ 2 * ((h : ℝ) ^ 2 * L ^ 2 / 2) *
        (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) := by
  set q := cq s₁ b₁ J m W h q₀ l ω with hq
  have hw := tw_nonneg m l
  have hh0 : (0 : ℝ) ≤ (h : ℝ) / 2 := by positivity
  have e : ‖tw m l • tdr s₁ b₁ J m W h q₀ l ω‖ =
      tw m l * ((h : ℝ) / 2 * ‖(b₁ q.1.1 - b₁ q.2.1) + (b₁ q.1.2 - b₁ q.2.2)‖) := by
    rw [norm_smul, Real.norm_of_nonneg hw, tdr, norm_smul, Real.norm_of_nonneg hh0]
    congr 3; abel
  have a1 : ‖b₁ q.1.1 - b₁ q.2.1‖ ≤ L * ‖tD' s₁ b₁ J m W h q₀ l ω‖ := (hLg _ _).2
  have a2 : ‖b₁ q.1.2 - b₁ q.2.2‖ ≤ L * ‖tD s₁ b₁ J m W h q₀ l ω‖ := (hLg _ _).2
  have a3 := norm_add_le (b₁ q.1.1 - b₁ q.2.1) (b₁ q.1.2 - b₁ q.2.2)
  have n3 := norm_nonneg ((b₁ q.1.1 - b₁ q.2.1) + (b₁ q.1.2 - b₁ q.2.2))
  have c1 : ‖(b₁ q.1.1 - b₁ q.2.1) + (b₁ q.1.2 - b₁ q.2.2)‖ ≤
      L * ‖tD' s₁ b₁ J m W h q₀ l ω‖ + L * ‖tD s₁ b₁ J m W h q₀ l ω‖ := by linarith only [a1, a2, a3]
  have c2 := pow_le_pow_left₀ n3 c1 2
  have c3 : ‖(b₁ q.1.1 - b₁ q.2.1) + (b₁ q.1.2 - b₁ q.2.2)‖ ^ 2 ≤
      2 * L ^ 2 * (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) := by
    linarith only [c2, sq_nonneg (L * ‖tD s₁ b₁ J m W h q₀ l ω‖ - L * ‖tD' s₁ b₁ J m W h q₀ l ω‖)]
  rw [e, mul_pow, mul_pow, div_pow]
  have hw2 : 0 ≤ tw m l ^ 2 := sq_nonneg _
  have hh2 : (0 : ℝ) ≤ (h : ℝ) ^ 2 / 2 ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left c3 (mul_nonneg hw2 hh2)
  linarith only [this]

set_option maxHeartbeats 1000000 in
/-- T1: maximal tracking estimate for the steered coupling. -/
theorem track_bound [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hW : IsStandardBrownian P W) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hm2 : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    (δ / (2 * m)) ^ 2 * P.real {ω | ∃ k ≤ m - 1, δ ≤ ‖tD s₁ b₁ J m W h q₀ k ω -
        (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω‖} ≤
      (6 * d * h * L ^ 2 + ((m - 1 : ℕ) : ℝ) * (h : ℝ) ^ 2 * L ^ 2 / 2) *
        ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 *
          ∫ ω, (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  set lam : ℝ := δ / (2 * m) with hlam
  have hlam0 : 0 < lam := div_pos hδ (by linarith)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  -- measurability of the coupled chain
  have hQa : ∀ k, Measurable fun ω => cq s₁ b₁ J m W h q₀ k ω := fun k => by
    have := crec_noise_meas_G (m := m) (G := fun _ => ‹MeasurableSpace Ω›)
      (fun r _ _ j => stdBrownian_coord_measurable hW r j) hW.2.1 hs hb hJm h k q₀
    exact this
  have hQp : ∀ k : ℕ, Measurable[completedBrownianPast P W (fun _ => (0 : SDEState d))
      ((k : ℝ) * h).toNNReal] fun ω => cq s₁ b₁ J m W h q₀ k ω := fun k => by
    have := crec_noise_meas_G (m := m) (fun r t hrt j => coord_measurable_completedPast P W
      (fun _ => (0 : SDEState d)) hrt j) hW.2.1 hs hb hJm h k q₀
    exact this
  have hAm : ∀ {G : MeasurableSpace Ω} (k : ℕ),
      Measurable[G] (fun ω => cq s₁ b₁ J m W h q₀ k ω) →
      (∀ p, Measurable[G] fun ω => tA s₁ b₁ J m W h q₀ k ω p) ∧
      (∀ p, Measurable[G] fun ω => tB s₁ b₁ J m W h q₀ k ω p) := by
    intro G k hQ
    let _ : MeasurableSpace Ω := G
    have h11 := hs.measurable.comp (measurable_fst.comp (measurable_fst.comp hQ))
    have h12 := hs.measurable.comp (measurable_snd.comp (measurable_fst.comp hQ))
    have h21 := hs.measurable.comp (measurable_fst.comp (measurable_snd.comp hQ))
    refine ⟨fun p => ?_, fun p => ?_⟩
    · exact (EuclideanSpace.proj p).continuous.measurable.comp ((h11.sub h21).const_smul (tw m k))
    · have h22' := hs.measurable.comp (measurable_snd.comp (measurable_snd.comp hQ))
      exact (EuclideanSpace.proj p).continuous.measurable.comp
        (((h12.sub h11).sub (h22'.sub h21)).const_smul (tw m k))
  have hAK : ∀ l ω, ‖tA s₁ b₁ J m W h q₀ l ω‖ ≤ 4 * S := fun l ω => by
    rw [tA, norm_smul, Real.norm_of_nonneg (tw_nonneg m l)]
    have := norm_sub_le (s₁ (cq s₁ b₁ J m W h q₀ l ω).1.1) (s₁ (cq s₁ b₁ J m W h q₀ l ω).2.1)
    have h1 := (hSg (cq s₁ b₁ J m W h q₀ l ω).1.1).1
    have h2 := (hSg (cq s₁ b₁ J m W h q₀ l ω).2.1).1
    have hw1 := tw_le_one m l
    have hN := norm_nonneg (s₁ (cq s₁ b₁ J m W h q₀ l ω).1.1 - s₁ (cq s₁ b₁ J m W h q₀ l ω).2.1)
    have h0 := norm_nonneg (s₁ (cq s₁ b₁ J m W h q₀ l ω).1.1)
    linarith only [this, h1, h2, h0, mul_nonneg hN (sub_nonneg.2 hw1)]
  have hBK : ∀ l ω, ‖tB s₁ b₁ J m W h q₀ l ω‖ ≤ 4 * S := fun l ω => by
    rw [tB, norm_smul, Real.norm_of_nonneg (tw_nonneg m l)]
    set q := cq s₁ b₁ J m W h q₀ l ω
    have a1 := norm_sub_le (s₁ q.1.2 - s₁ q.1.1) (s₁ q.2.2 - s₁ q.2.1)
    have a2 := norm_sub_le (s₁ q.1.2) (s₁ q.1.1)
    have a3 := norm_sub_le (s₁ q.2.2) (s₁ q.2.1)
    have c1 := (hSg q.1.1).1; have c2 := (hSg q.1.2).1; have c3 := (hSg q.2.1).1; have c4 := (hSg q.2.2).1
    have hw1 := tw_le_one m l
    have hN := norm_nonneg ((s₁ q.1.2 - s₁ q.1.1) - (s₁ q.2.2 - s₁ q.2.1))
    linarith only [a1, a2, a3, c1, c2, c3, c4, mul_nonneg hN (sub_nonneg.2 hw1)]
  -- L² of the differences
  have hDL := crec_diff_memLp (m := m) hW 0 hh hh1 hs hb hJm hJ hL hSg hLg q₀
  have hI : ∀ l, l ≤ m → Integrable (fun ω => ‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 +
      ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) P := fun l hl =>
    (integrable_norm_sq_of_coords (hDL l hl).1).add (integrable_norm_sq_of_coords (hDL l hl).2)
  -- the two bad events
  set Z : Ω → ℝ := fun ω => ∑ l ∈ Finset.range (m - 1), ‖tw m l • tdr s₁ b₁ J m W h q₀ l ω‖
    with hZ
  set M := gmart W h (tA s₁ b₁ J m W h q₀) (tB s₁ b₁ J m W h q₀) with hM
  have hsub : {ω | ∃ k ≤ m - 1, δ ≤ ‖tD s₁ b₁ J m W h q₀ k ω -
      (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω‖} ⊆
      {ω | ∃ k ≤ m - 1, lam ≤ ‖M k ω‖} ∪ {ω | lam ≤ Z ω} := by
    rintro ω ⟨k, hk, hδk⟩
    by_contra hc
    simp only [mem_union, mem_setOf_eq, not_or, not_exists, not_le] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hid := track_identity (m := m) (b₁ := b₁) W h q₀ hJ ω k (by omega)
    rw [hid, add_sub_cancel_left, norm_smul] at hδk
    have hkR : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
    rw [Real.norm_of_nonneg (by linarith)] at hδk
    have hS : ‖tS s₁ b₁ J m W h q₀ k ω‖ ≤ Z ω := by
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
        (fun _ _ _ => norm_nonneg _)
    have hG : ‖M k ω‖ < lam := lt_of_not_ge fun h' => hc1 k ⟨hk, h'⟩
    have ht := norm_add_le (tS s₁ b₁ J m W h q₀ k ω) (M k ω)
    have h3 : ((m : ℝ) - k) * ‖tS s₁ b₁ J m W h q₀ k ω + M k ω‖ ≤ m * (2 * lam) := by
      have hn := norm_nonneg (tS s₁ b₁ J m W h q₀ k ω + M k ω)
      have : ‖tS s₁ b₁ J m W h q₀ k ω + M k ω‖ < 2 * lam := by linarith
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith only [mul_nonneg hk0 hn, mul_le_mul_of_nonneg_left this.le (Nat.cast_nonneg (α := ℝ) m)]
    have h4 : (m : ℝ) * (2 * lam) = δ := by
      rw [hlam]; field_simp
    have h5 : ((m : ℝ) - k) * ‖tS s₁ b₁ J m W h q₀ k ω + M k ω‖ < δ := by
      have hn := norm_nonneg (tS s₁ b₁ J m W h q₀ k ω + M k ω)
      have : ‖tS s₁ b₁ J m W h q₀ k ω + M k ω‖ < 2 * lam := by linarith
      rcases eq_or_lt_of_le hkR with e | e
      · rw [e, sub_self, zero_mul]; exact hδ
      · have : ((m : ℝ) - k) * ‖tS s₁ b₁ J m W h q₀ k ω + M k ω‖ < ((m : ℝ) - k) * (2 * lam) :=
          mul_lt_mul_of_pos_left this (by linarith)
        linarith only [this, h4, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hlam0.le]
    linarith
  -- bound 1: Kolmogorov maximal inequality
  have hB1 := gmart_max hW 0 hh (A := tA s₁ b₁ J m W h q₀) (B := tB s₁ b₁ J m W h q₀)
    (fun l => (hAm l (hQp l)).1) (fun l => (hAm l (hQp l)).2) hAK hBK
    (fun l => (hAm l (hQa l)).1) (fun l => (hAm l (hQa l)).2) (m - 1) hlam0
  have hB1' : ∑ l ∈ Finset.range (m - 1), 2 * d * h *
      ∫ ω, (‖tA s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tB s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P ≤
      ∑ l ∈ Finset.range (m - 1), 6 * d * h * L ^ 2 * (tw m l ^ 2 *
        ∫ ω, (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P) := by
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l ≤ m := by have := Finset.mem_range.1 hl; omega
    have hmono : ∫ ω, (‖tA s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tB s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P ≤
        ∫ ω, 3 * tw m l ^ 2 * L ^ 2 *
          (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
        ((hI l hl').const_mul _) (ae_of_all _ fun ω => tAB_sq_le W h q₀ hL hLg l ω)
    rw [integral_const_mul] at hmono
    have hd : (0 : ℝ) ≤ 2 * d * h := by positivity
    have := mul_le_mul_of_nonneg_left hmono hd
    linarith only [this]
  -- bound 2: second moment of the drift sum
  have hZm : Measurable Z := by
    refine Finset.measurable_sum _ fun l _ => ?_
    have hQ := hQa l
    have h11 := hb.measurable.comp (measurable_fst.comp (measurable_fst.comp hQ))
    have h12 := hb.measurable.comp (measurable_snd.comp (measurable_fst.comp hQ))
    have h21 := hb.measurable.comp (measurable_fst.comp (measurable_snd.comp hQ))
    have h22 := hb.measurable.comp (measurable_snd.comp (measurable_snd.comp hQ))
    have ht : Measurable (fun ω => tdr s₁ b₁ J m W h q₀ l ω) :=
      ((h11.add h12).sub (h21.add h22)).const_smul ((h : ℝ) / 2)
    exact (ht.const_smul (tw m l)).norm
  set g : Ω → ℝ := fun ω => ((m - 1 : ℕ) : ℝ) * ∑ l ∈ Finset.range (m - 1),
    tw m l ^ 2 * ((h : ℝ) ^ 2 * L ^ 2 / 2) *
      (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) with hg
  have hgi : Integrable g P := by
    refine Integrable.const_mul (integrable_finsetSum _ fun l hl => ?_) _
    have hl' : l ≤ m := by have := Finset.mem_range.1 hl; omega
    exact (hI l hl').const_mul _
  have hZ2 : ∀ ω, Z ω ^ 2 ≤ g ω := fun ω => by
    have c1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (m - 1))
      (f := fun l => ‖tw m l • tdr s₁ b₁ J m W h q₀ l ω‖)
    rw [Finset.card_range] at c1
    refine c1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
      tdr_sq_le W h q₀ hL hLg l ω) (Nat.cast_nonneg _))
  have hZi : Integrable (fun ω => Z ω ^ 2) P :=
    Integrable.mono' hgi (hZm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hZ2 ω)
  have hB2 : lam ^ 2 * P.real {ω | lam ≤ Z ω} ≤ ∫ ω, g ω ∂P := by
    have hsub2 : {ω | lam ≤ Z ω} ⊆ {ω | lam ^ 2 ≤ Z ω ^ 2} := fun ω hω =>
      pow_le_pow_left₀ hlam0.le hω 2
    calc lam ^ 2 * P.real {ω | lam ≤ Z ω} ≤ lam ^ 2 * P.real {ω | lam ^ 2 ≤ Z ω ^ 2} :=
          mul_le_mul_of_nonneg_left (measureReal_mono hsub2) (sq_nonneg _)
      _ ≤ ∫ ω, Z ω ^ 2 ∂P :=
          mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) hZi _
      _ ≤ ∫ ω, g ω ∂P := integral_mono hZi hgi hZ2
  have hgint : ∫ ω, g ω ∂P = ((m - 1 : ℕ) : ℝ) * ((h : ℝ) ^ 2 * L ^ 2 / 2) *
      ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 *
        ∫ ω, (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P := by
    rw [hg, integral_const_mul, integral_finsetSum _ fun l hl => ?_]
    · simp_rw [integral_const_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    · have hl' : l ≤ m := by have := Finset.mem_range.1 hl; omega
      exact (hI l hl').const_mul _
  -- combine
  have hU := measureReal_union_le (μ := P) {ω | ∃ k ≤ m - 1, lam ≤ ‖M k ω‖} {ω | lam ≤ Z ω}
  have hmono := measureReal_mono (μ := P) hsub
  have hl2 : 0 ≤ lam ^ 2 := sq_nonneg _
  calc lam ^ 2 * P.real {ω | ∃ k ≤ m - 1, δ ≤ ‖tD s₁ b₁ J m W h q₀ k ω -
        (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω‖}
      ≤ lam ^ 2 * (P.real {ω | ∃ k ≤ m - 1, lam ≤ ‖M k ω‖} + P.real {ω | lam ≤ Z ω}) :=
        mul_le_mul_of_nonneg_left (hmono.trans hU) hl2
    _ = lam ^ 2 * P.real {ω | ∃ k ≤ m - 1, lam ≤ ‖M k ω‖} + lam ^ 2 * P.real {ω | lam ≤ Z ω} :=
        mul_add _ _ _
    _ ≤ (∑ l ∈ Finset.range (m - 1), 6 * d * h * L ^ 2 * (tw m l ^ 2 *
          ∫ ω, (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P)) +
        ((m - 1 : ℕ) : ℝ) * ((h : ℝ) ^ 2 * L ^ 2 / 2) *
          ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 *
            ∫ ω, (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P :=
        add_le_add (hB1.trans hB1') (hB2.trans hgint.le)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Arithmetic: the weighted sum in `track_bound` is controlled by the sum of `crec_diff_bounds`. -/
theorem track_V_le {m : ℕ} (hm2 : 2 ≤ m) {G : ℝ} (e e' : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k)
    (he'0 : e' 0 ≤ G) (he' : ∀ k, e' (k + 1) = e k) :
    ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * (e' l + e l) ≤
      G / ((m : ℝ) - 1) ^ 2 + 13 * ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hT : ∀ k ∈ Finset.range m, 0 ≤ e k / ((m : ℝ) - k) ^ 2 := fun k _ =>
    div_nonneg (he0 k) (sq_nonneg _)
  have htw : ∀ l, l + 1 < m → tw m l = 1 / ((m : ℝ) - l - 1) := fun l hl => by
    rw [tw, if_pos hl]
  -- the `e` part
  have h1 : ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * e l ≤
      4 * ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun l hl => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.sub_le m 1))
        fun k hk _ => by have := hT k hk; positivity)
    have hl : l + 1 < m := by have := Finset.mem_range.1 hl; omega
    have hlR : (l : ℝ) + 2 ≤ m := by exact_mod_cast hl
    rw [htw l hl, div_pow, one_pow, one_div_mul_eq_div]
    have ha : (0 : ℝ) < ((m : ℝ) - l) ^ 2 := pow_pos (by linarith only [hlR]) 2
    have hb : (0 : ℝ) < ((m : ℝ) - l - 1) ^ 2 := pow_pos (by linarith only [hlR]) 2
    have key : ((m : ℝ) - l) ^ 2 ≤ 4 * ((m : ℝ) - l - 1) ^ 2 := by nlinarith only [hlR]
    rw [div_le_iff₀ hb]
    have hq : 0 ≤ e l / ((m : ℝ) - l) ^ 2 := div_nonneg (he0 l) ha.le
    calc e l = e l / ((m : ℝ) - l) ^ 2 * ((m : ℝ) - l) ^ 2 := (div_mul_cancel₀ _ ha.ne').symm
      _ ≤ e l / ((m : ℝ) - l) ^ 2 * (4 * ((m : ℝ) - l - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left key hq
      _ = 4 * (e l / ((m : ℝ) - l) ^ 2) * ((m : ℝ) - l - 1) ^ 2 := by ring
  -- the `e'` part
  have h2 : ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * e' l ≤
      G / ((m : ℝ) - 1) ^ 2 + 9 * ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2 := by
    obtain ⟨n, hn⟩ : ∃ n, m - 1 = n + 1 := ⟨m - 2, by omega⟩
    rw [hn, Finset.sum_range_succ']
    have hz : tw m 0 ^ 2 * e' 0 ≤ G / ((m : ℝ) - 1) ^ 2 := by
      rw [htw 0 (by omega)]
      simp only [Nat.cast_zero, sub_zero, div_pow, one_pow]
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right he'0 (sq_nonneg _)
    have hs : ∑ j ∈ Finset.range n, tw m (j + 1) ^ 2 * e' (j + 1) ≤
        9 * ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2 := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun j hj => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          fun k hk _ => by have := hT k hk; positivity)
      have hj' : j + 1 + 1 < m := by have := Finset.mem_range.1 hj; omega
      have hjR : (j : ℝ) + 3 ≤ m := by exact_mod_cast hj'
      rw [he', htw _ hj', div_pow, one_pow, one_div_mul_eq_div]
      push_cast
      have ha : (0 : ℝ) < ((m : ℝ) - j) ^ 2 := pow_pos (by linarith only [hjR]) 2
      have hb : (0 : ℝ) < ((m : ℝ) - (j + 1) - 1) ^ 2 := pow_pos (by linarith only [hjR]) 2
      have key : ((m : ℝ) - j) ^ 2 ≤ 9 * ((m : ℝ) - (j + 1) - 1) ^ 2 := by nlinarith only [hjR]
      rw [div_le_iff₀ hb]
      have hq : 0 ≤ e j / ((m : ℝ) - j) ^ 2 := div_nonneg (he0 j) ha.le
      calc e j = e j / ((m : ℝ) - j) ^ 2 * ((m : ℝ) - j) ^ 2 := (div_mul_cancel₀ _ ha.ne').symm
        _ ≤ e j / ((m : ℝ) - j) ^ 2 * (9 * ((m : ℝ) - (j + 1) - 1) ^ 2) :=
            mul_le_mul_of_nonneg_left key hq
        _ = 9 * (e j / ((m : ℝ) - j) ^ 2) * ((m : ℝ) - (j + 1) - 1) ^ 2 := by ring
    linarith
  have hsplit : ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * (e' l + e l) =
      ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * e' l +
        ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * e l := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsplit]
  linarith

end C5t
end ItoLib

-- ===== CP =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5u
/-! CORE route, s28: explicit O(T) form of the tracking estimate (T = m h). -/

/-- Pure arithmetic behind `track_final`. -/
theorem track_arith {r h L dd G E V p δ : ℝ} (hr : 2 ≤ r) (hh : 0 ≤ h) (hL : 0 ≤ L) (hd : 0 ≤ dd)
    (hG : 0 ≤ G) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hV : V ≤ G / (r - 1) ^ 2 + 13 * (G * E / r))
    (hp : (δ / (2 * r)) ^ 2 * p ≤ (6 * dd * h * L ^ 2 + (r - 1) * h ^ 2 * L ^ 2 / 2) * V) :
    p ≤ 4 * G * (1 + 13 * E) * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) / δ ^ 2 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr1 : 0 < r - 1 := by linarith only [hr]
  set C1 := 6 * dd * h * L ^ 2 + (r - 1) * h ^ 2 * L ^ 2 / 2 with hC1
  have hC1n : 0 ≤ C1 := by positivity
  have f1 : r ^ 2 / (r - 1) ^ 2 ≤ 2 * r := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ r * (2 * r - 1) * (r - 2) :=
      mul_nonneg (mul_nonneg hr0.le (by linarith)) (by linarith)
    have h2 : 2 * r * (r - 1) ^ 2 - r ^ 2 = r * (2 * r - 1) * (r - 2) := by ring
    linarith only [h1, h2]
  have f2 : r ^ 2 * (r - 1) / (r - 1) ^ 2 ≤ r ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ r ^ 2 * (r - 1) * (r - 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg r) hr1.le) (by linarith)
    have h2 : r ^ 2 * (r - 1) ^ 2 - r ^ 2 * (r - 1) = r ^ 2 * (r - 1) * (r - 2) := by ring
    linarith only [h1, h2]
  have k1 : r ^ 2 * C1 * (G / (r - 1) ^ 2) =
      G * (6 * dd * h * L ^ 2) * (r ^ 2 / (r - 1) ^ 2) +
        G * (h ^ 2 * L ^ 2 / 2) * (r ^ 2 * (r - 1) / (r - 1) ^ 2) := by
    rw [hC1]; ring
  have k1' : r ^ 2 * C1 * (G / (r - 1) ^ 2) ≤ G * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) := by
    rw [k1]
    have a1 : 0 ≤ G * (6 * dd * h * L ^ 2) := by positivity
    have a2 : 0 ≤ G * (h ^ 2 * L ^ 2 / 2) := by positivity
    have m1 := mul_le_mul_of_nonneg_left f1 a1
    have m2 := mul_le_mul_of_nonneg_left f2 a2
    have dif : G * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) -
        (G * (6 * dd * h * L ^ 2) * (2 * r) + G * (h ^ 2 * L ^ 2 / 2) * r ^ 2) =
        G * (L * r * h) ^ 2 / 2 := by ring
    have : 0 ≤ G * (L * r * h) ^ 2 / 2 := by positivity
    linarith only [m1, m2, dif, this]
  have k2 : r ^ 2 * C1 * (13 * (G * E / r)) =
      13 * G * E * (6 * dd * L ^ 2 * (r * h) + (r - 1) * r * h ^ 2 * L ^ 2 / 2) := by
    rw [hC1]; field_simp <;> ring
  have k2' : r ^ 2 * C1 * (13 * (G * E / r)) ≤
      13 * E * G * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) := by
    rw [k2]
    have dif : 13 * E * G * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) -
        13 * G * E * (6 * dd * L ^ 2 * (r * h) + (r - 1) * r * h ^ 2 * L ^ 2 / 2) =
        13 * G * E * (6 * dd * L ^ 2 * (r * h) + L ^ 2 * r * h ^ 2 * (r + 1) / 2) := by ring
    have : 0 ≤ 13 * G * E * (6 * dd * L ^ 2 * (r * h) + L ^ 2 * r * h ^ 2 * (r + 1) / 2) := by
      positivity
    linarith only [dif, this]
  have e0 : (δ / (2 * r)) ^ 2 = δ ^ 2 / (4 * r ^ 2) := by rw [div_pow, mul_pow]; norm_num
  have e : δ ^ 2 * p = 4 * r ^ 2 * ((δ / (2 * r)) ^ 2 * p) := by
    rw [e0]; field_simp
  have hpp : δ ^ 2 * p ≤ 4 * (r ^ 2 * C1 * V) := by
    calc δ ^ 2 * p = 4 * r ^ 2 * ((δ / (2 * r)) ^ 2 * p) := e
      _ ≤ 4 * r ^ 2 * (C1 * V) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 4 * (r ^ 2 * C1 * V) := by ring
  have hCV : r ^ 2 * C1 * V ≤ r ^ 2 * C1 * (G / (r - 1) ^ 2) + r ^ 2 * C1 * (13 * (G * E / r)) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hV (by positivity)
  rw [le_div_iff₀ (by positivity)]
  have fin : 4 * (G * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) +
      13 * E * G * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2)) =
      4 * G * (1 + 13 * E) * (12 * dd * L ^ 2 * (r * h) + L ^ 2 * (r * h) ^ 2) := by ring
  have : p * δ ^ 2 = δ ^ 2 * p := by ring
  linarith only [hpp, hCV, k1', k2', fin, this]

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0}

/-- Tracking estimate, explicit form: with `T = m h`, `E = (1 + 13 c h)^m`, `c = 2L + L^2 + 6dL^2`,
`P(∃ k ≤ m-1, δ ≤ ‖D_k - ((m-k)/m) D_0‖) ≤ 4 G (1 + 13 E) (12 d L^2 T + L^2 T^2) / δ^2`. -/
theorem track_final [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hW : IsStandardBrownian P W) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (hm2 : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G) :
    P.real {ω | ∃ k ≤ m - 1, δ ≤ ‖tD s₁ b₁ J m W h q₀ k ω -
        (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω‖} ≤
      4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
        (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 := by
  have hTB := track_bound W h q₀ hW hh hh1 hs hb hJm hJ hL hSg hLg hm2 hδ
  have hDL := crec_diff_memLp (m := m) hW 0 hh hh1 hs hb hJm hJ hL hSg hLg q₀
  have hCB := (crec_diff_bounds (m := m) hW 0 hh hh1 hs hb hJm hJ hL hSg hLg q₀
    (by omega) hG1 hG2).2
  set e : ℕ → ℝ := fun k => ∫ ω, ‖tD s₁ b₁ J m W h q₀ k ω‖ ^ 2 ∂P with he
  set e' : ℕ → ℝ := fun k => ∫ ω, ‖tD' s₁ b₁ J m W h q₀ k ω‖ ^ 2 ∂P with he'
  have hsum : ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 *
      ∫ ω, (‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2 + ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) ∂P =
      ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * (e' l + e l) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ m := by simp at hl; omega
    have i1 : Integrable (fun ω => ‖tD' s₁ b₁ J m W h q₀ l ω‖ ^ 2) P :=
      integrable_norm_sq_of_coords (hDL l hl').1
    have i2 : Integrable (fun ω => ‖tD s₁ b₁ J m W h q₀ l ω‖ ^ 2) P :=
      integrable_norm_sq_of_coords (hDL l hl').2
    rw [he, he', integral_add i1 i2]
  have hV := track_V_le hm2 e e' (fun k => integral_nonneg fun ω => by positivity)
    (by
      simp only [he', tD]
      change ∫ ω, ‖q₀.1.1 - q₀.2.1‖ ^ 2 ∂P ≤ G
      rw [integral_const]; simpa using hG1)
    (fun k => rfl)
  rw [hsum] at hTB
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hTB
  have hGn : 0 ≤ G := le_trans (by positivity) hG1
  set E := (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m with hE
  have hEn : 0 ≤ E := by rw [hE]; apply pow_nonneg; positivity
  have hsum2 : ∑ k ∈ Finset.range m, e k / ((m : ℝ) - k) ^ 2 ≤ G * E / m := hCB
  refine track_arith (r := (m : ℝ)) (h := (h : ℝ)) hmR h.2 hL (Nat.cast_nonneg d) hGn hEn hδ
    (V := ∑ l ∈ Finset.range (m - 1), tw m l ^ 2 * (e' l + e l)) ?_ hTB
  linarith

end C5u
end ItoLib

-- ===== CQ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5v
/-! CORE route, s28: discrete Girsanov for PATH events. The law of the plain path from `q₀.2` on a
path set `Ap` is at least `e^{-a}` times the probability that the STEERED path `Ŷ_k = (cq k).2.2`
lies in `Ap`, minus the entropy term. -/

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5v
end ItoLib

-- ===== CR =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5w
/-! CORE route, s28: finite-`h` lower bound for the plain chain from `q₀.2` on the PATH event
"ends in `A` and stays in `Bx`", in terms of the chain from `q₀.1` ending in `B` (`B` sits `ε` inside
`A`; `Bx` contains the `2δ`-neighbourhood of the segment from `q₀.1.2` to `q₀.2.2`). -/

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5w
end ItoLib

-- ===== CJ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5b
/-! CORE route C5b (s25): two Euler chains whose coefficients agree on a set `N` coincide as long
as one of them stays in `N` (used to replace the ball-localised coefficients of
`euler_close_tendsto` by the nondegenerate `σ ∘ π_N` of the steering). -/

variable {d : ℕ}

end C5b

end ItoLib

-- ===== CS =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5x
/-! CORE route, s28: transfer of `steer_lower_box` (stated for the box coefficients `s₂, b₂`)
to coefficients `s₁, b₁` that agree with `s₂, b₂` on the box `N`. -/

variable {d : ℕ}

variable {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5x
end ItoLib

-- ===== CT =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5y
/-! CORE route, s28 (C5e): the `h → 0` limit. The chains of `steer_lower_s1` are compared with the
SDE solutions through `euler_close_tendsto`; the result is a minorisation of `P(X^y_T ∈ F)` by
`P(X^x_T ∈ F_{4ρ})` (`F_r = {z | ball z r ⊆ F}`) up to explicit errors that are small for small `T`. -/

variable {d : ℕ}

end C5y
end ItoLib

-- ===== CU =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5z
/-! CORE route, s28 (C5f, first half): `ρ → 0` in `core_minor` turns `F_{4ρ}` into `interior F`. -/

variable {d : ℕ}

end C5z
end ItoLib

-- ===== CV =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5fa
/-! CORE route, s29 (C5f-a): `R → ∞` in `core_minor_int` with a truncation family `s₁ R, b₁ R`. -/

variable {d : ℕ}

end C5fa
end ItoLib


-- ===== CA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CA (CORE route, s22): measure-theoretic transfer lemmas for the Euler-limit minorization.
A lower bound `c L(int F) ≤ μ F + η` on closed sets (what a weak/in-probability limit gives)
upgrades to all Borel sets, and a common lower bound of two probability measures bounds their
total variation distance. -/

end ItoLib

-- ===== CW =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5fb
/-! CORE route, s29 (C5f-b): the closed-set minorisation of `core_minor_lim` gives a TV overlap
of the two time-`T` laws. -/

variable {d : ℕ}

end C5fb
end ItoLib

-- ===== CX =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5g
/-! CORE route, s29 (C5g): instantiation for the Kolmogorov model. For a box `[α, β]ⁿ` with
`α > 0` and every small `T > 0`, the time-`T` laws from any two points of the box overlap. -/

open StochKolmogorov.Persist

variable {n : ℕ}

end C5g
end ItoLib


-- ===== QA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

noncomputable def hm (m : ℕ) : ℝ≥0 := 1 / 2 ^ m

end QA
end ItoLib

-- ===== QB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

end QB
end ItoLib

-- ===== QC =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QC
end ItoLib

-- ===== QD =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QD

end ItoLib

-- ===== QE =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

end QEface

end ItoLib

-- ===== QF =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

-- ===== QG =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

end QG

end ItoLib

-- ===== QH =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QH

end ItoLib

-- ===== QI =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QI
end ItoLib

-- ===== QJ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QJan
/-! Clause 1 toolkit (E4, part 1): analysis helpers. -/

end QJan

section QJ
/-! Clause 1 toolkit (E4, part 1): the continuous Ito integral as a function, and the Picard map. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QJ
end ItoLib

-- ===== QK =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QKan

end QKan

section QK
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QK
end ItoLib

-- ===== QL =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QL
/-! Clause 1 toolkit (E4, part 3): initial bound and the Picard moment bound. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QL
end ItoLib

-- ===== QM =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QM
/-! Clause 1 toolkit (E4, part 4): Borel–Cantelli for the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QM
end ItoLib

-- ===== QN =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Nat
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QN
/-! Clause 1 toolkit (E4, part 5): almost-sure geometric convergence of the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QN
end ItoLib

-- ===== QO =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QO
/-! Clause 1 toolkit (E4, part 6): the Picard limit process. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QO
end ItoLib

-- ===== QP =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QP
/-! Clause 1 toolkit (E4, part 7): the Picard limit solves the SDE (bounded Lipschitz case). -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QP
end ItoLib

-- ===== QZ4 =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QZ4
/-! Clause 1 toolkit (E4, final): strong existence for bounded globally Lipschitz coefficients. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QZ4
end ItoLib

-- ===== E5A =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5A
/-! Clause 1 toolkit (E5, part 1): two solutions from the same point, of SDEs whose bounded
coefficients agree on a ball, coincide as long as the first stays in a smaller ball. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5A

end ItoLib

-- ===== E5B =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5B
/-! Clause 1 toolkit (E5, part 2): gluing a consistent, non-exploding family of truncated
solutions into a global strong solution. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5B

end ItoLib

-- ===== HB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HB (Harris route, s30): iterates of a Markov kernel, drift iteration, and the TV-Cauchy
estimate for `kpow κ k x` coming from `hm_iterate` (HA). -/

section HB
variable {X : Type*} [MeasurableSpace X]

end HB
end ItoLib

-- ===== F41e =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41e
/-! F41e (eq_4_1 work, 986b9ae0, 2026-10-30): generic tools for the face overlap (E3):
integrand congruence, constant integrands, masked vectors, the face projection. -/

variable {n : ℕ}
open StochKolmogorov.Persist

end F41e
end ItoLib

-- ===== F41f =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41f
/-! F41f (eq_4_1 work, 986b9ae0, 2026-10-30): the lift of a face solution to a nondegenerate
`n`-dimensional SDE (additive noise in the coordinates off the face) and the face overlap. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end F41f
end ItoLib

-- ===== F41g =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41g
/-! F41g (eq_4_1 work, 986b9ae0, 2026-10-30): the face overlap property (E3) through the lifted
nondegenerate SDE and `core_tv`, and eq_4_1 without extra hypotheses. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end F41g
end ItoLib

namespace ItoLib
open EthierKurtz
theorem tf_bridge {Ω : Type*} {d : ℕ} {W : ℝ≥0 → Ω → SDEState d} 
    {h : ℝ≥0} 
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} 
    
    
    
    {m : ℕ}  (ξ ζ : ℕ → Ω → Fin d → ℝ)
    (hξ : ∀ l ω j, ξ l ω j = W (((l : ℝ) * h).toNNReal + h) ω j - W ((l : ℝ) * h).toNNReal ω j)
    (hζ : ∀ l ω j, ζ l ω j = (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h,
      (W (((l : ℝ) * h).toNNReal + h) ω j - W (((l : ℝ) * h).toNNReal + u.toNNReal) ω j))
    (Z : SDEState d × SDEState d → (Fin d → ℝ) → (Fin d → ℝ) → SDEState d)
    (hZ : ∀ p a c, Z p a c = p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * a j +
      (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * c j) + (h : ℝ) / 2 * (b₁ p.1 i + b₁ p.2 i)))
    (Q : ℕ → Ω → (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hQ0 : ∀ ω, Q 0 ω = q₀)
    (U : ℕ → Ω → Fin d → ℝ)
    (hU : ∀ k ω, U k ω = if k < m then
      J (Q k ω).2 ((1 / ((m : ℝ) - k)) • ((Q k ω).1.2 - (Q k ω).2.2)) else 0)
    (hQ : ∀ k ω, Q (k + 1) ω = (((Q k ω).1.2, Z (Q k ω).1 (ξ k ω) (ζ k ω)),
      ((Q k ω).2.2, Z (Q k ω).2 (ξ k ω + U k ω) (ζ k ω + fun j => U k ω j / 2))))
 :
    ∀ k ω, Q k ω = cq s₁ b₁ J m W h q₀ k ω := by
  have hZ' : ∀ p a c, Z p a c = zstep s₁ b₁ (h : ℝ) p (a, c) := fun p a c => by rw [hZ]; rfl
  intro k
  induction k with
  | zero => intro ω; rw [hQ0]; rfl
  | succ k ih =>
    intro ω
    have e1 : ξ k ω = (noiseAt W h 0 ω k).1 := funext fun j => by
      rw [hξ]; simp only [noiseAt, Nat.zero_add]
    have e2 : ζ k ω = (noiseAt W h 0 ω k).2 := funext fun j => by
      rw [hζ]; simp only [noiseAt, cellZeta, zetaF, Nat.zero_add]
    have e3 : U k ω = steer J m k (cq s₁ b₁ J m W h q₀ k ω) := by rw [hU, ih]; rfl
    rw [hQ, e1, e2, e3, ih, hZ', hZ']
    rfl
end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open EthierKurtz in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs : Continuous s₁) (hb : Continuous b₁)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} (hJm : Measurable (Function.uncurry J))
    (hJ : ∀ p v, WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * J p v j) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {m : ℕ} (hm2 : 2 ≤ m) (ξ ζ : ℕ → Ω → Fin d → ℝ)
    (hξ : ∀ l ω j, ξ l ω j = W (((l : ℝ) * h).toNNReal + h) ω j - W ((l : ℝ) * h).toNNReal ω j)
    (hζ : ∀ l ω j, ζ l ω j = (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h,
      (W (((l : ℝ) * h).toNNReal + h) ω j - W (((l : ℝ) * h).toNNReal + u.toNNReal) ω j))
    (Z : SDEState d × SDEState d → (Fin d → ℝ) → (Fin d → ℝ) → SDEState d)
    (hZ : ∀ p a c, Z p a c = p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * a j +
      (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * c j) + (h : ℝ) / 2 * (b₁ p.1 i + b₁ p.2 i)))
    (Q : ℕ → Ω → (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hQ0 : ∀ ω, Q 0 ω = q₀)
    (U : ℕ → Ω → Fin d → ℝ)
    (hU : ∀ k ω, U k ω = if k < m then
      J (Q k ω).2 ((1 / ((m : ℝ) - k)) • ((Q k ω).1.2 - (Q k ω).2.2)) else 0)
    (hQ : ∀ k ω, Q (k + 1) ω = (((Q k ω).1.2, Z (Q k ω).1 (ξ k ω) (ζ k ω)),
      ((Q k ω).2.2, Z (Q k ω).2 (ξ k ω + U k ω) (ζ k ω + fun j => U k ω j / 2))))
    {δ : ℝ} (hδ : 0 < δ) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G) :
    P.real {ω | ∃ k ≤ m - 1, δ ≤ ‖((Q k ω).1.2 - (Q k ω).2.2) -
        (((m : ℝ) - k) / m) • ((Q 0 ω).1.2 - (Q 0 ω).2.2)‖} ≤
      4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
        (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2
 := by
  have hbr := ItoLib.tf_bridge ξ ζ hξ hζ Z hZ Q q₀ hQ0 U hU hQ
  have key := ItoLib.track_final (m := m) (J := J) hW hh hh1 hs hb hJm hJ hL hSg hLg q₀ hm2 hδ hG1 hG2
  have hset : {ω | ∃ k ≤ m - 1, δ ≤ ‖((Q k ω).1.2 - (Q k ω).2.2) -
        (((m : ℝ) - k) / m) • ((Q 0 ω).1.2 - (Q 0 ω).2.2)‖} =
      {ω | ∃ k ≤ m - 1, δ ≤ ‖ItoLib.tD s₁ b₁ J m W h q₀ k ω -
        (((m : ℝ) - k) / m) • ItoLib.tD s₁ b₁ J m W h q₀ 0 ω‖} := by
    ext ω; simp only [Set.mem_setOf_eq, hbr, ItoLib.tD]
  rw [hset]; exact key
