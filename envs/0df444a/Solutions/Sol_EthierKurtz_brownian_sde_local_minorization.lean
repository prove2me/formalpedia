-- Prove2me | solution 1 for EthierKurtz.brownian_sde_local_minorization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T00:11:18.316777+00:00
-- url     : https://prove2.me/submissions/14bde541-33ce-46aa-8ac4-706ba3848dcd

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
import Theorems.Thm_EthierKurtz_steered_euler_coupling_lower_box
import Theorems.Thm_EthierKurtz_euler_chain_close_in_probability
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

/-- Smooth cutoff: `1` on `(-∞, r]`, `0` on `[r+1, ∞)`, values in `[0,1]`. -/
noncomputable def cutoff (r : ℝ) (x : ℝ) : ℝ := Real.smoothTransition (r + 1 - x)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

def ixc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.castAdd d k)
def iyc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.natAdd d k)
def iac : Fin (d + d + 1) := Fin.last _

/-- `Q(u) = |x - y|²`. -/
noncomputable def Qf (u : SDEState (d + d + 1)) : ℝ := ∑ k, (u (ixc k) - u (iyc k)) ^ 2
/-- `N(u) = |x|² + |y|²`. -/
noncomputable def Nf (u : SDEState (d + d + 1)) : ℝ := ∑ k, (u (ixc k) ^ 2 + u (iyc k) ^ 2)
/-- Cut-off test function `e^{-a} χ_r(|x|²+|y|²) |x-y|²`. -/
noncomputable def Ff (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nf u) * Qf u)

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

/-- `(x, y, a) ↦ u` with `u (ixc k) = x k`, `u (iyc k) = y k`, `u iac = a`. -/
noncomputable def pack (x y : SDEState d) (a : ℝ) : SDEState (d + d + 1) :=
  WithLp.toLp 2 (fun i => Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j) i)

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

/-- Column `j` of a diffusion matrix. -/
noncomputable def scol (s : SDEDiffusion d) (j : Fin d) : SDEState d :=
  WithLp.toLp 2 (fun k => s (k, j))

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

/-- Distance of `x` from the closed ball of radius `R`. -/
noncomputable def distB (R : ℝ) (x : SDEState d) : ℝ := max 0 (‖x‖ - R)

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

noncomputable def psiQ (q : ℝ) : ℝ := 1 - (1 - Real.smoothTransition (q / 4)) * Real.exp (-q)

/-- `|x|²` read off the `x`-block. -/
noncomputable def Nxf (u : SDEState (d + d + 1)) : ℝ := ∑ k, u (ixc k) ^ 2

/-- Test function `e^{-a} χ_r(|x|²) ψ(|x-y|²)`. -/
noncomputable def Gf (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nxf u) * psiQ (Qf u))

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

/-- Generator of `Gf r` along `(X, Y, A)` with coefficient values `σx, bx`, `σy, by'`. -/
noncomputable def driftH (r κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) : ℝ :=
  fderiv ℝ (Gf r) (pack x y a) (pack bx by' κ) +
    (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ (Gf r)) (pack x y a)
      (pack (scol σx j) (scol σy j) 0) (pack (scol σx j) (scol σy j) 0)

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

/-- Clock rate penalising only `X` outside `B_R`. -/
noncomputable def kapX (c M R : ℝ) (x : SDEState d) : ℝ := c + M * distB R x

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

variable (s₁ b₁ h w) in
/-- The diffusion integrand of the scheme as a matrix. -/
noncomputable def eulerHM (a y : SDEState d) (u : ℝ) : SDEDiffusion d :=
  WithLp.toLp 2 fun p : Fin d × Fin d => eulerH s₁ b₁ h w a y p.1 p.2 u

variable (s₁ b₁ h w) in
/-- The drift of the scheme as a vector. -/
noncomputable def eulerBV (a y : SDEState d) (u : ℝ) : SDEState d :=
  WithLp.toLp 2 fun i => eulerB s₁ b₁ h w a y i u

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

/-- Coefficient-error integrand of the scheme. -/
noncomputable def eulerErr (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
    (h C : ℝ) (W : ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d) (s : ℝ≥0) (ω : Ω) : ℝ :=
  C * (‖b₁ (eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ s) - eulerBV s₁ b₁ h (fun s => W s ω) x₀ x₀ s‖ ^ 2 +
    ‖s₁ (eulerY s₁ b₁ h (fun s => W s ω) x₀ x₀ s) - eulerHM s₁ b₁ h (fun s => W s ω) x₀ x₀ s‖ ^ 2)

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

theorem coord_abs_le_diff (A : SDEDiffusion d) (p : Fin d × Fin d) : |A p| ≤ ‖A‖ := by
  have := PiLp.norm_apply_le A p; rwa [Real.norm_eq_abs] at this

theorem integrable_norm_sq_of_coords [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → SDEState d}
    (hf : ∀ i, MemLp (fun ω => f ω i) 2 P) : Integrable (fun ω => ‖f ω‖ ^ 2) P := by
  simp_rw [state_norm_sq]
  exact integrable_finsetSum _ fun i _ => (hf i).integrable_sq

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

/-- The restart function `G(a, y) = E f(Z_k)` of the Euler scheme started from `(a, y)`. -/
noncomputable def eulerG (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (f : SDEState d → ℝ)
    (h : ℝ) (k : ℕ) (a y : SDEState d) : ℝ :=
  ∫ ω, f (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 ∂P

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

noncomputable def mneg (v : ℝ) : ℝ := max (-v) 0

/-- `φ(v) = (v⁻)³`. -/
noncomputable def phi3 (v : ℝ) : ℝ := mneg v ^ 3

variable {d : ℕ}

/-- `Φ(u) = Σ_k φ(x_k)`. -/
noncomputable def Phif (u : SDEState (d + d + 1)) : ℝ := ∑ k, phi3 (u (ixc k))

/-- Orthant test function `e^{-a} χ_r(|x|²) Φ`. -/
noncomputable def Hf (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nxf u) * Phif u)

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

/-- Cameron-Martin weight of a shift by `a` for `N(0, v)`. -/
noncomputable def cmw (v : ℝ≥0) (a x : ℝ) : ℝ := Real.exp (-(a * x) / v - a ^ 2 / (2 * v))

/-- Multi-dimensional weight. -/
noncomputable def cmwPi {ι : Type*} [Fintype ι] (v : ι → ℝ≥0) (a x : ι → ℝ) : ℝ :=
  ∏ i, cmw (v i) (a i) (x i)

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

/-- Linear map from dyadic increments to the dyadic approximation of the cell noise. -/
noncomputable def psiN (h : ℝ≥0) (n : ℕ) (D : Fin d × Fin (2 ^ n) → ℝ) : Fin 1 → Noise d :=
  fun _ => (fun j => ∑ i : Fin (2 ^ n), D (j, i),
    fun j => (1 / (h : ℝ)) * ((∑ r : Fin (2 ^ n), ∑ i : Fin (2 ^ n),
      (if (r : ℕ) ≤ (i : ℕ) then D (j, i) else 0)) * ((h / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)))

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

/-- Shift of a noise block by an adapted drift `U`. -/
noncomputable def shV (U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)) {k : ℕ} (v : Fin k → Noise d) :
    Fin k → Noise d :=
  fun l => v l + (U l (extN v), fun j => U l (extN v) j / 2)

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

/-- The steering drift as an adapted functional of the noise sequence. -/
noncomputable def steerN (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (l : ℕ)
    (N : ℕ → Noise d) : Fin d → ℝ :=
  steer J m l (crec s₁ b₁ h J m N l q₀)

variable {s₁ b₁ h J m}

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

variable (s₁ b₁ J m) in
/-- The coupled chain driven by the cells `0, 1, ...` of `W`. -/
noncomputable def cq (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (k : ℕ) (ω : Ω) :
    (SDEState d × SDEState d) × (SDEState d × SDEState d) :=
  crec s₁ b₁ (h : ℝ) J m (noiseAt W h 0 ω) k q₀

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

/-- Martingale increment of the Euler chain on one cell. -/
noncomputable def mInc (s₁ : SDEState d → SDEDiffusion d) (p : SDEState d × SDEState d)
    (n : Noise d) : SDEState d :=
  WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * n.1 j + (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * n.2 j))

/-- Martingale part of the chain. -/
noncomputable def mpart (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
    (h : ℝ) (N : ℕ → Noise d) (k : ℕ) (p : SDEState d × SDEState d) : SDEState d :=
  ∑ l ∈ Finset.range k, mInc s₁ (zrec s₁ b₁ h N l p) (N l)

/-- Drift part of the chain. -/
noncomputable def dpart (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
    (h : ℝ) (N : ℕ → Noise d) (k : ℕ) (p : SDEState d × SDEState d) : SDEState d :=
  ∑ l ∈ Finset.range k, (h / 2) • (b₁ (zrec s₁ b₁ h N l p).1 + b₁ (zrec s₁ b₁ h N l p).2)

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem zstep_split (h : ℝ) (p : SDEState d × SDEState d) (n : Noise d) :
    zstep s₁ b₁ h p n = p.2 + mInc s₁ p n + (h / 2) • (b₁ p.1 + b₁ p.2) := by
  ext i
  simp [zstep, mInc]
  ring

theorem zrec_decomp (h : ℝ) (N : ℕ → Noise d) (p : SDEState d × SDEState d) (k : ℕ) :
    (zrec s₁ b₁ h N k p).2 = p.2 + mpart s₁ b₁ h N k p + dpart s₁ b₁ h N k p := by
  induction k with
  | zero => simp [zrec, mpart, dpart]
  | succ k ih =>
    show zstep s₁ b₁ h (zrec s₁ b₁ h N k p) (N k) = _
    rw [zstep_split]
    simp only [mpart, dpart] at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    generalize zrec s₁ b₁ h N k p = z at ih ⊢
    rw [ih]
    abel

theorem dpart_norm_le {h S : ℝ} (hh : 0 ≤ h) (hb : ∀ x, ‖b₁ x‖ ≤ S) (N : ℕ → Noise d) (k : ℕ)
    (p : SDEState d × SDEState d) : ‖dpart s₁ b₁ h N k p‖ ≤ k * (h * S) := by
  unfold dpart
  refine (norm_sum_le _ _).trans ?_
  have hl : ∀ l ∈ Finset.range k,
      ‖(h / 2) • (b₁ (zrec s₁ b₁ h N l p).1 + b₁ (zrec s₁ b₁ h N l p).2)‖ ≤ h * S := by
    intro l _
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_add_le (b₁ (zrec s₁ b₁ h N l p).1) (b₁ (zrec s₁ b₁ h N l p).2)
    have h2 := hb (zrec s₁ b₁ h N l p).1
    have h3 := hb (zrec s₁ b₁ h N l p).2
    nlinarith
  refine (Finset.sum_le_sum hl).trans ?_
  simp [Finset.sum_const, nsmul_eq_mul]

theorem mInc_continuous (hs : Continuous s₁) :
    Continuous fun q : (SDEState d × SDEState d) × Noise d => mInc s₁ q.1 q.2 := by
  have hp1 : Continuous fun q : (SDEState d × SDEState d) × Noise d => q.1.1 :=
    continuous_fst.comp continuous_fst
  have hp2 : Continuous fun q : (SDEState d × SDEState d) × Noise d => q.1.2 :=
    continuous_snd.comp continuous_fst
  have hsc : ∀ p : Fin d × Fin d, ∀ {g : (SDEState d × SDEState d) × Noise d → SDEState d},
      Continuous g → Continuous fun q => s₁ (g q) p := fun p g hg =>
    (EuclideanSpace.proj p).continuous.comp (hs.comp hg)
  have hn1 : ∀ j : Fin d, Continuous fun q : (SDEState d × SDEState d) × Noise d => q.2.1 j :=
    fun j => (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  have hn2 : ∀ j : Fin d, Continuous fun q : (SDEState d × SDEState d) × Noise d => q.2.2 j :=
    fun j => (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine continuous_finsetSum _ fun j _ => ?_
  have e1 : Continuous fun q : (SDEState d × SDEState d) × Noise d => s₁ q.1.1 (i, j) :=
    hsc (i, j) hp1
  have e2 : Continuous fun q : (SDEState d × SDEState d) × Noise d => s₁ q.1.2 (i, j) :=
    hsc (i, j) hp2
  exact (e1.mul (hn1 j)).add ((e2.sub e1).mul (hn2 j))

theorem mpart_continuous {h : ℝ} (hs : Continuous s₁) (hb : Continuous b₁) (k : ℕ)
    (p : SDEState d × SDEState d) :
    Continuous fun N : ℕ → Noise d => mpart s₁ b₁ h N k p := by
  unfold mpart
  refine continuous_finsetSum _ fun l _ => ?_
  have hz : Continuous fun N : ℕ → Noise d => zrec s₁ b₁ h N l p :=
    (zrec_continuous hs hb l).comp (continuous_id.prodMk continuous_const)
  exact (mInc_continuous hs).comp (hz.prodMk (continuous_apply l))

theorem mpart_congr {h : ℝ} {N N' : ℕ → Noise d} (k : ℕ) (hN : ∀ l < k, N l = N' l)
    (p : SDEState d × SDEState d) : mpart s₁ b₁ h N k p = mpart s₁ b₁ h N' k p := by
  unfold mpart
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [zrec_congr l (fun j hj => hN j (hj.trans hl')) p, hN l hl']

/-- A continuous functional of the noise that only sees cells `< k` is measurable at time `k h`. -/
theorem noise_fun_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (h : ℝ≥0) (k : ℕ) {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {F : (ℕ → Noise d) → X} (hF : Continuous F)
    (hFk : ∀ N N' : ℕ → Noise d, (∀ l < k, N l = N' l) → F N = F N') :
    Measurable[G ((k : ℝ) * h).toNNReal] fun ω => F (noiseAt W h 0 ω) := by
  let _ : MeasurableSpace Ω := G ((k : ℝ) * h).toNNReal
  have e : (fun ω => F (noiseAt W h 0 ω)) =
      F ∘ (fun ω l => if l < k then noiseAt W h 0 ω l else 0) := by
    funext ω
    exact hFk _ _ (fun l hl => by simp [hl])
  rw [e]
  refine hF.measurable.comp (measurable_pi_lambda _ fun l => ?_)
  by_cases hl : l < k
  · simp only [hl, if_true]
    exact noiseAt_meas_G hG hWc h l (Real.toNNReal_le_toNNReal (by
      have : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      nlinarith [h.2]))
  · simp only [hl, if_false]
    exact measurable_const

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


theorem mInc_noiseAt (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (k : ℕ) (q : SDEState d × SDEState d)
    (ω : Ω) : mInc s₁ q (noiseAt W h 0 ω k) = cellNoise W ((k : ℝ) * h).toNNReal h
      (fun _ => s₁ q.1) (fun _ => s₁ q.2 - s₁ q.1) ω := by
  ext i
  simp [mInc, cellNoise, noiseAt]

theorem mpart_succ_noise (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (k : ℕ)
    (p : SDEState d × SDEState d) (ω : Ω) :
    mpart s₁ b₁ h (noiseAt W h 0 ω) (k + 1) p = mpart s₁ b₁ h (noiseAt W h 0 ω) k p +
      cellNoise W ((k : ℝ) * h).toNNReal h
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1)
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 -
          s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1) ω := by
  rw [mpart, Finset.sum_range_succ, ← mpart, mInc_noiseAt]
  rfl

theorem mpart_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (hs : Continuous s₁) (hb : Continuous b₁) (h : ℝ≥0)
    (k : ℕ) (p : SDEState d × SDEState d) :
    Measurable[G ((k : ℝ) * h).toNNReal] fun ω => mpart s₁ b₁ h (noiseAt W h 0 ω) k p :=
  noise_fun_meas_G hG hWc h k (mpart_continuous hs hb k p) (fun _ _ hN => mpart_congr k hN p)

theorem zrec_meas_G [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
    {G : ℝ≥0 → MeasurableSpace Ω}
    (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (hs : Continuous s₁) (hb : Continuous b₁) (h : ℝ≥0)
    (k : ℕ) (p : SDEState d × SDEState d) :
    Measurable[G ((k : ℝ) * h).toNNReal] fun ω => zrec s₁ b₁ h (noiseAt W h 0 ω) k p :=
  noise_fun_meas_G hG hWc h k ((zrec_continuous hs hb k).comp
    (continuous_id.prodMk continuous_const)) (fun _ _ hN => zrec_congr k hN p)

/-- Data of one cell of the martingale part: past-measurable bounded coefficients. -/
theorem cell_coef_props [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hs : Continuous s₁) (hb : Continuous b₁) {S : ℝ} (hS : ∀ x, ‖s₁ x‖ ≤ S)
    (p : SDEState d × SDEState d) (k : ℕ) :
    (∀ q, Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
      fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1 q) ∧
    (∀ q, Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
      fun ω => (s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 -
        s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1) q) ∧
    (∀ ω, ‖s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1‖ ≤ 2 * S) ∧
    (∀ ω, ‖s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 -
        s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1‖ ≤ 2 * S) := by
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hQ := zrec_meas_G (b₁ := b₁) hG hW.2.1 hs hb h k p
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have b1 : ∀ ω, ‖s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1‖ ≤ 2 * S := fun ω => by
    linarith [hS (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1]
  have b2 : ∀ ω, ‖s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 -
      s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1‖ ≤ 2 * S := fun ω => by
    have := norm_sub_le (s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2)
      (s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1)
    linarith [hS (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1,
      hS (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2]
  refine ⟨fun q => ?_, fun q => ?_, b1, b2⟩
  · let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal
    exact (EuclideanSpace.proj q).continuous.measurable.comp
      (hs.measurable.comp (measurable_fst.comp hQ))
  · let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal
    exact (EuclideanSpace.proj q).continuous.measurable.comp
      ((hs.measurable.comp (measurable_snd.comp hQ)).sub (hs.measurable.comp (measurable_fst.comp hQ)))

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

/-- L² and second moment of the martingale part. -/
theorem mpart_moment [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hs : Continuous s₁) (hb : Continuous b₁) {S : ℝ}
    (hS : ∀ x, ‖s₁ x‖ ≤ S) (p : SDEState d × SDEState d) (k : ℕ) :
    (∀ i, MemLp (fun ω => mpart s₁ b₁ h (noiseAt W h 0 ω) k p i) 2 P) ∧
      ∫ ω, ‖mpart s₁ b₁ h (noiseAt W h 0 ω) k p‖ ^ 2 ∂P ≤ 16 * d * S ^ 2 * (k * h) := by
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  induction k with
  | zero => refine ⟨fun i => ?_, ?_⟩ <;> simp [mpart]
  | succ k ih =>
    obtain ⟨ihL, ihB⟩ := ih
    obtain ⟨hA, hB, hAK, hBK⟩ := cell_coef_props (b₁ := b₁) hW x₀ (h := h) hs hb hS p k
    have hDm := mpart_meas_G (b₁ := b₁) hG hW.2.1 hs hb h k p
    have hDc : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
        fun ω => mpart s₁ b₁ h (noiseAt W h 0 ω) k p i := fun i =>
      (EuclideanSpace.proj i).continuous.measurable.comp hDm
    have step := cellNoise_step hW x₀ _ h hh hDc ihL hA hB hAK hBK
    have hNL := cellNoise_memLp hW x₀ _ h hh hA hB hAK hBK
    simp_rw [mpart_succ_noise]
    refine ⟨fun i => (ihL i).add (hNL i), ?_⟩
    have hI : ∫ ω, (‖s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1‖ ^ 2 +
        ‖s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 -
          s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).1‖ ^ 2) ∂P ≤ 8 * S ^ 2 := by
      calc _ ≤ ∫ _ω, (8 * S ^ 2 : ℝ) ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) (integrable_const _)
              (ae_of_all _ fun ω => by
                have a1 := pow_le_pow_left₀ (norm_nonneg _) (hAK ω) 2
                have a2 := pow_le_pow_left₀ (norm_nonneg _) (hBK ω) 2
                dsimp only
                nlinarith)
        _ = 8 * S ^ 2 := by simp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have k4 := mul_le_mul_of_nonneg_left hI (by positivity : (0 : ℝ) ≤ 2 * d * h)
    push_cast
    nlinarith

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

/-- The orthogonality hypothesis of `kolmogorov_max` for the martingale part. -/
theorem mpart_orth [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hs : Continuous s₁) (hb : Continuous b₁) {S : ℝ}
    (hS : ∀ x, ‖s₁ x‖ ≤ S) (p : SDEState d × SDEState d) (lam : ℝ) {k m : ℕ} (hkm : k ≤ m) :
    ∫ ω in firstHit (fun j ω => mpart s₁ b₁ h (noiseAt W h 0 ω) j p) lam k,
      ⟪mpart s₁ b₁ h (noiseAt W h 0 ω) k p,
        mpart s₁ b₁ h (noiseAt W h 0 ω) m p - mpart s₁ b₁ h (noiseAt W h 0 ω) k p⟫_ℝ ∂P = 0 := by
  set M : ℕ → Ω → SDEState d := fun j ω => mpart s₁ b₁ h (noiseAt W h 0 ω) j p with hMdef
  set F := firstHit M lam k with hFdef
  have hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have hGa : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable fun ω => W r ω j :=
    fun r _ _ j => stdBrownian_coord_measurable hW r j
  have hMa : ∀ j, Measurable (M j) := fun j =>
    mpart_meas_G (G := fun _ => ‹MeasurableSpace Ω›) hGa hW.2.1 hs hb h j p
  have hF : MeasurableSet F := firstHit_measurable hMa lam k
  set tk : ℝ≥0 := ((k : ℝ) * h).toNNReal with htk
  have hFG : MeasurableSet[completedBrownianPast P W (fun _ => x₀) tk] F := by
    have hj' : ∀ j ≤ k, Measurable[completedBrownianPast P W (fun _ => x₀) tk] (M j) :=
      fun j hj => (mpart_meas_G hG hW.2.1 hs hb h j p).mono (completedBrownianPast_mono P W _
        (Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) h.2))) le_rfl
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) tk
    exact firstHit_meas_le hj' lam
  set Y : Ω → SDEState d := F.indicator (M k) with hYdef
  have hYm : Measurable[completedBrownianPast P W (fun _ => x₀) tk] Y := by
    let _ : MeasurableSpace Ω := completedBrownianPast P W (fun _ => x₀) tk
    exact (mpart_meas_G hG hW.2.1 hs hb h k p).indicator hFG
  have hML := (mpart_moment hW x₀ hh hs hb hS p k).1
  have hYc : ∀ i, (fun ω => Y ω i) = F.indicator (fun ω => M k ω i) := fun i => by
    funext ω; by_cases hω : ω ∈ F <;> simp [hYdef, hω]
  have hYL : ∀ i, MemLp (fun ω => Y ω i) 2 P := fun i => by
    rw [hYc i]; exact (hML i).indicator hF
  have hdiff : ∀ ω, M m ω - M k ω = ∑ l ∈ Finset.Ico k m, cellNoise W ((l : ℝ) * h).toNNReal h
      (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1)
      (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).2 -
        s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1) ω := by
    intro ω
    simp only [hMdef, mpart]
    rw [← Finset.sum_Ico_eq_sub _ hkm]
    exact Finset.sum_congr rfl fun l _ => mInc_noiseAt W h l _ ω
  have hind : ∀ ω, F.indicator (fun ω => ⟪M k ω, M m ω - M k ω⟫_ℝ) ω =
      ∑ l ∈ Finset.Ico k m, ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1)
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).2 -
          s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1) ω⟫_ℝ := by
    intro ω
    rw [← inner_sum, ← hdiff ω]
    by_cases hω : ω ∈ F <;> simp [hYdef, hω]
  have hl : ∀ l ∈ Finset.Ico k m, Integrable (fun ω => ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1)
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).2 -
          s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1) ω⟫_ℝ) P ∧
      ∫ ω, ⟪Y ω, cellNoise W ((l : ℝ) * h).toNNReal h
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1)
        (fun ω => s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).2 -
          s₁ (zrec s₁ b₁ h (noiseAt W h 0 ω) l p).1) ω⟫_ℝ ∂P = 0 := fun l hl' => by
    have hkl : k ≤ l := (Finset.mem_Ico.1 hl').1
    obtain ⟨hA, hB, hAK, hBK⟩ := cell_coef_props (b₁ := b₁) hW x₀ (h := h) hs hb hS p l
    have hmono : completedBrownianPast P W (fun _ => x₀) tk ≤
        completedBrownianPast P W (fun _ => x₀) ((l : ℝ) * h).toNNReal :=
      completedBrownianPast_mono P W _ (Real.toNNReal_le_toNNReal
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) h.2))
    refine cell_orth hW x₀ _ h hh (fun i => ?_) hYL hA hB hAK hBK
    exact ((EuclideanSpace.proj i).continuous.measurable.comp hYm).mono hmono le_rfl
  rw [← integral_indicator hF, integral_congr_ae (ae_of_all _ hind),
    integral_finsetSum _ fun l hl' => (hl l hl').1]
  exact Finset.sum_eq_zero fun l hl' => (hl l hl').2

/-- C5c: exit estimate for the Euler chain with bounded coefficients, uniform in the start and
the mesh: `(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/
theorem chain_exit [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hs : Continuous s₁) (hb : Continuous b₁) {S : ℝ}
    (hS : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S) (p : SDEState d × SDEState d) (m : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hT : m * (h * S) ≤ δ / 2) :
    (δ / 2) ^ 2 * P.real {ω | ∃ k ≤ m, δ ≤ ‖(zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 - p.2‖} ≤
      16 * d * S ^ 2 * (m * h) := by
  have hs' : ∀ x, ‖s₁ x‖ ≤ S := fun x => (hS x).1
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hs' 0)
  set M : ℕ → Ω → SDEState d := fun j ω => mpart s₁ b₁ h (noiseAt W h 0 ω) j p with hMdef
  have hGa : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable fun ω => W r ω j :=
    fun r _ _ j => stdBrownian_coord_measurable hW r j
  have hMa : ∀ j, Measurable (M j) := fun j =>
    mpart_meas_G (G := fun _ => ‹MeasurableSpace Ω›) hGa hW.2.1 hs hb h j p
  have hsub : {ω | ∃ k ≤ m, δ ≤ ‖(zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 - p.2‖} ⊆
      {ω | ∃ k ≤ m, δ / 2 ≤ ‖M k ω‖} := by
    rintro ω ⟨k, hk, hδk⟩
    refine ⟨k, hk, ?_⟩
    have e : (zrec s₁ b₁ h (noiseAt W h 0 ω) k p).2 - p.2 =
        M k ω + dpart s₁ b₁ h (noiseAt W h 0 ω) k p := by
      rw [zrec_decomp]; simp only [hMdef]; abel
    have hD := dpart_norm_le (s₁ := s₁) (h := (h : ℝ)) (NNReal.coe_nonneg h) (fun x => (hS x).2)
      (noiseAt W h 0 ω) k p
    have hkm : (k : ℝ) * (h * S) ≤ m * (h * S) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (mul_nonneg (NNReal.coe_nonneg h) hS0)
    rw [e] at hδk
    have := norm_add_le (M k ω) (dpart s₁ b₁ h (noiseAt W h 0 ω) k p)
    linarith
  have hK := kolmogorov_max (μ := P) hMa m
    (fun k _ => integrable_norm_sq_of_coords (mpart_moment hW 0 hh hs hb hs' p k).1)
    (half_pos hδ) (fun k hk => mpart_orth hW 0 hh hs hb hs' p (δ / 2) hk)
  calc _ ≤ (δ / 2) ^ 2 * P.real {ω | ∃ k ≤ m, δ / 2 ≤ ‖M k ω‖} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg _)
    _ ≤ ∫ ω, ‖M m ω‖ ^ 2 ∂P := hK
    _ ≤ 16 * d * S ^ 2 * (m * h) := (mpart_moment hW 0 hh hs hb hs' p m).2

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

/-- Coordinatewise clamp to the box `[α, β]^n`. -/
noncomputable def boxP (α β : ℝ) (x : SDEState n) : SDEState n :=
  WithLp.toLp 2 (fun i => max α (min β (x i)))

open StochKolmogorov.Persist

/-- The diagonal factor of the boxed diffusion. -/
noncomputable def aK (C : Coeffs n) (α β : ℝ) (i : Fin n) (x : SDEState n) : ℝ :=
  boxP α β x i * C.g i (posPart (boxP α β x))

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

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

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

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
  (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)
  (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
  (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))

variable {s₁ b₁ J m}

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

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0}

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

theorem steer_lower_box [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hm2 : 2 ≤ m) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G)
    {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) (ha : 0 < a)
    (hT : m * (h * S) ≤ δ / 2)
    {A B Bx : Set (SDEState d)} (hA : MeasurableSet A) (hBxm : MeasurableSet Bx)
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z,
      ‖z - (q₀.1.2 - t • (q₀.1.2 - q₀.2.2))‖ < 2 * δ → z ∈ Bx) :
    Real.exp (-a) * (P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m q₀.1).2 ∈ B} -
        16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2 -
        4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
          (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m q₀.2).2 ∈ A ∧
        ∀ k ≤ m, (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2 ∈ Bx} := by
  exact EthierKurtz.steered_euler_coupling_lower_box hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ hm2
    (fun l ω => (noiseAt W h 0 ω l).1) (fun l ω => (noiseAt W h 0 ω l).2)
    (fun l ω j => by simp only [noiseAt, Nat.zero_add])
    (fun l ω j => by simp only [noiseAt, cellZeta, zetaF, Nat.zero_add])
    (fun p a c => zstep s₁ b₁ (h : ℝ) p (a, c)) (fun p a c => rfl)
    (fun p k ω => zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k p) (fun p ω => rfl) (fun p k ω => rfl)
    q₀ hG1 hG2 hδ hε hεδ ha hT hA hBxm hB hBx
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

theorem zstep_agree {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    {N : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (h : ℝ)
    (p : SDEState d × SDEState d) (h1 : p.1 ∈ N) (h2 : p.2 ∈ N) (n : Noise d) :
    zstep s₁ b₁ h p n = zstep s₂ b₂ h p n := by
  unfold zstep
  rw [(hag _ h1).1, (hag _ h1).2, (hag _ h2).1, (hag _ h2).2]

theorem zrec_agree {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    {N : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (h : ℝ)
    (Nn : ℕ → Noise d) (p : SDEState d × SDEState d) (k : ℕ)
    (hin : ∀ j < k, (zrec s₂ b₂ h Nn j p).1 ∈ N ∧ (zrec s₂ b₂ h Nn j p).2 ∈ N) :
    zrec s₁ b₁ h Nn k p = zrec s₂ b₂ h Nn k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun j hj => hin j (Nat.lt_succ_of_lt hj)
    show ((zrec s₁ b₁ h Nn k p).2, zstep s₁ b₁ h (zrec s₁ b₁ h Nn k p) (Nn k)) =
      ((zrec s₂ b₂ h Nn k p).2, zstep s₂ b₂ h (zrec s₂ b₂ h Nn k p) (Nn k))
    rw [ih']
    obtain ⟨h1, h2⟩ := hin k (Nat.lt_succ_self k)
    rw [zstep_agree hag h _ h1 h2]

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

theorem zrec_stay_agree {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    {N : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (h : ℝ)
    (Nn : ℕ → Noise d) (p : SDEState d × SDEState d) (hp1 : p.1 ∈ N) (k : ℕ)
    (hin : ∀ j ≤ k, (zrec s₂ b₂ h Nn j p).2 ∈ N) :
    zrec s₁ b₁ h Nn k p = zrec s₂ b₂ h Nn k p := by
  refine zrec_agree hag h Nn p k fun j hj => ⟨?_, hin j hj.le⟩
  cases j with
  | zero => exact hp1
  | succ j => exact hin j (by omega)

theorem xside_transfer [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0} (hh : 0 < (h : ℝ))
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs₂ : Continuous s₂) (hb₂ : Continuous b₂) {S : ℝ} (hS : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    {N : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x)
    (p : SDEState d × SDEState d) (hp1 : p.1 ∈ N) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ z, ‖z - p.2‖ < δ → z ∈ N) (hT : n * (h * S) ≤ δ / 2) (B : Set (SDEState d)) :
    P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) n p).2 ∈ B} ≤
      P.real {ω | (zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) n p).2 ∈ B} +
        16 * d * S ^ 2 * (n * h) / (δ / 2) ^ 2 := by
  have hex := chain_exit hW hh hs₂ hb₂ hS p n hδ hT
  have hsub : {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) n p).2 ∈ B} ⊆
      {ω | (zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) n p).2 ∈ B} ∪
        {ω | ∃ k ≤ n, δ ≤ ‖(zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) k p).2 - p.2‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_cases he : ∃ k ≤ n, δ ≤ ‖(zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) k p).2 - p.2‖
    · exact Or.inr he
    · left
      have hin : ∀ j ≤ n, (zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) j p).2 ∈ N := fun j hj => by
        refine hball _ ?_
        by_contra hc
        exact he ⟨j, hj, not_lt.1 hc⟩
      simp only [Set.mem_setOf_eq]
      rw [← zrec_stay_agree hag _ _ p hp1 n hin]
      exact hω
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have : P.real {ω | ∃ k ≤ n, δ ≤ ‖(zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) k p).2 - p.2‖} ≤
      16 * d * S ^ 2 * (n * h) / (δ / 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

theorem yside_transfer [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0}
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (p : SDEState d × SDEState d) (hp1 : p.1 ∈ N) (n : ℕ) (A : Set (SDEState d)) :
    P.real {ω | (zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) n p).2 ∈ A ∧
        ∀ k ≤ n, (zrec s₂ b₂ (h : ℝ) (noiseAt W h 0 ω) k p).2 ∈ Bx} ≤
      P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) n p).2 ∈ A} := by
  refine measureReal_mono (fun ω hω => ?_)
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [zrec_stay_agree hag _ _ p hp1 n fun j hj => hBxN (hω.2 j hj)]
  exact hω.1

variable {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

/-- Finite-`h` minorisation for chains with coefficients `s₁, b₁` started at `(x,x)` and `(y,y)`,
via the box coefficients `s₂, b₂` (nondegenerate: right inverse `J`). -/
theorem steer_lower_s1 [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) (x y : SDEState d) (hm2 : 2 ≤ m) {G : ℝ}
    (hG : ‖x - y‖ ^ 2 ≤ G)
    {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) (ha : 0 < a)
    (hT : m * (h * S) ≤ δ / 2)
    {A B : Set (SDEState d)} (hA : MeasurableSet A)
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx) :
    Real.exp (-a) * (P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈ B} -
        2 * (16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
          (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (y, y)).2 ∈ A} := by
  have hxN : ∀ z, ‖z - x‖ < δ → z ∈ N := fun z hz =>
    hBxN (hBx 0 le_rfl zero_le_one z (by simp; linarith))
  have hyN : y ∈ N := hBxN (hBx 1 zero_le_one le_rfl y (by simp; positivity))
  have hxN' : x ∈ N := hxN x (by simp [hδ])
  have hbox := steer_lower_box (J := J) (m := m) hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ
    ((x, x), (y, y)) hm2 hG hG hδ hε hεδ ha hT hA hBxm hB hBx
  have hy := yside_transfer (P := P) (W := W) (h := h) (s₁ := s₁) (b₁ := b₁) hag hBxN (y, y)
    hyN m A
  have hx := xside_transfer (P := P) hW hh hs hb hSg hag (x, x) hxN' m hδ hxN hT B
  refine le_trans ?_ (hbox.trans hy)
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  linarith

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

/-- `F_r = {z | ball z r ⊆ F}` is closed. -/
theorem inner_set_isClosed (F : Set (SDEState d)) (r : ℝ) :
    IsClosed {z : SDEState d | Metric.ball z r ⊆ F} := by
  rw [← isOpen_compl_iff]
  have e : {z : SDEState d | Metric.ball z r ⊆ F}ᶜ = ⋃ w ∈ Fᶜ, Metric.ball w r := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.not_subset,
      Metric.mem_ball, exists_prop]
    constructor
    · rintro ⟨w, hw, hwF⟩; exact ⟨w, hwF, by rw [dist_comm]; exact hw⟩
    · rintro ⟨w, hwF, hw⟩; exact ⟨w, by rw [dist_comm]; exact hw, hwF⟩
  rw [e]
  exact isOpen_biUnion fun w _ => Metric.isOpen_ball

theorem pow_E_le {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (m : ℕ) :
    (1 + 13 * c * h) ^ m ≤ Real.exp (13 * c * (m * h)) := by
  have h1 : 1 + 13 * c * h ≤ Real.exp (13 * c * h) := by
    have := Real.add_one_le_exp (13 * c * h); linarith
  calc (1 + 13 * c * h) ^ m ≤ Real.exp (13 * c * h) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
    _ = Real.exp (13 * c * (m * h)) := by rw [← Real.exp_nat_mul]; ring_nf

theorem eulerY_T_eq {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} (T : ℝ≥0) (n : ℕ)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (hT : (T : ℝ) = n * (h : ℝ)) (x : SDEState d) (ω : Ω) :
    eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) x x (T : ℝ) =
      (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) n (x, x)).2 := by
  rw [hT, eulerY_grid hh (hWc ω)]
  have := eulerZZ_eq_zrec (s₁ := s₁) (b₁ := b₁) ω (hWc ω) hh x x 0 n
  rw [zero_add] at this
  rw [this]
  rfl

set_option maxHeartbeats 1000000 in
/-- One step `h = T/m` of the limit (C5e): minorisation with Euler errors. -/
theorem core_step [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ ρ a R : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) {m : ℕ} (hm2 : 2 ≤ m) {h : ℝ≥0} (hh : 0 < (h : ℝ))
    (hh1 : (h : ℝ) ≤ 1) (hmh : (m : ℝ) * h = T) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} -
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a -
        P.real {ω | (∀ s ≤ T, ‖Xx s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xx T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) x x T‖ ^ 2} -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
          Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2 * h) ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ +
        P.real {ω | (∀ s ≤ T, ‖Xy s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xy T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) y y T‖ ^ 2} := by
  set c := 2 * L + L ^ 2 + 6 * d * L ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hG0 : 0 ≤ G := le_trans (by positivity) hG
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hTm : (m : ℝ) * ((h : ℝ) * S) ≤ δ / 2 := by rw [← mul_assoc, hmh]; exact hTS
  have hB : ∀ z ∈ {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}, ∀ z', ‖z' - z‖ < ρ →
      z' ∈ {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F} := by
    intro z hz z' hz' w hw
    refine hz ?_
    rw [Metric.mem_ball] at hw ⊢
    rw [dist_eq_norm] at hw ⊢
    have := norm_sub_le_norm_sub_add_norm_sub w z' z
    rw [← dist_eq_norm, ← dist_eq_norm] at this
    rw [dist_eq_norm, dist_eq_norm] at this
    linarith
  have st := steer_lower_s1 (m := m) hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ hag hBxN hBxm x y hm2
    hG hδ hρ hρδ ha hTm (inner_set_isClosed F (2 * ρ)).measurableSet hB hBx
  -- Euler = chain at time T
  have hWc : ∀ ω, Continuous fun s => W s ω := hW.2.1
  have hTe : (T : ℝ) = m * (h : ℝ) := hmh.symm
  have eY : ∀ z ω, eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) z z (T : ℝ) =
      (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (z, z)).2 := fun z ω =>
    eulerY_T_eq hWc T m hh hTe z ω
  have hsq : ∀ v : SDEState d, ¬ ρ ^ 2 < ‖v‖ ^ 2 → ‖v‖ ≤ ρ := fun v hv => by
    by_contra hc'
    exact hv (pow_lt_pow_left₀ (not_le.1 hc') hρ.le two_ne_zero)
  -- x side
  have hxs : {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} ⊆
      ({ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈
          {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} ∪
        {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ) ∪
        {ω | (∀ s ≤ T, ‖Xx s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xx T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) x x T‖ ^ 2} := by
    intro ω hω
    by_cases hst : ∀ s ≤ T, ‖Xx s ω‖ ≤ R
    · by_cases he : ρ ^ 2 < ‖Xx T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) x x T‖ ^ 2
      · exact Or.inr ⟨hst, he⟩
      · left; left
        have hd := hsq _ he
        rw [eY] at hd
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro w hw
        refine hω ?_
        rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
        have := norm_sub_le_norm_sub_add_norm_sub w (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2
          (Xx T ω)
        rw [norm_sub_rev (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2] at this
        linarith
    · exact Or.inl (Or.inr hst)
  have hx1 : P.real {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} ≤
      P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈
          {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} +
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ +
        P.real {ω | (∀ s ≤ T, ‖Xx s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xx T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) x x T‖ ^ 2} := by
    refine (measureReal_mono (μ := P) hxs).trans ?_
    have u1 := measureReal_union_le (μ := P) ({ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈
          {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} ∪
        {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ) {ω | (∀ s ≤ T, ‖Xx s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xx T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) x x T‖ ^ 2}
    have u2 := measureReal_union_le (μ := P) {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈
          {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ
    linarith
  -- y side
  have hys : {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (y, y)).2 ∈
        {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F}} ⊆
      ({ω | Xy T ω ∈ F} ∪ {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ) ∪
        {ω | (∀ s ≤ T, ‖Xy s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xy T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) y y T‖ ^ 2} := by
    intro ω hω
    by_cases hst : ∀ s ≤ T, ‖Xy s ω‖ ≤ R
    · by_cases he : ρ ^ 2 < ‖Xy T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) y y T‖ ^ 2
      · exact Or.inr ⟨hst, he⟩
      · left; left
        have hd := hsq _ he
        rw [eY] at hd
        simp only [Set.mem_setOf_eq] at hω ⊢
        refine hω ?_
        rw [Metric.mem_ball, dist_eq_norm]
        linarith
    · exact Or.inl (Or.inr hst)
  have hy1 : P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (y, y)).2 ∈
        {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F}} ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ +
        P.real {ω | (∀ s ≤ T, ‖Xy s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xy T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) y y T‖ ^ 2} := by
    refine (measureReal_mono (μ := P) hys).trans ?_
    have u1 := measureReal_union_le (μ := P) ({ω | Xy T ω ∈ F} ∪ {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ)
      {ω | (∀ s ≤ T, ‖Xy s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xy T ω - eulerY s₁ b₁ (h : ℝ) (fun s => W s ω) y y T‖ ^ 2}
    have u2 := measureReal_union_le (μ := P) {ω | Xy T ω ∈ F} {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ
    linarith
  -- constants
  have hE := pow_E_le hc0 (NNReal.coe_nonneg h) m
  rw [hmh] at hE
  set E := (1 + 13 * c * (h : ℝ)) ^ m with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have htr : 4 * G * (1 + 13 * E) * (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) /
      δ ^ 2 ≤ 4 * G * (1 + 13 * Real.exp (13 * c * T)) *
        (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 := by
    rw [hmh]
    gcongr
  have hKL : (Λ ^ 2 * (G * E / m) / (2 * h) + 1) / a ≤
      (Λ ^ 2 * G * Real.exp (13 * c * T) / (2 * T) + 1) / a := by
    gcongr ?_ / a
    have e : Λ ^ 2 * (G * E / m) / (2 * h) = Λ ^ 2 * G * E / (2 * T) := by
      rw [← hmh]; field_simp
    rw [e]
    gcongr
  have hch : 5 * c * h * G * E / (m : ℝ) ^ 2 / ρ ^ 2 ≤
      5 * c * G * Real.exp (13 * c * T) / ρ ^ 2 * h := by
    have h1 : 5 * c * h * G * E / (m : ℝ) ^ 2 ≤ 5 * c * h * G * E := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ 5 * c * h * G * E := by positivity
      have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
      exact le_mul_of_one_le_right this hm1
    have h2 : 5 * c * h * G * E ≤ 5 * c * h * G * Real.exp (13 * c * T) := by
      gcongr
    calc 5 * c * h * G * E / (m : ℝ) ^ 2 / ρ ^ 2 ≤ 5 * c * h * G * Real.exp (13 * c * T) / ρ ^ 2 :=
          div_le_div_of_nonneg_right (h1.trans h2) (by positivity)
      _ = 5 * c * G * Real.exp (13 * c * T) / ρ ^ 2 * h := by ring
  have hex : 2 * (16 * d * S ^ 2 * ((m : ℝ) * h) / (δ / 2) ^ 2) =
      2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) := by rw [hmh]
  refine le_trans ?_ (st.trans ?_)
  · refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    linarith
  · linarith

/-- Grid form of the Euler limit: via `EthierKurtz.euler_chain_close_in_probability`. -/
theorem euler_close_grid [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S L R : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    (hag : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {hn : ℕ → ℝ≥0} (hpos : ∀ n, 0 < (hn n : ℝ)) (hlim : Tendsto (fun n => (hn n : ℝ)) atTop (𝓝 0))
    (j : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hj : ∀ n, (T : ℝ) = j n * (hn n : ℝ)) :
    Tendsto (fun n => P {ω | (∀ s ≤ T, ‖X s ω‖ ≤ R) ∧
      ε < ‖X T ω - eulerY s₁ b₁ (hn n : ℝ) (fun s => W s ω) x₀ x₀ T‖ ^ 2}) atTop (𝓝 0) := by
  have key := EthierKurtz.euler_chain_close_in_probability hW x₀ hσ hb hX hs₁ hb₁ hR hL hSg hLg hag
    T hpos hlim j hj hε (fun n ω k => zrec s₁ b₁ (hn n : ℝ) (noiseAt W (hn n) 0 ω) k (x₀, x₀))
    (fun n ω => rfl) (fun n ω k => by
      simp only [zrec, zstep, noiseAt, cellZeta, zetaF, Nat.zero_add])
  have e : ∀ n ω, eulerY s₁ b₁ (hn n : ℝ) (fun s => W s ω) x₀ x₀ (T : ℝ) =
      (zrec s₁ b₁ (hn n : ℝ) (noiseAt W (hn n) 0 ω) (j n) (x₀, x₀)).2 := fun n ω =>
    eulerY_T_eq hW.2.1 T (j n) (hpos n) (hj n) x₀ ω
  simp only [e]
  exact key

/-- C5e: minorisation of the SDE transition laws, `h → 0` limit of `core_step`. -/
theorem core_minor [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S₁ L₁ R : ℝ} (hR : 0 ≤ R) (hL₁ : 0 ≤ L₁)
    (hSg₁ : ∀ x, ‖s₁ x‖ ≤ S₁ ∧ ‖b₁ x‖ ≤ S₁)
    (hLg₁ : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L₁ * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L₁ * ‖x - y‖)
    (hag₁ : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ ρ a : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} -
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a) ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ := by
  set hN : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 2) with hNdef
  have hcoe : ∀ n, ((hN n : ℝ≥0) : ℝ) = (T : ℝ) / ((n : ℝ) + 2) := fun n => by
    simp [hNdef, NNReal.coe_div]
  have hpos : ∀ n, 0 < ((hN n : ℝ≥0) : ℝ) := fun n => by rw [hcoe]; positivity
  have hlim : Tendsto (fun n => ((hN n : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    simp_rw [hcoe]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hmh : ∀ n, (((n + 2 : ℕ) : ℝ)) * ((hN n : ℝ≥0) : ℝ) = T := fun n => by
    rw [hcoe]; push_cast; field_simp
  have eux := euler_close_grid hW x hσ hb0 hXx hs₁ hb₁ hR hL₁ hSg₁ hLg₁ hag₁
    (hn := hN) hpos hlim (fun n => n + 2) (ε := ρ ^ 2) (by positivity) T (fun n => (hmh n).symm)
  have euy := euler_close_grid hW y hσ hb0 hXy hs₁ hb₁ hR hL₁ hSg₁ hLg₁ hag₁
    (hn := hN) hpos hlim (fun n => n + 2) (ε := ρ ^ 2) (by positivity) T (fun n => (hmh n).symm)
  have rux := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp eux
  have ruy := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp euy
  rw [ENNReal.toReal_zero] at rux ruy
  have hev : ∀ᶠ n in atTop, ((hN n : ℝ≥0) : ℝ) < 1 := hlim.eventually (gt_mem_nhds one_pos)
  have key : ∀ᶠ n in atTop,
      Real.exp (-a) * (P.real {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} -
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a -
        ((fun x => ENNReal.toReal x) ∘ fun n => P {ω | (∀ s ≤ T, ‖Xx s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xx T ω - eulerY s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) x x T‖ ^ 2}) n -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
          Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2 * ((hN n : ℝ≥0) : ℝ)) ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ +
        ((fun x => ENNReal.toReal x) ∘ fun n => P {ω | (∀ s ≤ T, ‖Xy s ω‖ ≤ R) ∧
          ρ ^ 2 < ‖Xy T ω - eulerY s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) y y T‖ ^ 2}) n := by
    filter_upwards [hev] with n hn
    exact core_step (m := n + 2) (h := hN n) hW x y hs hb hJm hJ hL hSg hLg hΛ hag hBxN hBxm hG
      hT0 hδ hρ hρδ ha hTS hBx F (by omega) (hpos n) hn.le (hmh n)
  have lim := le_of_tendsto_of_tendsto
    (((tendsto_const_nhds.sub rux).sub (hlim.const_mul _)).const_mul (Real.exp (-a)))
    (tendsto_const_nhds.add ruy) key
  simp only [sub_zero, mul_zero, add_zero] at lim
  exact lim

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

theorem iUnion_inner_eq_interior (F : Set (SDEState d)) {δ : ℝ} (hδ : 0 < δ) :
    ⋃ k : ℕ, {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F} = interior F := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    exact interior_maximal hk Metric.isOpen_ball (Metric.mem_ball_self (by positivity))
  · intro hz
    obtain ⟨r, hr, hrF⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    obtain ⟨k, hk⟩ := exists_nat_gt (4 * δ / r)
    refine ⟨k, (Metric.ball_subset_ball ?_).trans (hrF.trans interior_subset)⟩
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hr] at hk
    rw [mul_div_assoc', div_le_iff₀ hk1]
    linarith

theorem inner_mono (F : Set (SDEState d)) {δ : ℝ} (hδ : 0 < δ) :
    Monotone fun k : ℕ => {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F} := by
  intro k k' hkk z hz
  refine (Metric.ball_subset_ball ?_).trans hz
  have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
  gcongr

theorem core_minor_int [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S₁ L₁ R : ℝ} (hR : 0 ≤ R) (hL₁ : 0 ≤ L₁)
    (hSg₁ : ∀ x, ‖s₁ x‖ ≤ S₁ ∧ ‖b₁ x‖ ≤ S₁)
    (hLg₁ : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L₁ * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L₁ * ‖x - y‖)
    (hag₁ : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ a : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ interior F} -
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a) ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ := by
  have hmx : Measurable (Xx T) := hXx.1 T
  have hmono : Monotone fun k : ℕ =>
      Xx T ⁻¹' {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F} :=
    fun k k' hkk => Set.preimage_mono (inner_mono F hδ hkk)
  have hU : (⋃ k : ℕ, Xx T ⁻¹' {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F}) =
      {ω | Xx T ω ∈ interior F} := by
    rw [← Set.preimage_iUnion, iUnion_inner_eq_interior F hδ]; rfl
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at ht
  have htr := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp ht
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hρ : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1) := fun k => by have := hk1 k; positivity
  have hρδ : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ := fun k =>
    div_le_self hδ.le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  refine le_of_tendsto' (x := (atTop : Filter ℕ)) ?_ fun k => core_minor hW hσ hb0 x y hXx hXy hs₁ hb₁ hR hL₁ hSg₁ hLg₁ hag₁
    hs hb hJm hJ hL hSg hLg hΛ hag hBxN hBxm hG hT0 hδ (hρ k) (hρδ k) ha hTS hBx F
  refine Tendsto.const_mul _ ?_
  refine (((Tendsto.sub_const ?_ _).sub_const _).sub_const _).sub_const _
  have e : ∀ k : ℕ, 4 * (δ / ((k : ℝ) + 1)) = 4 * (δ / ((k : ℝ) + 1)) := fun _ => rfl
  exact htr

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

theorem exit_real_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → SDEState d} (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous fun t => X t ω)
    (T : ℝ≥0) :
    Tendsto (fun R : ℕ => P.real {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (exit_tendsto (P := P) hm hc T)
  simpa [Function.comp_def, measureReal_def] using h

theorem core_minor_lim [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ : ℕ → SDEState d → SDEDiffusion d} {b₁ : ℕ → SDEState d → SDEState d} {S₁ L₁ : ℕ → ℝ}
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL₁ : ∀ R, 0 ≤ L₁ R)
    (hSg₁ : ∀ R x, ‖s₁ R x‖ ≤ S₁ R ∧ ‖b₁ R x‖ ≤ S₁ R)
    (hLg₁ : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L₁ R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L₁ R * ‖x - y‖)
    (hag₁ : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {s₂ : SDEState d → SDEDiffusion d} {b₂ : SDEState d → SDEState d}
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, σ₀ x = s₂ x ∧ b₀ x = b₂ x)
    {R₀ : ℝ} (hNR : ∀ x ∈ N, ‖x‖ ≤ R₀) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ a : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ interior F} - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a) ≤
      P.real {ω | Xy T ω ∈ F} := by
  have hx := exit_real_tendsto (P := P) hXx.1 hXx.2.1 T
  have hy := exit_real_tendsto (P := P) hXy.1 hXy.2.1 T
  set E1 : ℝ := 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2)
  set E2 : ℝ := 4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2
  set E3 : ℝ := (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a
  set A : ℝ := P.real {ω | Xx T ω ∈ interior F}
  set B : ℝ := P.real {ω | Xy T ω ∈ F}
  have hf : Tendsto (fun R : ℕ => Real.exp (-a) * (A - P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ (R : ℝ)}ᶜ
      - E1 - E2 - E3)) atTop (𝓝 (Real.exp (-a) * (A - 0 - E1 - E2 - E3))) :=
    Tendsto.const_mul _ ((((tendsto_const_nhds.sub hx).sub_const _).sub_const _).sub_const _)
  have hg : Tendsto (fun R : ℕ => B + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ (R : ℝ)}ᶜ) atTop (𝓝 (B + 0)) :=
    tendsto_const_nhds.add hy
  rw [sub_zero] at hf
  rw [add_zero] at hg
  refine le_of_tendsto_of_tendsto hf hg ?_
  obtain ⟨R1, hR1⟩ := exists_nat_ge R₀
  filter_upwards [eventually_ge_atTop R1] with R hR
  have hRR : R₀ ≤ (R : ℝ) := hR1.trans (by exact_mod_cast hR)
  have hag' : ∀ z ∈ N, s₁ R z = s₂ z ∧ b₁ R z = b₂ z := by
    intro z hz
    have h1 := hag₁ R z (by linarith [hNR z hz])
    exact ⟨h1.1.trans (hag z hz).1, h1.2.trans (hag z hz).2⟩
  exact core_minor_int hW hσ hb0 x y hXx hXy (hs₁ R) (hb₁ R) (Nat.cast_nonneg R) (hL₁ R) (hSg₁ R)
    (hLg₁ R) (hag₁ R) hs hb hJm hJ hL hSg hLg hΛ hag' hBxN hBxm hG hT0 hδ ha hTS hBx F

end C5fa
end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open EthierKurtz in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ : ℕ → SDEState d → SDEDiffusion d} {b₁ : ℕ → SDEState d → SDEState d} {S₁ L₁ : ℕ → ℝ}
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL₁ : ∀ R, 0 ≤ L₁ R)
    (hSg₁ : ∀ R x, ‖s₁ R x‖ ≤ S₁ R ∧ ‖b₁ R x‖ ≤ S₁ R)
    (hLg₁ : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L₁ R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L₁ R * ‖x - y‖)
    (hag₁ : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {s₂ : SDEState d → SDEDiffusion d} {b₂ : SDEState d → SDEState d}
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, WithLp.toLp 2 (fun i => ∑ j, (s₂ p.1 (i, j) + s₂ p.2 (i, j)) / 2 * J p v j) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, σ₀ x = s₂ x ∧ b₀ x = b₂ x)
    {R₀ : ℝ} (hNR : ∀ x ∈ N, ‖x‖ ≤ R₀) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ a : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (hsmall : 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) +
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 +
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a ≤ 1 / 4)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ interior F} - 1 / 4) ≤ P.real {ω | Xy T ω ∈ F} := by
  have h := ItoLib.core_minor_lim hW hσ hb0 x y hXx hXy hs₁ hb₁ hL₁ hSg₁ hLg₁ hag₁ hs hb hJm hJ hL hSg hLg
    hΛ hag hNR hBxN hBxm hG hT0 hδ ha hTS hBx F
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos (-a)).le) h
  linarith

