-- Prove2me | solution 1 for EthierKurtz.steered_euler_coupling_lower_box
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:42:07.326632+00:00
-- url     : https://prove2.me/submissions/50330e39-398f-40bb-9045-8be242c221a5

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
import Theorems.Thm_EthierKurtz_steered_euler_coupling_tracking
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

theorem dyTime_mono (t : ℝ≥0) (N : ℕ) {i l : ℕ} (h : i ≤ l) : dyTime t N i ≤ dyTime t N l := by
  unfold dyTime; gcongr

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

/-- Noises of the cells `m, m+1, ...` of the scheme driven by `W`. -/
noncomputable def noiseAt (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (m : ℕ) (ω : Ω) (l : ℕ) : Noise d :=
  (fun j => W ((((m + l : ℕ) : ℝ) * h).toNNReal + h) ω j - W (((m + l : ℕ) : ℝ) * h).toNNReal ω j,
    fun j => cellZeta W (((m + l : ℕ) : ℝ) * h).toNNReal h j ω)

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

/-- Cameron-Martin weight of a shift by `a` for `N(0, v)`. -/
noncomputable def cmw (v : ℝ≥0) (a x : ℝ) : ℝ := Real.exp (-(a * x) / v - a ^ 2 / (2 * v))

theorem pdf_mul_cmw (v : ℝ≥0) (hv : v ≠ 0) (a x : ℝ) :
    gaussianPDFReal 0 v x * cmw v a x = gaussianPDFReal 0 v (x + a) := by
  simp only [gaussianPDFReal_def, cmw, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

/-- One-dimensional Cameron-Martin: `E[g(ξ + a) w_a(ξ)] = E[g(ξ)]` for `ξ ~ N(0, v)`. -/
theorem gauss_shift_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ≥0) (hv : v ≠ 0) (a : ℝ) (g : ℝ → E) :
    ∫ x, cmw v a x • g (x + a) ∂gaussianReal 0 v = ∫ x, g x ∂gaussianReal 0 v := by
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have : ∀ x, gaussianPDFReal 0 v x • (cmw v a x • g (x + a)) =
      (fun y => gaussianPDFReal 0 v y • g y) (x + a) := by
    intro x
    simp only [smul_smul]
    rw [pdf_mul_cmw v hv a x]
  simp_rw [this]
  exact integral_add_right_eq_self (μ := volume) (fun y => gaussianPDFReal 0 v y • g y) a

theorem cmw_pos (v : ℝ≥0) (a x : ℝ) : 0 < cmw v a x := Real.exp_pos _

theorem integrable_cmw (v : ℝ≥0) (a : ℝ) : Integrable (cmw v a) (gaussianReal 0 v) := by
  have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(a / v))).const_mul
    (Real.exp (-(a ^ 2 / (2 * v))))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [cmw]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Multi-dimensional weight. -/
noncomputable def cmwPi {ι : Type*} [Fintype ι] (v : ι → ℝ≥0) (a x : ι → ℝ) : ℝ :=
  ∏ i, cmw (v i) (a i) (x i)

/-- Finite-family Cameron-Martin: shifting independent `N(0, vᵢ)` coordinates by `a` and weighting
by `cmwPi` gives back the product Gaussian. -/
theorem gauss_pi_shift {ι : Type*} [Fintype ι] (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) (a : ι → ℝ) :
    ((Measure.pi fun i => gaussianReal 0 (v i)).withDensity
        (fun x => ENNReal.ofReal (cmwPi v a x))).map (fun x => x + a) =
      Measure.pi fun i => gaussianReal 0 (v i) := by
  have hmeas : Measurable fun x : ι → ℝ => x + a := measurable_id.add_const a
  have hwm : Measurable fun x : ι → ℝ => ENNReal.ofReal (cmwPi v a x) := by
    apply ENNReal.measurable_ofReal.comp
    unfold cmwPi cmw
    fun_prop
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs),
    withDensity_apply _ (hmeas (MeasurableSet.univ_pi hs))]
  set f : ι → ℝ → ℝ := fun i x => (s i).indicator (fun _ => (1 : ℝ)) (x + a i) * cmw (v i) (a i) x
    with hf
  have hfi : ∀ i, Integrable (f i) (gaussianReal 0 (v i)) := by
    intro i
    refine (integrable_cmw (v i) (a i)).mono' ?_ (ae_of_all _ fun x => ?_)
    · have h1 : Measurable fun x : ℝ => (s i).indicator (fun _ => (1 : ℝ)) (x + a i) :=
        (measurable_const.indicator (hs i)).comp (measurable_id.add_const _)
      have h2 : Measurable (cmw (v i) (a i)) := by unfold cmw; fun_prop
      exact (h1.mul h2).aestronglyMeasurable
    · simp only [hf, Real.norm_eq_abs, abs_mul]
      have hc : |cmw (v i) (a i) x| = cmw (v i) (a i) x := abs_of_pos (cmw_pos _ _ _)
      rw [hc]
      by_cases hx : x + a i ∈ s i
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx, (cmw_pos _ _ _).le]
  have hf0 : ∀ i x, 0 ≤ f i x := fun i x =>
    mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (cmw_pos _ _ _).le
  have hone : ∀ i, ∫ x, f i x ∂gaussianReal 0 (v i) = (gaussianReal 0 (v i) (s i)).toReal := by
    intro i
    have := gauss_shift_integral (v i) (hv i) (a i) (fun y => (s i).indicator (fun _ => (1 : ℝ)) y)
    simp only [smul_eq_mul] at this
    simp only [hf]
    rw [show (fun x => (s i).indicator (fun _ => (1 : ℝ)) (x + a i) * cmw (v i) (a i) x) =
      fun x => cmw (v i) (a i) x * (s i).indicator (fun _ => (1 : ℝ)) (x + a i) from
        funext fun x => mul_comm _ _, this, integral_indicator (hs i), setIntegral_const,
      smul_eq_mul, mul_one]
    rfl
  have hpt : ∀ x : ι → ℝ, ((fun x => x + a) ⁻¹' univ.pi s).indicator
      (fun x => ENNReal.ofReal (cmwPi v a x)) x = ENNReal.ofReal (∏ i, f i (x i)) := by
    intro x
    by_cases hx : x + a ∈ univ.pi s
    · rw [indicator_of_mem (show x ∈ (fun x => x + a) ⁻¹' univ.pi s from hx)]
      congr 1
      simp only [cmwPi, hf]
      refine Finset.prod_congr rfl fun i _ => ?_
      have : x i + a i ∈ s i := hx i (mem_univ i)
      simp [indicator_of_mem this]
    · rw [indicator_of_notMem (show x ∉ (fun x => x + a) ⁻¹' univ.pi s from hx)]
      obtain ⟨i, hi⟩ : ∃ i, x i + a i ∉ s i := by
        by_contra hcon
        push_neg at hcon
        exact hx fun i _ => hcon i
      have h0 : f i (x i) = 0 := by simp [hf, indicator_of_notMem hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, ENNReal.ofReal_zero]
  rw [← lintegral_indicator (hmeas (MeasurableSet.univ_pi hs))]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hfi)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => hf0 i (x i)),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => integral_nonneg (hf0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hone i, ENNReal.ofReal_toReal (measure_ne_top _ _)]

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

theorem map_withDensity_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (P : Measure α) {X : α → β} (hX : Measurable X) {g : β → ℝ≥0∞}
    (hg : Measurable g) {F : β → γ} (hF : Measurable F) :
    (P.withDensity (fun ω => g (X ω))).map (fun ω => F (X ω)) =
      ((P.map X).withDensity g).map F := by
  have hFX : Measurable fun ω => F (X ω) := hF.comp hX
  ext s hs
  rw [Measure.map_apply hFX hs, Measure.map_apply hF hs,
    withDensity_apply _ (hFX hs), withDensity_apply _ (hF hs),
    setLIntegral_map (hF hs) hg hX]
  rfl

/-- Dyadic Brownian increments on the first cell `[0, h]`. -/
noncomputable def dInc (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (n : ℕ) (ω : Ω) :
    Fin d × Fin (2 ^ n) → ℝ :=
  fun p => W (dyTime h n ((p.2 : ℕ) + 1)) ω p.1 - W (dyTime h n (p.2 : ℕ)) ω p.1

theorem dyTime_succ_sub' (h : ℝ≥0) (n r : ℕ) :
    (dyTime h n (r + 1) : ℝ) - dyTime h n r = ((h / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  simp only [dyTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]
  push_cast
  ring


theorem dyTime_zero' (h : ℝ≥0) (n : ℕ) : dyTime h n 0 = 0 := by simp [dyTime]

theorem dyTime_top (h : ℝ≥0) (n : ℕ) : dyTime h n (2 ^ n) = h := by
  unfold dyTime
  push_cast
  rw [mul_div_assoc, mul_div_cancel₀ _ (pow_ne_zero n two_ne_zero)]

theorem dInc_measurable [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (h : ℝ≥0) (n : ℕ) : Measurable (dInc W h n) :=
  measurable_pi_lambda _ fun _ =>
    Measurable.sub (G := ℝ) (stdBrownian_coord_measurable hW _ _) (stdBrownian_coord_measurable hW _ _)

theorem dInc_indep [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (n : ℕ) :
    iIndepFun (fun (p : Fin d × Fin (2 ^ n)) ω => dInc W h n ω p) P := by
  have hm : ∀ (j : Fin d) (i : Fin (2 ^ n)), Measurable fun ω => dInc W h n ω (j, i) :=
    fun j i => Measurable.sub (G := ℝ) (stdBrownian_coord_measurable hW _ _) (stdBrownian_coord_measurable hW _ _)
  set G : Fin d → (ℝ≥0 → ℝ) → (Fin (2 ^ n) → ℝ) := fun _ x i =>
    x (dyTime h n ((i : ℕ) + 1)) - x (dyTime h n (i : ℕ)) with hG
  have hGm : ∀ j, Measurable (G j) := fun _ =>
    measurable_pi_lambda _ fun i => (measurable_pi_apply _).sub (measurable_pi_apply _)
  have h1' := hW.2.2.2.comp G hGm
  have e1 : (fun (j : Fin d) ω (i : Fin (2 ^ n)) => dInc W h n ω (j, i)) =
      fun j => G j ∘ (fun ω t => W t ω j) := by
    funext j ω i
    rfl
  have h1 : iIndepFun (fun (j : Fin d) ω (i : Fin (2 ^ n)) => dInc W h n ω (j, i)) P := by
    rw [e1]; exact h1'
  have h2 : ∀ j : Fin d, iIndepFun (fun (i : Fin (2 ^ n)) ω => dInc W h n ω (j, i)) P := by
    intro j
    have := (hW.2.2.1 j).toIsPreBrownianReal.hasIndepIncrements (2 ^ n)
      (fun r : Fin (2 ^ n + 1) => dyTime h n r)
      (fun a b hab => dyTime_mono h n (by exact_mod_cast hab))
    have e : (fun (i : Fin (2 ^ n)) ω => dInc W h n ω (j, i)) = fun (i : Fin (2 ^ n)) ω =>
        W (dyTime h n ((i.succ : Fin (2 ^ n + 1)) : ℕ)) ω j -
          W (dyTime h n ((i.castSucc : Fin (2 ^ n + 1)) : ℕ)) ω j := by
      funext i ω
      simp only [dInc, Fin.val_succ, Fin.coe_castSucc]
    rw [e]
    exact this
  exact iIndepFun_uncurry' (X := fun j i ω => dInc W h n ω (j, i)) hm h1 h2

theorem dInc_marg [MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (n : ℕ)
    (p : Fin d × Fin (2 ^ n)) :
    P.map (fun ω => dInc W h n ω p) = gaussianReal 0 (h / (2 : ℝ≥0) ^ n) := by
  have hl := ((hW.2.2.1 p.1).toIsPreBrownianReal.hasLaw_sub (dyTime h n ((p.2 : ℕ) + 1))
    (dyTime h n (p.2 : ℕ))).map_eq
  have hd : nndist (dyTime h n ((p.2 : ℕ) + 1)).1 (dyTime h n (p.2 : ℕ)).1 =
      h / (2 : ℝ≥0) ^ n := by
    apply NNReal.eq
    rw [coe_nndist, Real.dist_eq, NNReal.val_eq_coe, NNReal.val_eq_coe, dyTime_succ_sub',
      abs_of_nonneg (NNReal.coe_nonneg _)]
  rw [hd] at hl
  have e2 : (fun ω => dInc W h n ω p) = (fun t ω => W t ω p.1) (dyTime h n ((p.2 : ℕ) + 1)) -
      (fun t ω => W t ω p.1) (dyTime h n (p.2 : ℕ)) := by
    funext ω
    rfl
  rw [e2]
  exact hl

/-- The dyadic increments are i.i.d. `N(0, h / 2^n)`. -/
theorem dInc_law [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (n : ℕ) :
    P.map (dInc W h n) = Measure.pi (fun _ => gaussianReal 0 (h / (2 : ℝ≥0) ^ n)) := by
  have hm : ∀ p : Fin d × Fin (2 ^ n), Measurable fun ω => dInc W h n ω p :=
    fun p => Measurable.sub (G := ℝ) (stdBrownian_coord_measurable hW _ _) (stdBrownian_coord_measurable hW _ _)
  have := (iIndepFun_iff_map_fun_eq_pi_map fun p => (hm p).aemeasurable).1 (dInc_indep hW h n)
  rw [show (fun ω (p : Fin d × Fin (2 ^ n)) => dInc W h n ω p) = dInc W h n from rfl] at this
  rw [this]
  congr 1
  funext p
  exact dInc_marg hW h n p

/-- Linear map from dyadic increments to the dyadic approximation of the cell noise. -/
noncomputable def psiN (h : ℝ≥0) (n : ℕ) (D : Fin d × Fin (2 ^ n) → ℝ) : Fin 1 → Noise d :=
  fun _ => (fun j => ∑ i : Fin (2 ^ n), D (j, i),
    fun j => (1 / (h : ℝ)) * ((∑ r : Fin (2 ^ n), ∑ i : Fin (2 ^ n),
      (if (r : ℕ) ≤ (i : ℕ) then D (j, i) else 0)) * ((h / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)))

theorem psiN_continuous (h : ℝ≥0) (n : ℕ) : Continuous (psiN (d := d) h n) := by
  refine continuous_pi fun _ => Continuous.prodMk
    (continuous_pi fun j => continuous_finsetSum _ fun i _ => continuous_apply _)
    (continuous_pi fun j => continuous_const.mul ((continuous_finsetSum _ fun r _ =>
      continuous_finsetSum _ fun i _ => ?_).mul continuous_const))
  by_cases hc : (r : ℕ) ≤ (i : ℕ)
  · simpa [hc] using continuous_apply (j, i)
  · simpa [hc] using continuous_const

theorem psiN_add (h : ℝ≥0) (n : ℕ) (D E : Fin d × Fin (2 ^ n) → ℝ) :
    psiN h n (D + E) = psiN h n D + psiN h n E := by
  funext l
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp [psiN, Finset.sum_add_distrib]
  · simp only [psiN, Pi.add_apply, Prod.snd_add]
    rw [← mul_add, ← add_mul, ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

theorem tele_ite (f : ℕ → ℝ) (m r : ℕ) (hr : r ≤ m) :
    ∑ i ∈ Finset.range m, (if r ≤ i then f (i + 1) - f i else 0) = f m - f r := by
  induction m with
  | zero =>
    have : r = 0 := Nat.le_zero.1 hr
    subst this
    simp
  | succ m ih =>
    rcases Nat.lt_or_ge m r with hlt | hge
    · have hr' : r = m + 1 := le_antisymm hr hlt
      subst hr'
      rw [sub_self]
      exact Finset.sum_eq_zero fun i hi => if_neg (by simp at hi; omega)
    · rw [Finset.sum_range_succ, ih hge, if_pos hge]
      ring

theorem sum_dInc (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (n : ℕ) (ω : Ω) (j : Fin d) (r : ℕ)
    (hr : r ≤ 2 ^ n) :
    ∑ i : Fin (2 ^ n), (if r ≤ (i : ℕ) then dInc W h n ω (j, i) else 0) =
      W h ω j - W (dyTime h n r) ω j := by
  have := tele_ite (fun k => W (dyTime h n k) ω j) (2 ^ n) r hr
  rw [dyTime_top] at this
  rw [← this, ← Fin.sum_univ_eq_sum_range (fun i => if r ≤ i then
    W (dyTime h n (i + 1)) ω j - W (dyTime h n i) ω j else 0) (2 ^ n)]
  rfl

theorem sum_dInc_all (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (n : ℕ) (ω : Ω) (j : Fin d) :
    ∑ i : Fin (2 ^ n), dInc W h n ω (j, i) = W h ω j - W 0 ω j := by
  have := sum_dInc W h n ω j 0 (Nat.zero_le _)
  simpa [dyTime_zero'] using this

/-- The level-`n` approximation of the first cell noise is `psiN` of the dyadic increments. -/
theorem apx_eq_psiN (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (n : ℕ) (ω : Ω) :
    apxPsi h 1 n (fun j q => W (apxT h 1 n q) ω j) = psiN h n (dInc W h n ω) := by
  funext l
  have hl : (l : ℕ) = 0 := Fin.val_eq_zero l
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp only [apxPsi, apxT, psiN, hl, Option.elim]
    rw [sum_dInc_all]
    simp [dyTime_zero']
  · simp only [apxPsi, apxT, psiN, hl, Option.elim]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sum_dInc W h n ω j r (le_of_lt r.2)]
    simp

/-- The constant drift increments. -/
noncomputable def aN (n : ℕ) (u : Fin d → ℝ) : Fin d × Fin (2 ^ n) → ℝ := fun p => u p.1 / 2 ^ n

theorem cmwPi_dInc (h : ℝ≥0) (hh : h ≠ 0) (n : ℕ) (u : Fin d → ℝ) (D : Fin d × Fin (2 ^ n) → ℝ) :
    cmwPi (fun _ : Fin d => h) u (fun j => ∑ i, D (j, i)) =
      cmwPi (fun _ => h / (2 : ℝ≥0) ^ n) (aN n u) D := by
  unfold cmwPi cmw aN
  rw [← Real.exp_sum, ← Real.exp_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have key : ∀ i : Fin (2 ^ n), -(u j / 2 ^ n * D (j, i)) / (((h / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) -
      (u j / 2 ^ n) ^ 2 / (2 * (((h / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ))) =
      (-u j / h) * D (j, i) - u j ^ 2 / (2 * h * 2 ^ n) := by
    intro i
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    field_simp
  simp_rw [key]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- Finite-level Cameron-Martin for the dyadic approximation. -/
theorem cm_level [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (hh : h ≠ 0) (n : ℕ)
    (u : Fin d → ℝ) :
    (P.withDensity (fun ω => ENNReal.ofReal
        (cmwPi (fun _ : Fin d => h) u (fun j => W h ω j - W 0 ω j)))).map
      (fun ω => psiN h n (dInc W h n ω + aN n u)) = P.map (fun ω => psiN h n (dInc W h n ω)) := by
  set g : (Fin d × Fin (2 ^ n) → ℝ) → ℝ≥0∞ :=
    fun D => ENNReal.ofReal (cmwPi (fun _ => h / (2 : ℝ≥0) ^ n) (aN n u) D) with hg
  have hgm : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    unfold cmwPi cmw
    fun_prop
  have hdens : (fun ω => ENNReal.ofReal
      (cmwPi (fun _ : Fin d => h) u (fun j => W h ω j - W 0 ω j))) = fun ω => g (dInc W h n ω) := by
    funext ω
    simp only [hg]
    rw [← cmwPi_dInc h hh n u]
    simp_rw [sum_dInc_all]
  have hX := dInc_measurable hW h n
  have hψ := (psiN_continuous (d := d) h n).measurable
  have hF : Measurable fun D : Fin d × Fin (2 ^ n) → ℝ => psiN h n (D + aN n u) :=
    hψ.comp (measurable_id.add_const _)
  rw [hdens, map_withDensity_comp P hX hgm hF, dInc_law hW h n,
    show (fun D : Fin d × Fin (2 ^ n) → ℝ => psiN h n (D + aN n u)) =
      psiN h n ∘ (fun D => D + aN n u) from rfl,
    ← Measure.map_map hψ (measurable_add_const (aN n u))]
  rw [gauss_pi_shift (fun _ => h / (2 : ℝ≥0) ^ n) (fun _ => div_ne_zero hh (pow_ne_zero _ two_ne_zero)) (aN n u),
    ← dInc_law hW h n, Measure.map_map hψ hX]
  rfl

theorem sum_range_cast_mul_two (m : ℕ) : (∑ r ∈ Finset.range m, (r : ℝ)) * 2 = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem psiN_aN (h : ℝ≥0) (hh : h ≠ 0) (n : ℕ) (u : Fin d → ℝ) :
    psiN h n (aN n u) = fun _ => (u, fun j => u j / 2 + u j / 2 * (1 / 2) ^ n) := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  funext l
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp only [psiN, aN]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · simp only [psiN, aN]
    have inner : ∀ r : Fin (2 ^ n), ∑ i : Fin (2 ^ n),
        (if (r : ℕ) ≤ (i : ℕ) then u j / 2 ^ n else 0) =
          u j / 2 ^ n * (2 : ℝ) ^ n - u j / 2 ^ n * ((r : ℕ) : ℝ) := by
      intro r
      have ht := tele_ite (fun k => u j / 2 ^ n * (k : ℝ)) (2 ^ n) r (le_of_lt r.2)
      simp only [Nat.cast_pow, Nat.cast_ofNat] at ht
      rw [← ht, ← Fin.sum_univ_eq_sum_range (fun i => if (r : ℕ) ≤ i then
        u j / 2 ^ n * ((i + 1 : ℕ) : ℝ) - u j / 2 ^ n * (i : ℝ) else 0) (2 ^ n)]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs
      · push_cast; ring
      · rfl
    rw [Finset.sum_congr rfl fun r _ => inner r, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun r => (r : ℝ)) (2 ^ n)]
    have hs := sum_range_cast_mul_two (2 ^ n)
    have hS : ∑ r ∈ Finset.range (2 ^ n), (r : ℝ) = (2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1) / 2 := by
      push_cast at hs
      linarith
    rw [hS, one_div_pow]
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    push_cast
    field_simp
    ring

theorem psiN_aN_tendsto (h : ℝ≥0) (hh : h ≠ 0) (u : Fin d → ℝ) :
    Tendsto (fun n => psiN h n (aN n u)) atTop (𝓝 (fun _ : Fin 1 => (u, fun j => u j / 2))) := by
  simp_rw [psiN_aN h hh]
  refine tendsto_pi_nhds.2 fun _ => Tendsto.prodMk_nhds tendsto_const_nhds
    (tendsto_pi_nhds.2 fun j => ?_)
  have := (tendsto_const_nhds (x := u j / 2) (f := (atTop : Filter ℕ))).add
    ((tendsto_const_nhds (x := u j / 2) (f := (atTop : Filter ℕ))).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)))
  simpa using this

/-- One-cell Cameron-Martin (C2b): weighting by `cmwPi h u ξ` and shifting the first cell noise
by `(u, u/2)` preserves its law. -/
theorem cell_cm [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (hh : h ≠ 0)
    (u : Fin d → ℝ) :
    (P.withDensity (fun ω => ENNReal.ofReal
        (cmwPi (fun _ : Fin d => h) u (fun j => W h ω j - W 0 ω j)))).map
      (fun ω => noiseV W h 1 ω + fun _ => (u, fun j => u j / 2)) = P.map (noiseV W h 1) := by
  have hlev := fun n => cm_level hW h hh n u
  set Q := P.withDensity (fun ω => ENNReal.ofReal
        (cmwPi (fun _ : Fin d => h) u (fun j => W h ω j - W 0 ω j))) with hQ
  set c : Fin 1 → Noise d := fun _ => (u, fun j => u j / 2) with hc
  have hX := fun n => dInc_measurable hW h n
  have hψ := fun n => psiN_continuous (d := d) h n
  have hmF : ∀ n, Measurable fun ω => psiN h n (dInc W h n ω + aN n u) :=
    fun n => (hψ n).measurable.comp ((hX n).add_const _)
  have hmG : ∀ n, Measurable fun ω => psiN h n (dInc W h n ω) :=
    fun n => (hψ n).measurable.comp (hX n)
  have : IsProbabilityMeasure Q := by
    constructor
    have := congrArg (fun μ : Measure (Fin 1 → Noise d) => μ univ) (hlev 0)
    rw [Measure.map_apply (hmF 0) MeasurableSet.univ, Measure.map_apply (hmG 0) MeasurableSet.univ,
      preimage_univ, preimage_univ] at this
    rw [this, measure_univ]
  have hV := noiseV_measurable hW h 1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun Φ => ?_
  rw [integral_map (hV.add_const c).aemeasurable Φ.continuous.aestronglyMeasurable,
    integral_map hV.aemeasurable Φ.continuous.aestronglyMeasurable]
  have hY : ∀ ω, Tendsto (fun n => psiN h n (dInc W h n ω)) atTop (𝓝 (noiseV W h 1 ω)) := by
    intro ω
    have := apx_tendsto hW.2.1 h 1 ω
    simp_rw [apx_eq_psiN] at this
    exact this
  have hcn := psiN_aN_tendsto h hh u
  have hL : Tendsto (fun n => ∫ ω, Φ (psiN h n (dInc W h n ω) + psiN h n (aN n u)) ∂Q) atTop
      (𝓝 (∫ ω, Φ (noiseV W h 1 ω + c) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖Φ‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => Φ.norm_coe_le_norm _)
      (Eventually.of_forall fun ω => (Φ.continuous.tendsto _).comp ((hY ω).add hcn))
    exact (Φ.continuous.measurable.comp ((hmG n).add_const _)).aestronglyMeasurable
  have hR : Tendsto (fun n => ∫ ω, Φ (psiN h n (dInc W h n ω)) ∂P) atTop
      (𝓝 (∫ ω, Φ (noiseV W h 1 ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖Φ‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => Φ.norm_coe_le_norm _)
      (Eventually.of_forall fun ω => (Φ.continuous.tendsto _).comp (hY ω))
    exact (Φ.continuous.measurable.comp (hmG n)).aestronglyMeasurable
  have hmid : ∀ n, ∫ ω, Φ (psiN h n (dInc W h n ω) + psiN h n (aN n u)) ∂Q =
      ∫ ω, Φ (psiN h n (dInc W h n ω)) ∂P := by
    intro n
    have e1 : ∫ ω, Φ (psiN h n (dInc W h n ω) + psiN h n (aN n u)) ∂Q =
        ∫ x, Φ x ∂(Q.map fun ω => psiN h n (dInc W h n ω + aN n u)) := by
      rw [integral_map (hmF n).aemeasurable Φ.continuous.aestronglyMeasurable]
      simp_rw [psiN_add]
    rw [e1, hlev n, integral_map (hmG n).aemeasurable Φ.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique (hL.congr hmid) hR

/-- One-cell Cameron-Martin at the level of the first cell noise `noiseAt W h 0 · 0`. -/
theorem cell_cm0 [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (hh : h ≠ 0)
    (u : Fin d → ℝ) :
    (P.withDensity (fun ω => ENNReal.ofReal
        (cmwPi (fun _ : Fin d => h) u (fun j => W h ω j - W 0 ω j)))).map
      (fun ω => noiseAt W h 0 ω 0 + (u, fun j => u j / 2)) = P.map (fun ω => noiseAt W h 0 ω 0) := by
  have hV := noiseV_measurable hW h 1
  have he : Measurable fun x : Fin 1 → Noise d => x 0 := measurable_pi_apply 0
  have := congrArg (fun μ : Measure (Fin 1 → Noise d) => μ.map fun x => x 0) (cell_cm hW h hh u)
  simp only at this
  rw [Measure.map_map he (hV.add_const _), Measure.map_map he hV] at this
  exact this

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

theorem noiseAt_meas_past {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (h : ℝ≥0) (x₀ : SDEState d) {k l : ℕ} (hl : l < k) :
    Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
      fun ω => noiseAt W h 0 ω l := by
  set sl : ℝ≥0 := (((0 + l : ℕ) : ℝ) * h).toNNReal with hsl
  have hle : sl + h ≤ ((k : ℝ) * h).toNNReal := by
    rw [← NNReal.coe_le_coe, NNReal.coe_add, hsl,
      Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    have hk : ((l : ℝ) + 1) ≤ k := by exact_mod_cast hl
    have h0 : (0 : ℝ) ≤ h := h.2
    push_cast
    nlinarith
  have hWm : ∀ r, r ≤ sl + h → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
        fun ω => W r ω j :=
    fun r hr j => coord_measurable_completedPast P W _ (hr.trans hle) j
  refine Measurable.prodMk ?_ ?_
  · refine @measurable_pi_lambda Ω _ _
      (completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal) _ _ fun j => ?_
    exact (hWm _ le_rfl j).sub (hWm _ le_self_add j)
  · refine @measurable_pi_lambda Ω _ _
      (completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal) _ _ fun j => ?_
    have hm : ∀ p : ℝ≥0, p ≤ h →
        Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal]
          fun ω => W (sl + h) ω j - W (sl + p) ω j :=
      fun p hp => (hWm _ le_rfl j).sub (hWm _ (by gcongr) j)
    have hc : ∀ ω, Continuous fun p : ℝ≥0 => W (sl + h) ω j - W (sl + p) ω j := fun ω =>
      continuous_const.sub (((EuclideanSpace.proj j).continuous.comp (hWc ω)).comp
        (continuous_const.add continuous_id))
    exact (measurable_intervalIntegral_of_continuous
      (completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal) h hm hc).const_mul _

theorem noiseV_meas_past {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (h : ℝ≥0) (x₀ : SDEState d) (k : ℕ) :
    Measurable[completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal] (noiseV W h k) :=
  @measurable_pi_lambda Ω (Fin k) (fun _ => Noise d)
    (completedBrownianPast P W (fun _ => x₀) ((k : ℝ) * h).toNNReal) _ (noiseV W h k)
    fun (l : Fin k) => noiseAt_meas_past (P := P) hWc h x₀ l.2

theorem noiseV_succ (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (k : ℕ) (ω : Ω) :
    noiseV W h (k + 1) ω =
      (Fin.snoc (noiseV W h k ω) (noiseAt W h k ω 0) : Fin (k + 1) → Noise d) := by
  funext l
  induction l using Fin.lastCases with
  | last => simp [noiseV, noiseAt]
  | cast i => simp [noiseV]

theorem measurable_snoc' (k : ℕ) :
    Measurable fun p : (Fin k → Noise d) × Noise d =>
      (Fin.snoc p.1 p.2 : Fin (k + 1) → Noise d) := by
  refine measurable_pi_lambda _ fun l => ?_
  induction l using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact measurable_snd
  | cast i => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply i).comp measurable_fst

theorem noiseAt_k_law [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (h : ℝ≥0) (k : ℕ) :
    P.map (fun ω => noiseAt W h k ω 0) = P.map (fun ω => noiseAt W h 0 ω 0) := by
  have hW' := shiftBM_std hW ((k : ℝ) * h).toNNReal
  have e : (fun ω => noiseAt W h k ω 0) =
      fun ω => noiseV (shiftBM W ((k : ℝ) * h).toNNReal) h 1 ω 0 :=
    funext fun ω => noiseAt_shift W h k ω 0
  have he : Measurable fun x : Fin 1 → Noise d => x 0 := measurable_pi_apply 0
  have := congrArg (fun μ : Measure (Fin 1 → Noise d) => μ.map fun x => x 0)
    (noiseV_law hW' hW h 1)
  rw [Measure.map_map he (noiseV_measurable hW' h 1), Measure.map_map he
    (noiseV_measurable hW h 1)] at this
  rw [e]
  exact this

theorem noiseV_succ_law [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (h : ℝ≥0) (k : ℕ) :
    P.map (noiseV W h (k + 1)) =
      ((P.map (noiseV W h k)).prod (P.map fun ω => noiseAt W h 0 ω 0)).map
        (fun p => (Fin.snoc p.1 p.2 : Fin (k + 1) → Noise d)) := by
  set t₀ : ℝ≥0 := ((k : ℝ) * h).toNNReal with ht₀
  have hU := noiseV_measurable hW h k
  have hVf := noiseAt_meas_fut hW.2.1 h k 0
  have hV : Measurable fun ω => noiseAt W h k ω 0 := hVf.mono (futBrownian_le hW _) le_rfl
  have hind : IndepFun (noiseV W h k) (fun ω => noiseAt W h k ω 0) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left
      (stdBrownian_indep_completedPast hW 0 t₀)
      (noiseV_meas_past (P := P) hW.2.1 h 0 k).comap_le) hVf.comap_le
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hind
  have e : noiseV W h (k + 1) = (fun p : (Fin k → Noise d) × Noise d =>
      (Fin.snoc p.1 p.2 : Fin (k + 1) → Noise d)) ∘ fun ω => (noiseV W h k ω, noiseAt W h k ω 0) :=
    funext (noiseV_succ W h k)
  rw [e, ← Measure.map_map (measurable_snoc' k) (hU.prodMk hV), hmap, noiseAt_k_law hW h k]

/-- One-cell Cameron-Martin, lintegral form on the law `ν₁` of a cell noise. -/
theorem cell_cm_lint [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (h : ℝ≥0) (hh : h ≠ 0) (u : Fin d → ℝ)
    {G : Noise d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ b, G (b + (u, fun j => u j / 2)) * ENNReal.ofReal (cmwPi (fun _ : Fin d => h) u b.1)
        ∂(P.map fun ω => noiseAt W h 0 ω 0) = ∫⁻ b, G b ∂(P.map fun ω => noiseAt W h 0 ω 0) := by
  set g : Noise d → ℝ≥0∞ := fun b => ENNReal.ofReal (cmwPi (fun _ : Fin d => h) u b.1) with hg
  have hgm : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    unfold cmwPi cmw
    fun_prop
  have hX : Measurable fun ω => noiseAt W h 0 ω 0 :=
    (measurable_pi_apply 0).comp (noiseV_measurable hW h 1)
  have hs : Measurable fun b : Noise d => b + (u, fun j => u j / 2) := measurable_add_const _
  have key := cell_cm0 hW h hh u
  have hdens : (fun ω => ENNReal.ofReal (cmwPi (fun _ : Fin d => h) u
      (fun j => W h ω j - W 0 ω j))) = fun ω => g (noiseAt W h 0 ω 0) := by
    funext ω
    simp [hg, noiseAt]
  rw [hdens, map_withDensity_comp P hX hgm hs] at key
  conv_rhs => rw [← key]
  have hc : Measurable fun b : Noise d => G (b + (u, fun j => u j / 2)) := hG.comp hs
  rw [lintegral_map hG hs, lintegral_withDensity_eq_lintegral_mul _ hgm hc]
  refine lintegral_congr fun b => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [mul_comm]

/-- Shift of a noise block by an adapted drift `U`. -/
noncomputable def shV (U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)) {k : ℕ} (v : Fin k → Noise d) :
    Fin k → Noise d :=
  fun l => v l + (U l (extN v), fun j => U l (extN v) j / 2)

/-- Girsanov weight of the shift. -/
noncomputable def wV (h : ℝ≥0) (U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)) {k : ℕ}
    (v : Fin k → Noise d) : ℝ :=
  ∏ l : Fin k, cmwPi (fun _ : Fin d => h) (U l (extN v)) (v l).1

theorem wV_nonneg (h : ℝ≥0) (U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)) {k : ℕ}
    (v : Fin k → Noise d) : 0 ≤ wV h U v :=
  Finset.prod_nonneg fun l _ => Finset.prod_nonneg fun j _ => (cmw_pos _ _ _).le

theorem shV_measurable {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)} (hUm : ∀ l, Measurable (U l))
    (k : ℕ) : Measurable (shV U (k := k)) := by
  have he := (extN_continuous (d := d) k).measurable
  refine measurable_pi_lambda _ fun l => ?_
  exact (measurable_pi_apply l).add (((hUm l).comp he).prodMk
    (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp ((hUm l).comp he)).div_const _))

theorem wV_measurable (h : ℝ≥0) {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)}
    (hUm : ∀ l, Measurable (U l)) (k : ℕ) : Measurable (wV h U (k := k)) := by
  have he := (extN_continuous (d := d) k).measurable
  unfold wV cmwPi cmw
  refine Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun j _ => ?_
  have h1 : Measurable fun v : Fin k → Noise d => U l (extN v) j :=
    (measurable_pi_apply j).comp ((hUm l).comp he)
  have h2 : Measurable fun v : Fin k → Noise d => (v l).1 j :=
    (measurable_pi_apply j).comp (measurable_fst.comp (measurable_pi_apply l))
  exact Real.measurable_exp.comp (((h1.mul h2).neg.div_const _).sub ((h1.pow_const 2).div_const _))

theorem extN_snoc_lt {k : ℕ} (a : Fin k → Noise d) (b : Noise d) {i : ℕ} (hi : i < k) :
    extN (Fin.snoc a b : Fin (k + 1) → Noise d) i = extN a i := by
  have hi' : i < k + 1 := Nat.lt_succ_of_lt hi
  simp only [extN, hi, hi', dite_true]
  have : (⟨i, hi'⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, Fin.snoc_castSucc]

theorem U_snoc {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)}
    (hUa : ∀ l (n n' : ℕ → Noise d), (∀ i < l, n i = n' i) → U l n = U l n')
    {k : ℕ} (a : Fin k → Noise d) (b : Noise d) {l : ℕ} (hl : l ≤ k) :
    U l (extN (Fin.snoc a b : Fin (k + 1) → Noise d)) = U l (extN a) :=
  hUa l _ _ fun i hi => extN_snoc_lt a b (lt_of_lt_of_le hi hl)

theorem shV_snoc {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)}
    (hUa : ∀ l (n n' : ℕ → Noise d), (∀ i < l, n i = n' i) → U l n = U l n')
    {k : ℕ} (a : Fin k → Noise d) (b : Noise d) :
    shV U (Fin.snoc a b : Fin (k + 1) → Noise d) =
      (Fin.snoc (shV U a) (b + (U k (extN a), fun j => U k (extN a) j / 2)) :
        Fin (k + 1) → Noise d) := by
  funext l
  induction l using Fin.lastCases with
  | last =>
    simp only [shV, Fin.snoc_last, Fin.val_last]
    rw [U_snoc hUa a b le_rfl]
  | cast i =>
    simp only [shV, Fin.snoc_castSucc, Fin.coe_castSucc]
    rw [U_snoc hUa a b (le_of_lt i.2)]

theorem wV_snoc (h : ℝ≥0) {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)}
    (hUa : ∀ l (n n' : ℕ → Noise d), (∀ i < l, n i = n' i) → U l n = U l n')
    {k : ℕ} (a : Fin k → Noise d) (b : Noise d) :
    wV h U (Fin.snoc a b : Fin (k + 1) → Noise d) =
      wV h U a * cmwPi (fun _ : Fin d => h) (U k (extN a)) b.1 := by
  unfold wV
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.coe_castSucc, Fin.snoc_last, Fin.val_last]
  rw [U_snoc hUa a b le_rfl]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [U_snoc hUa a b (le_of_lt i.2)]

/-- Adapted discrete Girsanov over `k` cells (C3). -/
theorem girsanov_cells [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (h : ℝ≥0) (hh : h ≠ 0)
    {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)} (hUm : ∀ l, Measurable (U l))
    (hUa : ∀ l (n n' : ℕ → Noise d), (∀ i < l, n i = n' i) → U l n = U l n') (k : ℕ)
    {F : (Fin k → Noise d) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, F (shV U v) * ENNReal.ofReal (wV h U v) ∂(P.map (noiseV W h k)) =
      ∫⁻ v, F v ∂(P.map (noiseV W h k)) := by
  induction k with
  | zero =>
    refine lintegral_congr fun v => ?_
    have hv : shV U v = v := funext fun l => l.elim0
    simp [hv, wV]
  | succ k ih =>
    set ν₁ := P.map fun ω => noiseAt W h 0 ω 0 with hν₁
    have hsn := measurable_snoc' (d := d) k
    have hsh := shV_measurable hUm (k + 1)
    have hwv := wV_measurable h hUm (k + 1)
    have hFw : Measurable fun v : Fin (k + 1) → Noise d => F (shV U v) * ENNReal.ofReal (wV h U v) :=
      (hF.comp hsh).mul (ENNReal.measurable_ofReal.comp hwv)
    have hFw' : Measurable fun p : (Fin k → Noise d) × Noise d =>
        F (shV U (Fin.snoc p.1 p.2 : Fin (k + 1) → Noise d)) *
          ENNReal.ofReal (wV h U (Fin.snoc p.1 p.2 : Fin (k + 1) → Noise d)) := hFw.comp hsn
    have hF' : Measurable fun p : (Fin k → Noise d) × Noise d =>
        F (Fin.snoc p.1 p.2 : Fin (k + 1) → Noise d) := hF.comp hsn
    rw [noiseV_succ_law hW h k, lintegral_map hFw hsn, lintegral_map hF hsn,
      lintegral_prod _ hFw'.aemeasurable, lintegral_prod _ hF'.aemeasurable]
    set G : (Fin k → Noise d) → ℝ≥0∞ := fun a =>
      ∫⁻ b, F (Fin.snoc a b : Fin (k + 1) → Noise d) ∂ν₁ with hGdef
    have hGm : Measurable G := hF'.lintegral_prod_right'
    have step : ∀ a : Fin k → Noise d,
        ∫⁻ b, F (shV U (Fin.snoc a b : Fin (k + 1) → Noise d)) *
          ENNReal.ofReal (wV h U (Fin.snoc a b : Fin (k + 1) → Noise d)) ∂ν₁ =
        G (shV U a) * ENNReal.ofReal (wV h U a) := by
      intro a
      have hsa : Measurable fun b : Noise d => (Fin.snoc (shV U a) b : Fin (k + 1) → Noise d) :=
        hsn.comp ((measurable_const (a := shV U a)).prodMk measurable_id)
      have hFa : Measurable fun b : Noise d => F (Fin.snoc (shV U a) b : Fin (k + 1) → Noise d) :=
        hF.comp hsa
      have hcm := cell_cm_lint hW h hh (U k (extN a)) hFa
      simp_rw [shV_snoc hUa, wV_snoc h hUa,
        ENNReal.ofReal_mul (wV_nonneg h U a)]
      have hcmw : Measurable fun b : Noise d =>
          ENNReal.ofReal (cmwPi (fun _ : Fin d => h) (U k (extN a)) b.1) := by
        apply ENNReal.measurable_ofReal.comp
        unfold cmwPi cmw
        fun_prop
      calc ∫⁻ b, F (Fin.snoc (shV U a) (b + (U k (extN a), fun j => U k (extN a) j / 2)) :
              Fin (k + 1) → Noise d) * (ENNReal.ofReal (wV h U a) *
              ENNReal.ofReal (cmwPi (fun _ : Fin d => h) (U k (extN a)) b.1)) ∂ν₁
          = ENNReal.ofReal (wV h U a) * ∫⁻ b, F (Fin.snoc (shV U a)
              (b + (U k (extN a), fun j => U k (extN a) j / 2)) : Fin (k + 1) → Noise d) *
              ENNReal.ofReal (cmwPi (fun _ : Fin d => h) (U k (extN a)) b.1) ∂ν₁ := by
            have hmm : Measurable fun b : Noise d => F (Fin.snoc (shV U a)
                (b + (U k (extN a), fun j => U k (extN a) j / 2)) : Fin (k + 1) → Noise d) *
                ENNReal.ofReal (cmwPi (fun _ : Fin d => h) (U k (extN a)) b.1) :=
              (hFa.comp (measurable_add_const _)).mul hcmw
            rw [← lintegral_const_mul _ hmm]
            refine lintegral_congr fun b => ?_
            ring
        _ = G (shV U a) * ENNReal.ofReal (wV h U a) := by
            rw [hcm, mul_comm]
    calc _ = ∫⁻ a, G (shV U a) * ENNReal.ofReal (wV h U a) ∂(P.map (noiseV W h k)) :=
          lintegral_congr fun a => step a
      _ = ∫⁻ a, G a ∂(P.map (noiseV W h k)) := ih hGm
      _ = _ := rfl

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

/-- The steering drift as an adapted functional of the noise sequence. -/
noncomputable def steerN (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (l : ℕ)
    (N : ℕ → Noise d) : Fin d → ℝ :=
  steer J m l (crec s₁ b₁ h J m N l q₀)

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

theorem steerN_adapted (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    ∀ l (n n' : ℕ → Noise d), (∀ i < l, n i = n' i) →
      steerN s₁ b₁ h J m q₀ l n = steerN s₁ b₁ h J m q₀ l n' := by
  intro l n n' hn
  unfold steerN
  rw [crec_congr l hn]

theorem crec_fst (N : ℕ → Noise d) (k : ℕ)
    (q : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    (crec s₁ b₁ h J m N k q).1 = zrec s₁ b₁ h N k q.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (cstep s₁ b₁ h J m k (crec s₁ b₁ h J m N k q) (N k)).1 =
      ((zrec s₁ b₁ h N k q.1).2, zstep s₁ b₁ h (zrec s₁ b₁ h N k q.1) (N k))
    simp only [cstep, ih]

theorem crec_snd (N : ℕ → Noise d) (k : ℕ)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    (crec s₁ b₁ h J m N k q₀).2 = zrec s₁ b₁ h (fun l => N l +
      (steerN s₁ b₁ h J m q₀ l N, fun j => steerN s₁ b₁ h J m q₀ l N j / 2)) k q₀.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (cstep s₁ b₁ h J m k (crec s₁ b₁ h J m N k q₀) (N k)).2 =
      ((zrec s₁ b₁ h _ k q₀.2).2, zstep s₁ b₁ h (zrec s₁ b₁ h _ k q₀.2) _)
    simp only [cstep, ih, steerN]

theorem cstep_steer (hJ : ∀ p v, avgApply s₁ p (J p v) = v) {l : ℕ} (hl : l < m)
    (q : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (n : Noise d) :
    (cstep s₁ b₁ h J m l q n).2.2 =
      zstep s₁ b₁ h q.2 n + (1 / ((m : ℝ) - l)) • (q.1.2 - q.2.2) := by
  simp only [cstep]
  rw [zstep_shift]
  simp only [steer, hl, if_true]
  rw [hJ]

/-- The steered copy is the plain scheme driven by the `shV`-shifted noise block. -/
theorem shV_crec (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (v : Fin m → Noise d) :
    zrec s₁ b₁ h (extN (shV (steerN s₁ b₁ h J m q₀) v)) m q₀.2 =
      (crec s₁ b₁ h J m (extN v) m q₀).2 := by
  rw [crec_snd]
  refine zrec_congr m (fun l hl => ?_) q₀.2
  simp only [extN, hl, dite_true, shV]

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

theorem steerN_measurable (hs : Continuous s₁) (hb : Continuous b₁)
    (hJ : Measurable (Function.uncurry J))
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (l : ℕ) :
    Measurable (steerN s₁ b₁ h J m q₀ l) := by
  have ih := crec_measurable (m := m) (h := h) hs hb hJ l q₀
  unfold steerN steer
  by_cases hk : l < m
  · simp only [hk, if_true]
    have h2 : Measurable fun N : ℕ → Noise d => (crec s₁ b₁ h J m N l q₀).2 :=
      measurable_snd.comp ih
    have h12 : Measurable fun N : ℕ → Noise d => (crec s₁ b₁ h J m N l q₀).1.2 :=
      measurable_snd.comp (measurable_fst.comp ih)
    have h22 : Measurable fun N : ℕ → Noise d => (crec s₁ b₁ h J m N l q₀).2.2 :=
      measurable_snd.comp h2
    exact hJ.comp (h2.prodMk ((h12.sub h22).const_smul (1 / ((m : ℝ) - l))))
  · simp only [hk, if_false]
    exact measurable_const

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

theorem weight_lower_bound [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hfm : Measurable f) (hf0 : ∀ ω, 0 < f ω) (hfi : Integrable f μ)
    (hf1 : ∫ ω, f ω ∂μ ≤ 1) (hgi : Integrable (fun ω => -Real.log (f ω)) μ) {K : ℝ}
    (hK : ∫ ω, -Real.log (f ω) ∂μ ≤ K) {E : Set Ω} (hE : MeasurableSet E) {a : ℝ}
    (ha : 0 < a) :
    Real.exp (-a) * (μ.real E - (K + 1) / a) ≤ ∫ ω in E, f ω ∂μ := by
  set g : Ω → ℝ := fun ω => -Real.log (f ω) with hg
  have hgm : Measurable g := (Real.measurable_log.comp hfm).neg
  have hgf0 : ∀ ω, 0 ≤ g ω + f ω := fun ω => by
    have hl : Real.log (f ω) ≤ f ω - 1 := Real.log_le_sub_one_of_pos (hf0 ω)
    simp only [hg]; linarith
  -- Markov
  have hM : μ.real {ω | a < g ω} ≤ (K + 1) / a := by
    have h1 := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hgf0) (hgi.add hfi) a
    have h2 : ∫ ω, (g ω + f ω) ∂μ ≤ K + 1 := by
      rw [integral_add hgi hfi]; linarith
    have h3 : μ.real {ω | a < g ω} ≤ μ.real {ω | a ≤ g ω + f ω} := by
      refine measureReal_mono (fun ω hω => ?_)
      simp only [mem_setOf_eq] at hω ⊢
      linarith [hf0 ω]
    rw [le_div_iff₀ ha]
    nlinarith
  set S : Set Ω := {ω | g ω ≤ a} with hS
  have hSm : MeasurableSet S := measurableSet_le hgm measurable_const
  have hfS : ∀ ω ∈ S, Real.exp (-a) ≤ f ω := fun ω hω => by
    simp only [hS, hg, mem_setOf_eq] at hω
    have : -a ≤ Real.log (f ω) := by linarith
    calc Real.exp (-a) ≤ Real.exp (Real.log (f ω)) := Real.exp_le_exp.mpr this
      _ = f ω := Real.exp_log (hf0 ω)
  have i1 : ∫ ω in E ∩ S, f ω ∂μ ≤ ∫ ω in E, f ω ∂μ :=
    setIntegral_mono_set hfi.integrableOn (ae_of_all _ fun ω => (hf0 ω).le)
      (Eventually.of_forall inter_subset_left)
  have i2 : Real.exp (-a) * μ.real (E ∩ S) ≤ ∫ ω in E ∩ S, f ω ∂μ := by
    have := setIntegral_mono_on (integrableOn_const (μ := μ) (s := E ∩ S)
      (C := Real.exp (-a)) (measure_ne_top _ _)) hfi.integrableOn (hE.inter hSm)
      (fun ω hω => hfS ω hω.2)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact this
  have i3 : μ.real E ≤ μ.real (E ∩ S) + μ.real {ω | a < g ω} := by
    refine (measureReal_mono (s₂ := (E ∩ S) ∪ {ω | a < g ω}) (fun ω hω => ?_)).trans
      (measureReal_union_le _ _)
    by_cases h : g ω ≤ a
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr (lt_of_not_ge h)
  have he : 0 < Real.exp (-a) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left (show μ.real E - (K + 1) / a ≤ μ.real (E ∩ S) by linarith)
    he.le]

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

open EthierKurtz in
/-- The Girsanov weight of an adapted shift has unit mass under `P`. -/
theorem wV_integral_one [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (h : ℝ≥0) (hh : h ≠ 0)
    {U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)} (hUm : ∀ l, Measurable (U l))
    (hUa : ∀ l (n n' : ℕ → Noise d), (∀ i < l, n i = n' i) → U l n = U l n') (k : ℕ) :
    ∫ ω, wV h U (noiseV W h k ω) ∂P = 1 := by
  have hg := girsanov_cells hW h hh hUm hUa k (F := fun _ => 1) measurable_const
  simp only [one_mul, lintegral_const, measure_univ, one_mul] at hg
  have hnm := noiseV_measurable hW h k
  have hwm := wV_measurable h hUm k
  rw [lintegral_map (f := fun v => ENNReal.ofReal (wV h U v))
    (ENNReal.measurable_ofReal.comp hwm) hnm, Measure.map_apply hnm MeasurableSet.univ,
    preimage_univ, measure_univ] at hg
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => wV_nonneg h U _)
    (hwm.comp hnm).aestronglyMeasurable]
  rw [hg]
  simp

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

theorem wV_eq_exp {d : ℕ} (h : ℝ≥0) (U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)) {k : ℕ}
    (v : Fin k → Noise d) :
    wV h U v = Real.exp (-∑ l : Fin k, ∑ j : Fin d,
      (U l (extN v) j * (v l).1 j / h + U l (extN v) j ^ 2 / (2 * h))) := by
  simp only [wV, cmwPi, cmw, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem neg_log_wV {d : ℕ} (h : ℝ≥0) (U : ℕ → (ℕ → Noise d) → (Fin d → ℝ)) {k : ℕ}
    (v : Fin k → Noise d) :
    -Real.log (wV h U v) = ∑ l : Fin k, ∑ j : Fin d,
      (U l (extN v) j * (v l).1 j / h + U l (extN v) j ^ 2 / (2 * h)) := by
  rw [wV_eq_exp, Real.log_exp, neg_neg]

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

theorem steer_measurable (hJ : Measurable (Function.uncurry J)) (l : ℕ) :
    Measurable (steer J m l) := by
  show Measurable fun q => steer J m l q
  by_cases hk : l < m
  · simp only [steer, hk, if_true]
    exact hJ.comp (measurable_snd.prodMk (((measurable_snd.comp measurable_fst).sub
      (measurable_snd.comp measurable_snd)).const_smul (1 / ((m : ℝ) - l))))
  · simp only [steer, hk, if_false]
    exact measurable_const

theorem steer_sq_le {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2) {l : ℕ}
    (hl : l < m) (q : (SDEState d × SDEState d) × (SDEState d × SDEState d)) :
    ∑ j, steer J m l q j ^ 2 ≤ Λ ^ 2 * ‖q.1.2 - q.2.2‖ ^ 2 / ((m : ℝ) - l) ^ 2 := by
  simp only [steer, hl, if_true]
  refine (hΛ _ _).trans (le_of_eq ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow, one_pow]
  ring

/-- C4d: the relative entropy of the steering weight is at most `Λ² Σ e_l/(m-l)² / (2h)`. -/
theorem kl_steer [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hm : 0 < m) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G) :
    Integrable (fun ω => -Real.log (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω))) P ∧
    ∫ ω, -Real.log (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω)) ∂P ≤
      Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) := by
  set x₀ : SDEState d := 0
  set Q : ℕ → Ω → (SDEState d × SDEState d) × (SDEState d × SDEState d) :=
    fun l ω => cq s₁ b₁ J m W h q₀ l ω with hQ
  set u : ℕ → Fin d → Ω → ℝ := fun l j ω => steer J m l (Q l ω) j with hu
  set ι : ℕ → Fin d → Ω → ℝ := fun l j ω =>
    W ((((0 + l : ℕ) : ℝ) * h).toNNReal + h) ω j - W (((0 + l : ℕ) : ℝ) * h).toNNReal ω j
    with hι
  set Dn : ℕ → Ω → ℝ := fun l ω => ‖(Q l ω).1.2 - (Q l ω).2.2‖ ^ 2 with hDn
  have hpt : ∀ ω, -Real.log (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω)) =
      ∑ l ∈ Finset.range m, ∑ j, (u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h)) := by
    intro ω
    rw [neg_log_wV, ← Fin.sum_univ_eq_sum_range
      (fun l => ∑ j, (u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h))) m]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    have e : steerN s₁ b₁ (h : ℝ) J m q₀ l (extN (noiseV W h m ω)) = steer J m l (Q l ω) := by
      simp only [steerN, hQ, cq]
      rw [crec_congr (N' := noiseAt W h 0 ω) (l : ℕ) (fun i hi => by
        simp [extN, noiseV, show i < m from hi.trans l.2])]
    rw [e]
    rfl
  have hGm : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[completedBrownianPast P W (fun _ => x₀) t] fun ω => W r ω j :=
    fun r t hrt j => coord_measurable_completedPast P W _ hrt j
  have humG : ∀ l j, Measurable[completedBrownianPast P W (fun _ => x₀)
      ((((0 + l : ℕ) : ℝ) * h).toNNReal)] (u l j) := by
    intro l j
    have hQm := crec_noise_meas_G (m := m) (J := J) hGm hW.2.1 hs hb hJm h l q₀
    rw [zero_add]
    exact (measurable_pi_apply j).comp ((steer_measurable hJm l).comp hQm)
  have huae : ∀ l j, AEStronglyMeasurable (u l j) P := fun l j =>
    aestronglyMeasurable_of_completedPast hW x₀ _ (humG l j)
  have hDi : ∀ l, l < m → Integrable (Dn l) P := by
    intro l hl
    have h2 := (crec_diff_memLp hW x₀ hh hh1 hs hb hJm hJ hL hSg hLg q₀ l hl.le).2
    have e : Dn l = fun ω => ∑ i, (((Q l ω).1.2 - (Q l ω).2.2) i) ^ 2 := by
      funext ω; simp only [hDn]; exact state_norm_sq _
    rw [e]
    exact integrable_finsetSum _ fun i _ => (h2 i).integrable_sq
  have hu2 : ∀ l, l < m → ∀ j, Integrable (fun ω => u l j ω ^ 2) P := by
    intro l hl j
    refine Integrable.mono' ((hDi l hl).const_mul (Λ ^ 2 / ((m : ℝ) - l) ^ 2))
      ((huae l j).pow 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : u l j ω ^ 2 ≤ ∑ j', u l j' ω ^ 2 :=
      Finset.single_le_sum (f := fun j' => u l j' ω ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 := steer_sq_le hΛ hl (Q l ω)
    have e : Λ ^ 2 / ((m : ℝ) - l) ^ 2 * Dn l ω =
        Λ ^ 2 * ‖(Q l ω).1.2 - (Q l ω).2.2‖ ^ 2 / ((m : ℝ) - l) ^ 2 := by
      simp only [hDn]; ring
    rw [e]
    exact h1.trans h2
  have hιL2 : ∀ l j, MemLp (ι l j) 2 P := fun l j =>
    (stdBrownian_memLp_two hW _ j).sub (stdBrownian_memLp_two hW _ j)
  have hprod : ∀ l, l < m → ∀ j, Integrable (fun ω => u l j ω * ι l j ω) P := by
    intro l hl j
    refine Integrable.mono' (((hu2 l hl j).add (hιL2 l j).integrable_sq).div_const 2)
      ((huae l j).mul (hιL2 l j).1) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    show |u l j ω| * |ι l j ω| ≤ (u l j ω ^ 2 + ι l j ω ^ 2) / 2
    nlinarith only [sq_nonneg (|u l j ω| - |ι l j ω|), sq_abs (u l j ω), sq_abs (ι l j ω)]
  have hmean : ∀ l j, ∫ ω, u l j ω * ι l j ω ∂P = 0 := fun l j =>
    past_incr_mean_zero hW x₀ _ h j (humG l j)
  have hterm : ∀ l, l < m → ∀ j,
      Integrable (fun ω => u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h)) P := fun l hl j =>
    ((hprod l hl j).div_const _).add ((hu2 l hl j).div_const _)
  have hint : Integrable (fun ω => ∑ l ∈ Finset.range m,
      ∑ j, (u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h))) P :=
    integrable_finsetSum _ fun l hl => integrable_finsetSum _ fun j _ =>
      hterm l (Finset.mem_range.1 hl) j
  have hfun : (fun ω => -Real.log (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω))) =
      fun ω => ∑ l ∈ Finset.range m, ∑ j, (u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h)) :=
    funext hpt
  refine ⟨hfun ▸ hint, ?_⟩
  rw [hfun, integral_finset_sum _ fun l hl => integrable_finsetSum _ fun j _ =>
      hterm l (Finset.mem_range.1 hl) j]
  have hstep : ∀ l ∈ Finset.range m,
      ∫ ω, ∑ j, (u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h)) ∂P ≤
        Λ ^ 2 * ((∫ ω, Dn l ω ∂P) / ((m : ℝ) - l) ^ 2) / (2 * h) := by
    intro l hl
    have hl' := Finset.mem_range.1 hl
    rw [integral_finset_sum _ fun j _ => hterm l hl' j]
    have e1 : ∀ j, ∫ ω, (u l j ω * ι l j ω / h + u l j ω ^ 2 / (2 * h)) ∂P =
        (∫ ω, u l j ω ^ 2 ∂P) / (2 * h) := fun j => by
      rw [integral_add ((hprod l hl' j).div_const _) ((hu2 l hl' j).div_const _),
        integral_div, integral_div, hmean, zero_div, zero_add]
    simp_rw [e1]
    rw [← Finset.sum_div, ← integral_finset_sum _ fun j _ => hu2 l hl' j]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hmono : ∫ ω, ∑ j, u l j ω ^ 2 ∂P ≤
        ∫ ω, Λ ^ 2 / ((m : ℝ) - l) ^ 2 * Dn l ω ∂P := by
      refine integral_mono (integrable_finsetSum _ fun j _ => hu2 l hl' j)
        ((hDi l hl').const_mul _) fun ω => ?_
      have h2 := steer_sq_le hΛ hl' (Q l ω)
      have e : Λ ^ 2 / ((m : ℝ) - l) ^ 2 * Dn l ω =
          Λ ^ 2 * ‖(Q l ω).1.2 - (Q l ω).2.2‖ ^ 2 / ((m : ℝ) - l) ^ 2 := by
        simp only [hDn]; ring
      rw [e]
      exact h2
    rw [integral_const_mul] at hmono
    calc ∫ ω, ∑ j, u l j ω ^ 2 ∂P ≤ Λ ^ 2 / ((m : ℝ) - l) ^ 2 * ∫ ω, Dn l ω ∂P := hmono
      _ = Λ ^ 2 * ((∫ ω, Dn l ω ∂P) / ((m : ℝ) - l) ^ 2) := by ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_div, ← Finset.mul_sum]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (by positivity)
  exact (crec_diff_bounds hW x₀ hh hh1 hs hb hJm hJ hL hSg hLg q₀ hm hG1 hG2).2

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

/-- Current difference `X_k - Ŷ_k`. -/
noncomputable def tD (k : ℕ) (ω : Ω) : SDEState d :=
  (cq s₁ b₁ J m W h q₀ k ω).1.2 - (cq s₁ b₁ J m W h q₀ k ω).2.2

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
  have key := EthierKurtz.steered_euler_coupling_tracking hW hh hh1 hs hb hJm hJ hL hSg hLg hm2
    (fun l ω => (noiseAt W h 0 ω l).1) (fun l ω => (noiseAt W h 0 ω l).2)
    (fun l ω j => by simp only [noiseAt, Nat.zero_add])
    (fun l ω j => by simp only [noiseAt, cellZeta, zetaF, Nat.zero_add])
    (fun p a c => zstep s₁ b₁ (h : ℝ) p (a, c)) (fun p a c => rfl)
    (cq s₁ b₁ J m W h q₀) q₀ (fun ω => rfl)
    (fun k ω => steer J m k (cq s₁ b₁ J m W h q₀ k ω)) (fun k ω => rfl)
    (fun k ω => rfl) hδ hG1 hG2
  exact key
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

theorem shV_crec_le (h : ℝ) (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (v : Fin m → Noise d) {k : ℕ} (hk : k ≤ m) :
    zrec s₁ b₁ h (extN (shV (steerN s₁ b₁ h J m q₀) v)) k q₀.2 =
      (crec s₁ b₁ h J m (extN v) k q₀).2 := by
  rw [crec_snd]
  refine zrec_congr k (fun l hl => ?_) q₀.2
  have hl' : l < m := lt_of_lt_of_le hl hk
  simp only [extN, hl', dite_true, shV]

theorem steer_girsanov_path [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1) (hs : Continuous s₁) (hb : Continuous b₁)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₁ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hm : 0 < m) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G)
    {Ap : Set (Fin (m + 1) → SDEState d)} (hAp : MeasurableSet Ap) {a : ℝ} (ha : 0 < a) :
    Real.exp (-a) * (P.real {ω | (fun k : Fin (m + 1) => (cq s₁ b₁ J m W h q₀ k ω).2.2) ∈ Ap} -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (fun k : Fin (m + 1) =>
        (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2) ∈ Ap} := by
  have hUm : ∀ l, Measurable (steerN s₁ b₁ (h : ℝ) J m q₀ l) := fun l =>
    steerN_measurable hs hb hJm q₀ l
  have hUa := steerN_adapted (s₁ := s₁) (b₁ := b₁) (h := (h : ℝ)) (J := J) (m := m) q₀
  have hh0 : h ≠ 0 := by
    intro e; rw [e] at hh; simp at hh
  have hnm := noiseV_measurable hW h m
  have he := (extN_continuous (d := d) m).measurable
  have hfm : Measurable fun ω => wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω) :=
    (wV_measurable h hUm m).comp hnm
  have hf0 : ∀ ω, 0 < wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω) := fun ω =>
    Finset.prod_pos fun l _ => Finset.prod_pos fun j _ => cmw_pos _ _ _
  have hf1 : ∫ ω, wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω) ∂P = 1 :=
    wV_integral_one hW h hh0 hUm hUa m
  have hfi : Integrable (fun ω => wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω)) P :=
    Integrable.of_integral_ne_zero (by rw [hf1]; exact one_ne_zero)
  obtain ⟨hgi, hK⟩ := kl_steer hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ q₀ hm hG1 hG2
  have hGa : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable fun ω => W r ω j :=
    fun r _ _ j => stdBrownian_coord_measurable hW r j
  have hQm : ∀ k, Measurable fun ω => cq s₁ b₁ J m W h q₀ k ω := fun k => by
    have := crec_noise_meas_G (W := W) (G := fun _ => ‹MeasurableSpace Ω›) (s₁ := s₁)
      (b₁ := b₁) (J := J) (m := m) hGa hW.2.1 hs hb hJm h k q₀
    exact this
  set E : Set Ω := {ω | (fun k : Fin (m + 1) => (cq s₁ b₁ J m W h q₀ k ω).2.2) ∈ Ap} with hE
  have hEm : MeasurableSet E := by
    have hpm' : Measurable fun ω => (fun k : Fin (m + 1) => (cq s₁ b₁ J m W h q₀ k ω).2.2) :=
      measurable_pi_lambda _ fun k => measurable_snd.comp (measurable_snd.comp (hQm k))
    exact hpm' hAp
  have hwl := weight_lower_bound hfm hf0 hfi hf1.le hgi hK hEm ha
  have hcr : ∀ ω (k : Fin (m + 1)), crec s₁ b₁ (h : ℝ) J m (extN (noiseV W h m ω)) k q₀ =
      cq s₁ b₁ J m W h q₀ k ω := fun ω k =>
    crec_congr (k : ℕ) (fun i hi => by
      have hi' : i < m := lt_of_lt_of_le hi (Nat.lt_succ_iff.1 k.2)
      simp [extN, noiseV, hi']) q₀
  have hzr : ∀ ω (k : Fin (m + 1)) (p : SDEState d × SDEState d),
      zrec s₁ b₁ (h : ℝ) (extN (noiseV W h m ω)) k p =
      zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k p := fun ω k p =>
    zrec_congr (k : ℕ) (fun i hi => by
      have hi' : i < m := lt_of_lt_of_le hi (Nat.lt_succ_iff.1 k.2)
      simp [extN, noiseV, hi']) p
  set pth : (Fin m → Noise d) → (Fin (m + 1) → SDEState d) := fun v k =>
    (zrec s₁ b₁ (h : ℝ) (extN v) k q₀.2).2 with hpth
  set F : (Fin m → Noise d) → ℝ≥0∞ := fun v => Ap.indicator (1 : (Fin (m + 1) → SDEState d) → ℝ≥0∞) (pth v) with hF
  have hpm : Measurable pth := measurable_pi_lambda _ fun k =>
    measurable_snd.comp ((zrec_continuous (h := (h : ℝ)) hs hb (k : ℕ)).measurable.comp
      (he.prodMk measurable_const))
  have hFm : Measurable F := (measurable_one.indicator hAp).comp hpm
  have hshV : Measurable fun v : Fin m → Noise d => shV (steerN s₁ b₁ (h : ℝ) J m q₀) v :=
    measurable_pi_lambda _ fun l => (measurable_pi_apply l).add
      (((hUm l).comp he).prodMk (measurable_pi_lambda _ fun j =>
        ((measurable_pi_apply j).comp ((hUm l).comp he)).div_const 2))
  have hgir := girsanov_cells hW h hh0 hUm hUa m hFm
  rw [lintegral_map (f := fun v => F (shV (steerN s₁ b₁ (h : ℝ) J m q₀) v) *
      ENNReal.ofReal (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) v)) ((hFm.comp hshV).mul
      (ENNReal.measurable_ofReal.comp (wV_measurable h hUm m))) hnm,
    lintegral_map hFm hnm] at hgir
  have hLw : ∀ ω, F (shV (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω)) *
      ENNReal.ofReal (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω)) =
      E.indicator (fun ω => ENNReal.ofReal
        (wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω))) ω := by
    intro ω
    have hp : pth (shV (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω)) =
        fun k : Fin (m + 1) => (cq s₁ b₁ J m W h q₀ k ω).2.2 := by
      funext k
      simp only [hpth]
      rw [shV_crec_le (h : ℝ) q₀ _ (Nat.lt_succ_iff.1 k.2), hcr]
    simp only [hF]
    rw [hp]
    by_cases hx : (fun k : Fin (m + 1) => (cq s₁ b₁ J m W h q₀ k ω).2.2) ∈ Ap
    · simp [Set.indicator, hE, hx]
    · simp [Set.indicator, hE, hx]
  set Y : Set Ω := {ω | (fun k : Fin (m + 1) =>
    (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2) ∈ Ap} with hY
  have hpY : ∀ ω, pth (noiseV W h m ω) = fun k : Fin (m + 1) =>
      (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2 := fun ω => by
    funext k; simp only [hpth]; rw [hzr]
  have hYm : MeasurableSet Y := by
    have e : Y = (fun ω => pth (noiseV W h m ω)) ⁻¹' Ap := by
      ext ω; simp only [hY, Set.mem_setOf_eq, Set.mem_preimage, hpY]
    rw [e]
    exact (hpm.comp hnm) hAp
  have hR : ∀ ω, F (noiseV W h m ω) = Y.indicator 1 ω := by
    intro ω
    simp only [hF]
    rw [hpY]
    by_cases hx : (fun k : Fin (m + 1) =>
        (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2) ∈ Ap
    · simp [Set.indicator, hY, hx]
    · simp [Set.indicator, hY, hx]
  simp_rw [hLw, hR] at hgir
  rw [lintegral_indicator hEm, lintegral_indicator_one hYm,
    ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (ae_of_all _ fun ω => (hf0 ω).le)] at hgir
  have hYr : P.real Y = ∫ ω in E, wV h (steerN s₁ b₁ (h : ℝ) J m q₀) (noiseV W h m ω) ∂P := by
    rw [measureReal_def, ← hgir, ENNReal.toReal_ofReal
      (setIntegral_nonneg hEm fun ω _ => (hf0 ω).le)]
  rw [hYr]
  exact hwl

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

/-- Deterministic core: on the good event the steered path ends in `A` and stays in `Bx`. -/
theorem steer_good_path {x y : SDEState d} {X D : ℕ → SDEState d} {δ ε : ℝ} (hεδ : ε ≤ δ)
    (hm : 0 < m) (hD0 : D 0 = x - y) {A B Bx : Set (SDEState d)}
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (hXB : X m ∈ B) (hexit : ∀ k ≤ m, ‖X k - x‖ < δ)
    (htr : ∀ k ≤ m - 1, ‖D k - (((m : ℝ) - k) / m) • D 0‖ < δ) (hDm : ‖D m‖ < ε) :
    X m - D m ∈ A ∧ ∀ k ≤ m, X k - D k ∈ Bx := by
  refine ⟨hB _ hXB _ (by simpa [norm_neg] using hDm), fun k hk => ?_⟩
  rcases Nat.lt_or_ge k m with hkm | hkm
  · have hk1 : k ≤ m - 1 := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
    refine hBx ((((m : ℝ) - k) / m)) (div_nonneg (by linarith) hmR.le)
      ((div_le_one hmR).2 (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) _ ?_
    have e : X k - D k - (x - (((m : ℝ) - k) / m) • (x - y)) =
        (X k - x) - (D k - (((m : ℝ) - k) / m) • D 0) := by rw [hD0]; abel
    rw [e]
    calc ‖(X k - x) - (D k - (((m : ℝ) - k) / m) • D 0)‖
        ≤ ‖X k - x‖ + ‖D k - (((m : ℝ) - k) / m) • D 0‖ := norm_sub_le _ _
      _ < δ + δ := add_lt_add (hexit k hk) (htr k hk1)
      _ = 2 * δ := by ring
  · have hkm' : k = m := le_antisymm hk hkm
    subst hkm'
    refine hBx 0 le_rfl zero_le_one _ ?_
    have e : X k - D k - (x - (0 : ℝ) • (x - y)) = (X k - x) - D k := by simp; abel
    rw [e]
    calc ‖(X k - x) - D k‖ ≤ ‖X k - x‖ + ‖D k‖ := norm_sub_le _ _
      _ < δ + ε := add_lt_add (hexit k hk) hDm
      _ ≤ 2 * δ := by linarith

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
  have hm : 0 < m := by omega
  set Ap : Set (Fin (m + 1) → SDEState d) :=
    {f | f (Fin.last m) ∈ A ∧ ∀ k, f k ∈ Bx} with hAp
  have hApm : MeasurableSet Ap := by
    rw [hAp, Set.setOf_and]
    refine ((measurable_pi_apply (Fin.last m)) hA).inter ?_
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => (measurable_pi_apply k) hBxm
  have hgp := steer_girsanov_path hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ q₀ hm hG1 hG2 hApm ha
  -- the Y-side set
  have hYeq : {ω | (fun k : Fin (m + 1) => (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2) ∈ Ap} =
      {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m q₀.2).2 ∈ A ∧
        ∀ k ≤ m, (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.2).2 ∈ Bx} := by
    ext ω
    simp only [hAp, Set.mem_setOf_eq, Fin.val_last]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k hk => h2 ⟨k, Nat.lt_succ_of_le hk⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k => h2 k (Nat.lt_succ_iff.1 k.2)⟩
  rw [hYeq] at hgp
  refine le_trans ?_ hgp
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- bad events
  set Ex : Set Ω := {ω | ∃ k ≤ m, δ ≤ ‖(zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.1).2 - q₀.1.2‖}
    with hEx
  set Tr : Set Ω := {ω | ∃ k ≤ m - 1, δ ≤ ‖tD s₁ b₁ J m W h q₀ k ω -
      (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω‖} with hTr
  set Dn : Ω → ℝ := fun ω => ‖(cq s₁ b₁ J m W h q₀ m ω).1.2 - (cq s₁ b₁ J m W h q₀ m ω).2.2‖ ^ 2
    with hDn
  set Ch : Set Ω := {ω | ε ^ 2 ≤ Dn ω} with hCh
  set E : Set Ω := {ω | (fun k : Fin (m + 1) => (cq s₁ b₁ J m W h q₀ k ω).2.2) ∈ Ap} with hE
  have hsub : {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m q₀.1).2 ∈ B} ⊆
      ((E ∪ Ex) ∪ Tr) ∪ Ch := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    obtain ⟨⟨⟨hnE, hnEx⟩, hnTr⟩, hnCh⟩ := hn
    have hX : ∀ k, (cq s₁ b₁ J m W h q₀ k ω).1.2 = (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k q₀.1).2 :=
      fun k => by rw [cq, crec_fst]
    have hexit : ∀ k ≤ m, ‖(cq s₁ b₁ J m W h q₀ k ω).1.2 - q₀.1.2‖ < δ := fun k hk => by
      rw [hX]; by_contra hc; exact hnEx ⟨k, hk, not_lt.1 hc⟩
    have htr : ∀ k ≤ m - 1, ‖tD s₁ b₁ J m W h q₀ k ω -
        (((m : ℝ) - k) / m) • tD s₁ b₁ J m W h q₀ 0 ω‖ < δ := fun k hk => by
      by_contra hc; exact hnTr ⟨k, hk, not_lt.1 hc⟩
    have hDm : ‖tD s₁ b₁ J m W h q₀ m ω‖ < ε := by
      by_contra hc
      apply hnCh
      simp only [hCh, hDn, Set.mem_setOf_eq]
      exact pow_le_pow_left₀ hε.le (not_lt.1 hc) 2
    have hg := steer_good_path (m := m) (x := q₀.1.2) (y := q₀.2.2)
      (X := fun k => (cq s₁ b₁ J m W h q₀ k ω).1.2) (D := fun k => tD s₁ b₁ J m W h q₀ k ω)
      hεδ hm rfl hB hBx (by rw [hX]; exact hω) hexit htr hDm
    apply hnE
    simp only [hE, hAp, Set.mem_setOf_eq]
    have hY : ∀ k, (cq s₁ b₁ J m W h q₀ k ω).1.2 - tD s₁ b₁ J m W h q₀ k ω =
        (cq s₁ b₁ J m W h q₀ k ω).2.2 := fun k => by simp [tD]
    refine ⟨?_, fun k => ?_⟩
    · have := hg.1; simp only [hY] at this; simpa using this
    · have := hg.2 k (Nat.lt_succ_iff.1 k.2); simp only [hY] at this; exact this
  have hX4 : P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m q₀.1).2 ∈ B} ≤
      P.real E + P.real Ex + P.real Tr + P.real Ch := by
    refine (measureReal_mono hsub).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    have h1 := measureReal_union_le (μ := P) (E ∪ Ex) Tr
    have h2 := measureReal_union_le (μ := P) E Ex
    linarith
  -- exit
  have hExb : P.real Ex ≤ 16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2 := by
    have := chain_exit hW hh hs hb hSg q₀.1 m hδ hT
    rw [le_div_iff₀ (by positivity)]; linarith
  -- tracking
  have hTrb := track_final hW hh hh1 hs hb hJm hJ hL hSg hLg q₀ hm2 hδ hG1 hG2
  -- Chebyshev
  have hDi : Integrable Dn P := by
    have h2 := (crec_diff_memLp hW (0 : SDEState d) hh hh1 hs hb hJm hJ hL hSg hLg q₀ m le_rfl).2
    have e : Dn = fun ω => ∑ i, (((cq s₁ b₁ J m W h q₀ m ω).1.2 -
        (cq s₁ b₁ J m W h q₀ m ω).2.2) i) ^ 2 := by
      funext ω; simp only [hDn]; exact state_norm_sq _
    rw [e]
    exact integrable_finsetSum _ fun i _ => (h2 i).integrable_sq
  have hDb := (crec_diff_bounds hW (0 : SDEState d) hh hh1 hs hb hJm hJ hL hSg hLg q₀ hm
    hG1 hG2).1
  have hcheb : ε ^ 2 * P.real Ch ≤ ∫ ω, Dn ω ∂P :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) hDi _
  have hChb : P.real Ch ≤
      5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
        (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : ∫ ω, Dn ω ∂P ≤ 5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
        (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 := hDb
    linarith
  linarith

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
theorem slb_bridge {Ω : Type*} {d : ℕ} {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0}
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (ξ ζ : ℕ → Ω → Fin d → ℝ)
    (hξ : ∀ l ω j, ξ l ω j = W (((l : ℝ) * h).toNNReal + h) ω j - W ((l : ℝ) * h).toNNReal ω j)
    (hζ : ∀ l ω j, ζ l ω j = (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h,
      (W (((l : ℝ) * h).toNNReal + h) ω j - W (((l : ℝ) * h).toNNReal + u.toNNReal) ω j))
    (Z : SDEState d × SDEState d → (Fin d → ℝ) → (Fin d → ℝ) → SDEState d)
    (hZ : ∀ p a c, Z p a c = p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * a j +
      (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * c j) + (h : ℝ) / 2 * (b₁ p.1 i + b₁ p.2 i)))
    (Y : SDEState d × SDEState d → ℕ → Ω → SDEState d × SDEState d)
    (hY0 : ∀ p ω, Y p 0 ω = p) (hY : ∀ p k ω, Y p (k + 1) ω = ((Y p k ω).2, Z (Y p k ω) (ξ k ω) (ζ k ω)))
 :
    ∀ p k ω, Y p k ω = zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k p := by
  have hZ' : ∀ p a c, Z p a c = zstep s₁ b₁ (h : ℝ) p (a, c) := fun p a c => by rw [hZ]; rfl
  intro p k
  induction k with
  | zero => intro ω; rw [hY0]; rfl
  | succ k ih =>
    intro ω
    have e1 : ξ k ω = (noiseAt W h 0 ω k).1 := funext fun j => by
      rw [hξ]; simp only [noiseAt, Nat.zero_add]
    have e2 : ζ k ω = (noiseAt W h 0 ω k).2 := funext fun j => by
      rw [hζ]; simp only [noiseAt, cellZeta, zetaF, Nat.zero_add]
    rw [hY, e1, e2, ih, hZ']
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
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {m : ℕ} (hm2 : 2 ≤ m) (ξ ζ : ℕ → Ω → Fin d → ℝ)
    (hξ : ∀ l ω j, ξ l ω j = W (((l : ℝ) * h).toNNReal + h) ω j - W ((l : ℝ) * h).toNNReal ω j)
    (hζ : ∀ l ω j, ζ l ω j = (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h,
      (W (((l : ℝ) * h).toNNReal + h) ω j - W (((l : ℝ) * h).toNNReal + u.toNNReal) ω j))
    (Z : SDEState d × SDEState d → (Fin d → ℝ) → (Fin d → ℝ) → SDEState d)
    (hZ : ∀ p a c, Z p a c = p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * a j +
      (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * c j) + (h : ℝ) / 2 * (b₁ p.1 i + b₁ p.2 i)))
    (Y : SDEState d × SDEState d → ℕ → Ω → SDEState d × SDEState d)
    (hY0 : ∀ p ω, Y p 0 ω = p) (hY : ∀ p k ω, Y p (k + 1) ω = ((Y p k ω).2, Z (Y p k ω) (ξ k ω) (ζ k ω)))
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G)
    {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) (ha : 0 < a)
    (hT : m * (h * S) ≤ δ / 2)
    {A B Bx : Set (SDEState d)} (hA : MeasurableSet A) (hBxm : MeasurableSet Bx)
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z,
      ‖z - (q₀.1.2 - t • (q₀.1.2 - q₀.2.2))‖ < 2 * δ → z ∈ Bx) :
    Real.exp (-a) * (P.real {ω | (Y q₀.1 m ω).2 ∈ B} -
        16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2 -
        4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
          (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (Y q₀.2 m ω).2 ∈ A ∧ ∀ k ≤ m, (Y q₀.2 k ω).2 ∈ Bx} := by
  have hbr := ItoLib.slb_bridge ξ ζ hξ hζ Z hZ Y hY0 hY
  have key := ItoLib.steer_lower_box (J := J) (m := m) hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ q₀ hm2
    hG1 hG2 hδ hε hεδ ha hT hA hBxm hB hBx
  simp only [hbr]
  exact key
