-- Prove2me | solution 1 for EthierKurtz.brownian_ito_integral_locality_and_continuity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T04:15:24.735052+00:00
-- url     : https://prove2.me/submissions/1c8335b9-4054-42eb-97ee-3c7e3634c0de

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option linter.all false


-- ===== ItoM1 =====
section FlatM_ItoM1

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

/-- Coefficients stopped once the running discrete quadratic variation exceeds `δ`. -/
noncomputable def stopCoef (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if (∑ i ∈ Finset.range (k + 1), c i ω ^ 2) * h ≤ δ then c k ω else 0

theorem stopCoef_eq_of_le (c : ℕ → Ω → ℝ) {h δ : ℝ} (hh : 0 ≤ h) {N : ℕ} {ω : Ω}
    (hN : (∑ i ∈ Finset.range N, c i ω ^ 2) * h ≤ δ) {k : ℕ} (hk : k < N) :
    stopCoef c h δ k ω = c k ω := by
  unfold stopCoef
  rw [if_pos]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hh) hN
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hk))
    (fun i _ _ => sq_nonneg _)

theorem stopCoef_sum_le (c : ℕ → Ω → ℝ) {h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ) (N : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range N, stopCoef c h δ k ω ^ 2) * h ≤ δ := by
  induction N with
  | zero => simpa using hδ
  | succ N ih =>
    by_cases hN : (∑ i ∈ Finset.range (N + 1), c i ω ^ 2) * h ≤ δ
    · have : ∑ k ∈ Finset.range (N + 1), stopCoef c h δ k ω ^ 2 =
          ∑ k ∈ Finset.range (N + 1), c k ω ^ 2 :=
        Finset.sum_congr rfl fun k hk => by
          rw [stopCoef_eq_of_le c hh hN (Finset.mem_range.1 hk)]
      rw [this]; exact hN
    · rw [Finset.sum_range_succ]
      have : stopCoef c h δ N ω = 0 := by unfold stopCoef; rw [if_neg hN]
      rw [this]; simpa using ih

theorem abs_stopCoef_le (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ) (ω : Ω) :
    |stopCoef c h δ k ω| ≤ |c k ω| := by
  unfold stopCoef; split_ifs <;> simp

theorem stopCoef_measurable [m : MeasurableSpace Ω] (c : ℕ → Ω → ℝ) (h δ : ℝ) (k : ℕ)
    (hc : ∀ i, i ≤ k → Measurable (c i)) : Measurable (stopCoef c h δ k) := by
  unfold stopCoef
  refine Measurable.ite ?_ (hc k le_rfl) measurable_const
  refine measurableSet_le ?_ measurable_const
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun i hi =>
    (hc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).pow_const 2

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

/-- Localized Chebyshev bound for discrete Ito sums: the sum is large only if the discrete
quadratic variation of the integrand exceeds `δ`, or with probability at most `δ / ε²`. -/
theorem itoStepSum_local_chebyshev {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (n : ℕ) (j : Fin d)
    (c : ℕ → Ω → ℝ)
    (hc : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c k))
    (C : ℝ) (hC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c k ω| ≤ C) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) :
    P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|} ≤
      ENNReal.ofReal (δ / ε ^ 2) +
      P {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) *
        ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)} := by
  have hP : IsProbabilityMeasure P := (hW.2.2.1 j).isGaussianProcess.isProbabilityMeasure
  set h : ℝ := ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) with hhdef
  have hh : 0 ≤ h := NNReal.coe_nonneg _
  have hsm : ∀ k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (stopCoef c h δ k) := by
    intro k hk
    exact stopCoef_measurable (m := completedBrownianPast P W (fun _ => x₀) _) c h δ k
      (fun i hi => (hc i (lt_of_le_of_lt hi hk)).mono
        (completedBrownianPast_mono P W _ (by gcongr)) le_rfl)
  have hsC : ∀ k : ℕ, k < 2 ^ n → ∀ ω, |stopCoef c h δ k ω| ≤ C := fun k hk ω =>
    (abs_stopCoef_le c h δ k ω).trans (hC k hk ω)
  have hiso := itoStepSum_isometry hW x₀ t n j (stopCoef c h δ) hsm C hsC
  have hL2 := itoStepSum_memLp hW t n j (stopCoef c h δ)
    (fun k hk => aestronglyMeasurable_of_completedPast hW x₀ _ (hsm k hk)) C hsC
  have hint : ∀ k ∈ Finset.range (2 ^ n), Integrable (fun ω => stopCoef c h δ k ω ^ 2) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine Integrable.of_bound
      ((aestronglyMeasurable_of_completedPast hW x₀ _ (hsm k hk')).pow 2) (C ^ 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsC k hk' ω) 2
  have hE : ∫ ω, (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2 ∂P ≤ δ := by
    rw [hiso]
    calc ∑ k ∈ Finset.range (2 ^ n), (∫ ω, stopCoef c h δ k ω ^ 2 ∂P) * h
        = (∫ ω, ∑ k ∈ Finset.range (2 ^ n), stopCoef c h δ k ω ^ 2 ∂P) * h := by
          rw [integral_finsetSum _ hint, Finset.sum_mul]
      _ = ∫ ω, (∑ k ∈ Finset.range (2 ^ n), stopCoef c h δ k ω ^ 2) * h ∂P := by
          rw [integral_mul_const]
      _ ≤ ∫ _ω, δ ∂P := integral_mono ((integrable_finsetSum _ hint).mul_const h)
          (integrable_const δ) (fun ω => stopCoef_sum_le c hh hδ _ ω)
      _ = δ := by simp
  have hsub : {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|} ⊆
      {ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ∪
      {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h} := by
    intro ω hω
    by_cases hq : (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h ≤ δ
    · left
      have heq : itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω =
          itoStepSum (fun s ω => W s ω j) t n c ω := by
        unfold itoStepSum
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [stopCoef_eq_of_le c hh hq (Finset.mem_range.1 hk)]
      show ε ^ 2 ≤ _
      rw [heq]
      calc ε ^ 2 ≤ |itoStepSum (fun s ω => W s ω j) t n c ω| ^ 2 :=
            pow_le_pow_left₀ hε.le hω 2
        _ = _ := sq_abs _
    · right; exact lt_of_not_ge hq
  have hA : P {ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ≤
      ENNReal.ofReal (δ / ε ^ 2) := by
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun ω => sq_nonneg
        (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω)) hL2.integrable_sq (ε ^ 2)
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hε2, mul_comm]
    exact hm.trans hE
  calc P {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n c ω|}
      ≤ P ({ω | ε ^ 2 ≤ (itoStepSum (fun s ω => W s ω j) t n (stopCoef c h δ) ω) ^ 2} ∪
          {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * h}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add_left hA _

/-- Discrete Ito sums whose integrands have discrete quadratic variation tending to zero in
probability tend to zero in probability. -/
theorem itoStepSum_tendstoInMeasure_zero {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (t : ℝ≥0) (j : Fin d)
    (c : ℕ → ℕ → Ω → ℝ)
    (hc : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c n k))
    (hC : ∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C)
    (hq : TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure P (fun n => itoStepSum (fun s ω => W s ω j) t n (c n)) atTop
      (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hq ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Filter.Eventually.of_forall fun _ => le_top
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he2top : e / 2 ≠ ⊤ := ENNReal.div_ne_top hetop (by norm_num)
  set δ : ℝ := (e / 2).toReal * ε ^ 2 with hδdef
  have hδpos : 0 < δ := mul_pos (ENNReal.toReal_pos he2.ne' he2top) (by positivity)
  have hδe : ENNReal.ofReal (δ / ε ^ 2) = e / 2 := by
    rw [hδdef, mul_div_cancel_right₀ _ (by positivity), ENNReal.ofReal_toReal he2top]
  have h2 := (ENNReal.tendsto_nhds_zero.1 (hq δ hδpos)) (e / 2) he2
  filter_upwards [h2] with n hn
  obtain ⟨C, hCn⟩ := hC n
  have hset : {ω | ε ≤ dist (itoStepSum (fun s ω => W s ω j) t n (c n) ω) 0} =
      {ω | ε ≤ |itoStepSum (fun s ω => W s ω j) t n (c n) ω|} := by
    ext ω; simp
  rw [hset]
  calc _ ≤ ENNReal.ofReal (δ / ε ^ 2) +
        P {ω | δ < (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
          ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)} :=
        itoStepSum_local_chebyshev hW x₀ t n j (c n) (hc n) C hCn hε hδpos.le
    _ ≤ e / 2 + e / 2 := by
        rw [hδe]
        refine add_le_add le_rfl (le_trans (measure_mono fun ω hω => ?_) hn)
        simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
        exact hω.le.trans (le_abs_self _)
    _ = e := ENNReal.add_halves e

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
  linarith

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
  constructor <;> linarith [le_abs_self (f i ω - g ω), neg_abs_le (f i ω - g ω),
    le_abs_self (f' i ω - g' ω), neg_abs_le (f' i ω - g' ω)]

theorem itoStepValue_sub (t : ℝ≥0) (n : ℕ) (a b : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n a u ω - itoStepValue t n b u ω =
      itoStepValue t n (fun k ω => a k ω - b k ω) u ω := by
  unfold itoStepValue
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

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

theorem itoStepValue_sq (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    (itoStepValue t n c u ω) ^ 2 = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key : ∀ p q : ℕ, p < q →
      ((p : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ (q : ℝ) * t.val / (2 : ℝ) ^ n := by
    intro p q hpq
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) h2.le
  unfold itoStepValue
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · simp only [Set.indicator_apply, Set.mem_Ioc]; split_ifs <;> ring
  · intro l _ hlk
    split_ifs with h1 h2 <;> try ring
    exfalso
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · linarith [key l k hlt, h1.1, h2.2]
    · linarith [key k l hgt, h1.2, h2.1]
  · intro hk'; exact absurd hk hk'

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

theorem itoStepValue_sq_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue t n c u ω) ^ 2) volume 0 t.val := by
  have heq : (fun u => (itoStepValue t n c u ω) ^ 2) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_sq]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

theorem itoStepValue_sq_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n c u ω) ^ 2 =
      (∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_sq]
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

end M5b

section M5c
variable [MeasurableSpace Ω]

/-- The local Ito integral of `HasBrownianItoIntegral` is unique up to null sets at each time,
for integrands with continuous paths. -/
theorem hasBrownianItoIntegral_ae_unique {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H J J' : ℝ≥0 → Ω → ℝ}
    (hH : ∀ ω, Continuous (fun u : ℝ => H u.toNNReal ω))
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J')
    (t : ℝ≥0) : J t =ᵐ[P] J' t := by
  obtain ⟨a, ham, haC, haH, haJ⟩ := hJ.2 t
  obtain ⟨b, hbm, hbC, hbH, hbJ⟩ := hJ'.2 t
  have hT : (0 : ℝ) ≤ t.val := t.2
  let c : ℕ → ℕ → Ω → ℝ := fun n k ω => a n k ω - b n k ω
  have hcm : ∀ n k : ℕ, k < 2 ^ n → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (c n k) := fun n k hk =>
    (ham n k hk).sub (hbm n k hk)
  have hcC : ∀ n, ∃ C : ℝ, ∀ k : ℕ, k < 2 ^ n → ∀ ω, |c n k ω| ≤ C := by
    intro n
    obtain ⟨C1, h1⟩ := haC n
    obtain ⟨C2, h2⟩ := hbC n
    refine ⟨C1 + C2, fun k hk ω => ?_⟩
    have h1' := abs_le.1 (h1 k hk ω)
    have h2' := abs_le.1 (h2 k hk ω)
    exact abs_le.2 ⟨by simp only [c]; linarith [h1'.1, h2'.2],
      by simp only [c]; linarith [h1'.2, h2'.1]⟩
  -- integrability of the squared errors
  have hfi : ∀ (n : ℕ) (e : ℕ → Ω → ℝ) ω, IntervalIntegrable
      (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) volume 0 t.val := by
    intro n e ω
    have h1 := itoStepValue_sq_intervalIntegrable t n e ω
    have h2 := (itoStepValue_intervalIntegrable t n e ω).mul_continuousOn (hH ω).continuousOn
    have h3 := ((hH ω).pow 2).intervalIntegrable (μ := volume) 0 t.val
    have h4 := (h1.sub (h2.const_mul 2)).add h3
    have heq : (fun u => (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2) = fun u =>
        (itoStepValue t n e u ω) ^ 2 - 2 * (itoStepValue t n e u ω * H u.toNNReal ω) +
          H u.toNNReal ω ^ 2 := by
      funext u; ring
    rw [heq]; exact h4
  have hq : TendstoInMeasure P (fun n ω => (∑ k ∈ Finset.range (2 ^ n), c n k ω ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_zero_of_abs_le (K := 2) two_pos haH hbH (fun n ω => ?_)
    rw [← itoStepValue_sq_integral]
    have hfa := hfi n (a n) ω
    have hfb := hfi n (b n) ω
    have hnn : ∀ e : ℕ → Ω → ℝ, 0 ≤ ∫ u in (0 : ℝ)..t.val,
        (itoStepValue t n e u ω - H u.toNNReal ω) ^ 2 :=
      fun e => intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)),
      abs_of_nonneg (hnn (a n)), abs_of_nonneg (hnn (b n))]
    calc ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (c n) u ω) ^ 2
        ≤ ∫ u in (0 : ℝ)..t.val, (2 * (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2 +
            2 * (itoStepValue t n (b n) u ω - H u.toNNReal ω) ^ 2) := by
          refine intervalIntegral.integral_mono_on hT
            (itoStepValue_sq_intervalIntegrable t n (c n) ω)
            ((hfa.const_mul 2).add (hfb.const_mul 2)) (fun u _ => ?_)
          rw [← itoStepValue_sub]
          nlinarith [sq_nonneg (itoStepValue t n (a n) u ω - H u.toNNReal ω +
            (itoStepValue t n (b n) u ω - H u.toNNReal ω))]
      _ = 2 * ((∫ u in (0 : ℝ)..t.val, (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2) +
            ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (b n) u ω - H u.toNNReal ω) ^ 2) := by
          rw [intervalIntegral.integral_add (hfa.const_mul 2) (hfb.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          ring
  have hS := itoStepSum_tendstoInMeasure_zero hW x₀ t j c hcm hcC hq
  have hsub := tendstoInMeasure_sub_real haJ hbJ
  have hsub' : TendstoInMeasure P (fun n => itoStepSum (fun s ω => W s ω j) t n (c n)) atTop
      (fun ω => J t ω - J' t ω) := by
    convert hsub using 2 with n
    funext ω
    exact (itoStepSum_sub _ t n (a n) (b n) ω).symm
  have hae := tendstoInMeasure_ae_unique hsub' hS
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.1 hω

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
    nlinarith
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  linarith

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
    exact abs_le.2 ⟨by simp only [D, leftCoef]; linarith [h1.1, h2.2],
      by simp only [D, leftCoef]; linarith [h1.2, h2.1]⟩
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
      have h3 : η ^ 2 ≤ η := by
        have := mul_le_mul_of_nonneg_left h1 hηpos.le
        linarith only [this]
      have h4 : η * ((t : ℝ) + 1) ≤ ε ^ 2 / 2 := by rwa [le_div_iff₀ (by positivity)] at h2
      have h5 := mul_le_mul_of_nonneg_right h3 ht
      linarith only [h5, h4, hηpos]
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
    linarith
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
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

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
    rw [div_le_iff₀ ht]
    have := mul_le_mul_of_nonneg_right hu.2 h2.le
    linarith only [this]
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
      exact absurd hlo (not_lt.2 (h1'.trans this))
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      exact absurd h1 (not_lt.2 (hhi.trans this))
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
      have hm2 := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [hm2]
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
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hs_ge m))]
      have e1 : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by ring
      have e2 := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [e1, e2, hhi]
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
      have : η ^ 2 ≤ η := by nlinarith
      exact mul_le_mul_of_nonneg_right this ht
    have h4 : η * t.val ≤ ε / (2 * (t.val + 1)) * t.val := mul_le_mul_of_nonneg_right h2 ht
    have h5 : ε / (2 * (t.val + 1)) * t.val < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
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
  linarith

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

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate. -/
theorem exists_hasBrownianItoIntegral {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).1 j H hHm hHc
/-- Any Ito integral of a continuous adapted integrand is the limit in probability of the
truncated left-point sums. -/
theorem clampLeft_tendsto_of_hasBrownianItoIntegral {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => itoStepSum (fun s ω => W s ω j) t n (leftCoef (clampH H n) t n)) atTop (J t) := by
  obtain ⟨J', hJ', hconv⟩ := exists_hasBrownianItoIntegral_clamp hW x₀ j hHm hHc
  exact (hconv t).congr_right (hasBrownianItoIntegral_ae_unique hW x₀ j
    (fun ω => (hHc ω).comp continuous_real_toNNReal) hJ' hJ t)

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

theorem tendstoInMeasure_add_real {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f f' : ι → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure P f l g) (hf' : TendstoInMeasure P f' l g') :
    TendstoInMeasure P (fun i ω => f i ω + f' i ω) l (fun ω => g ω + g' ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf hf' ⊢
  refine tendstoInMeasure_zero_of_abs_le one_pos hf hf' fun i ω => ?_
  rw [one_mul]
  calc |f i ω + f' i ω - (g ω + g' ω)| = |(f i ω - g ω) + (f' i ω - g' ω)| := by
        congr 1; ring
    _ ≤ _ := abs_add_le _ _

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

/-- Locality of the Ito integral: integrands agreeing on the dyadic grid of `[0, s]` on an event
give integrals agreeing a.e. on that event at time `s`. -/
theorem hasBrownianItoIntegral_eq_on {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N → H (dyTime s N i) ω = H' (dyTime s N i) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by
  refine tendstoInMeasure_ae_eq_on
    (clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ s)
    (clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hH'm hH'c hJ' s) fun n ω hω => ?_
  unfold itoStepSum
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  simp only [leftCoef]
  unfold clampH
  rw [hE ω hω n k (Finset.mem_range.1 hk).le]

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
  linarith only [hε, mul_nonneg hε.le ht]

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

theorem abs_clampH_le_abs (H : ℝ≥0 → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (s : ℝ≥0) (ω : Ω) :
    |clampH H R s ω| ≤ |H s ω| := by
  unfold clampH
  rw [abs_le]
  exact ⟨le_max_of_le_right (le_min (neg_abs_le _) (by linarith [abs_nonneg (H s ω)])),
    max_le (by linarith [abs_nonneg (H s ω)]) ((min_le_left _ _).trans (le_abs_self _))⟩

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

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
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

end FlatM_E
-- ===== F =====
section FlatM_F
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

end FlatM_F
-- ===== G =====
section FlatM_G
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


section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
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

end FlatM_H
-- ===== I =====
section FlatM_I
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
  have hm : Measurable (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2) :=
    measurable_pi_lambda _ fun p =>
      (stdBrownian_coord_measurable hW (s + p.1) p.2).sub (stdBrownian_coord_measurable hW s p.2)
  exact hm.le_map

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
  have hsqK : ∀ x : ℝ, |x| ≤ K → x ^ 2 ≤ K ^ 2 := fun x hx =>
    sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
  have i3 : ∀ i j, Integrable (fun ω => A ω (i, j) ^ 2 * ξ j ω ^ 2) P := fun i j =>
    ((hξL j).integrable_sq.const_mul (K ^ 2)).mono' (((aA _).pow 2).mul ((hξL j).1.pow 2))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hsqK _ (hAb ω _)) (sq_nonneg _))
  have i4 : ∀ i j, Integrable (fun ω => B ω (i, j) ^ 2 * ζ j ω ^ 2) P := fun i j =>
    ((hζm j).2.1.integrable_sq.const_mul (K ^ 2)).mono' (((aB _).pow 2).mul ((hζas j).pow 2))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
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

end FlatM_I
-- ===== J =====
section FlatM_J
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

theorem coord_abs_le_diff (A : SDEDiffusion d) (p : Fin d × Fin d) : |A p| ≤ ‖A‖ := by
  have := PiLp.norm_apply_le A p; rwa [Real.norm_eq_abs] at this

theorem integrable_norm_sq_of_coords [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → SDEState d}
    (hf : ∀ i, MemLp (fun ω => f ω i) 2 P) : Integrable (fun ω => ‖f ω‖ ^ 2) P := by
  simp_rw [state_norm_sq]
  exact integrable_finsetSum _ fun i _ => (hf i).integrable_sq

end M10d3

end ItoLib

end FlatM_J
-- ===== K =====
section FlatM_K
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

end FlatM_K
-- ===== L =====
section FlatM_L
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

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
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

end FlatM_CC
-- ===== CD =====
section FlatM_CD
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

end FlatM_CD
-- ===== CE =====
section FlatM_CE
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

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
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

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

end FlatM_CG
-- ===== CH =====
section FlatM_CH
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

end FlatM_CH
-- ===== CI =====
section FlatM_CI
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
      linarith only [h5, sq_nonneg (‖M m ω‖ - ‖M k ω‖), sq_nonneg ‖M m ω‖, sq_nonneg ‖M k ω‖]
    have hpt : ∀ ω, ‖M k ω‖ ^ 2 + 2 * ⟪M k ω, M m ω - M k ω⟫ ≤ ‖M m ω‖ ^ 2 := fun ω => by
      have e : M m ω = M k ω + (M m ω - M k ω) := by abel
      have := norm_add_sq_real (M k ω) (M m ω - M k ω)
      rw [← e] at this
      linarith only [this, sq_nonneg ‖M m ω - M k ω‖]
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

end FlatM_CI
-- ===== CK =====
section FlatM_CK
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

end FlatM_CK
-- ===== CL =====
section FlatM_CL
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

end FlatM_CL
-- ===== M =====
section FlatM_M
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

end FlatM_M
-- ===== N =====
section FlatM_N
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

end FlatM_N
-- ===== O =====
section FlatM_O
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

end FlatM_O
-- ===== P =====
section FlatM_P
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

end FlatM_P
-- ===== CM =====
section FlatM_CM
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

end FlatM_CM
-- ===== CN =====
section FlatM_CN
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

end FlatM_CN
-- ===== QA =====
section FlatM_QA
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

noncomputable def gpt (m l : ℕ) : ℝ≥0 := ((l : ℝ) * (hm m : ℝ)).toNNReal

theorem hm_coe (m : ℕ) : (hm m : ℝ) = 1 / 2 ^ m := by simp [hm]

theorem gpt_coe (m l : ℕ) : (gpt m l : ℝ) = l / 2 ^ m := by
  unfold gpt
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg _) (NNReal.coe_nonneg _)), hm_coe]
  ring

theorem gpt_le_iff (m a b : ℕ) : gpt m a ≤ gpt m b ↔ a ≤ b := by
  rw [← NNReal.coe_le_coe, gpt_coe, gpt_coe, div_le_div_iff_of_pos_right (by positivity)]
  exact Nat.cast_le

theorem gpt_lift {q r : ℕ} (hqr : q ≤ r) (l : ℕ) : gpt q l = gpt r (l * 2 ^ (r - q)) := by
  apply NNReal.coe_injective
  rw [gpt_coe, gpt_coe]
  push_cast
  have h2 : (2 : ℝ) ^ r = 2 ^ q * 2 ^ (r - q) := by
    rw [← pow_add, Nat.add_sub_cancel' hqr]
  rw [h2]
  field_simp

theorem gpt_nat (r N : ℕ) : gpt r (N * 2 ^ r) = (N : ℝ≥0) := by
  apply NNReal.coe_injective
  rw [gpt_coe]; push_cast; field_simp

/-- The step integral of `H` (left points of mesh `2^{-q}` on `[0,q]`), stopped at time `t`. -/
noncomputable def stepM (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) (q : ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range (q * 2 ^ q),
    H (gpt q l) ω * (W (min (gpt q (l + 1)) t) ω j - W (min (gpt q l) t) ω j)

/-- The discrete martingale of a level-`r` coefficient sequence. -/
noncomputable def dsum (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (r : ℕ) (φ : ℕ → Ω → ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, φ i ω * (W (gpt r (i + 1)) ω j - W (gpt r i) ω j)

theorem stepM_continuous {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (j : Fin d) (H : ℝ≥0 → Ω → ℝ) (q : ℕ) (ω : Ω) : Continuous fun t => stepM W j H q t ω := by
  unfold stepM
  have hc : ∀ a : ℝ≥0, Continuous fun t : ℝ≥0 => W (min a t) ω j := fun a =>
    (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp
      ((hWc ω).comp (continuous_const.min continuous_id)))
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((hc _).sub (hc _))

/-- One fine-grid step of `stepM`: on the level-`r` cell `k` the increment is the left
coefficient of the enclosing level-`q` cell times the Brownian increment. -/
theorem stepM_succ (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {q r : ℕ}
    (hqr : q ≤ r) {k : ℕ} (hk : k < q * 2 ^ r) (ω : Ω) :
    stepM W j H q (gpt r (k + 1)) ω - stepM W j H q (gpt r k) ω =
      H (gpt q (k / 2 ^ (r - q))) ω * (W (gpt r (k + 1)) ω j - W (gpt r k) ω j) := by
  set e := 2 ^ (r - q) with he
  have he0 : 0 < e := by positivity
  set l0 := k / e with hl0
  have hlo : l0 * e ≤ k := Nat.div_mul_le_self k e
  have hhi : k < (l0 + 1) * e := by
    rw [hl0, add_mul, one_mul]; exact Nat.lt_div_mul_add he0
  have hl0q : l0 < q * 2 ^ q := by
    rw [hl0, Nat.div_lt_iff_lt_mul he0, mul_assoc, he, ← pow_add, Nat.add_sub_cancel' hqr]
    exact hk
  unfold stepM
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l0]
  · have h1 : min (gpt q (l0 + 1)) (gpt r (k + 1)) = gpt r (k + 1) := by
      rw [gpt_lift hqr]; exact min_eq_right ((gpt_le_iff _ _ _).2 hhi)
    have h2 : min (gpt q (l0 + 1)) (gpt r k) = gpt r k := by
      rw [gpt_lift hqr]; exact min_eq_right ((gpt_le_iff _ _ _).2 hhi.le)
    have h3 : min (gpt q l0) (gpt r (k + 1)) = gpt q l0 := by
      rw [gpt_lift hqr]; exact min_eq_left ((gpt_le_iff _ _ _).2 (hlo.trans (Nat.le_succ k)))
    have h4 : min (gpt q l0) (gpt r k) = gpt q l0 := by
      rw [gpt_lift hqr]; exact min_eq_left ((gpt_le_iff _ _ _).2 hlo)
    rw [h1, h2, h3, h4]; ring
  · intro l _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hA : ∀ t ∈ ({gpt r k, gpt r (k + 1)} : Set ℝ≥0), min (gpt q (l + 1)) t = gpt q (l + 1) ∧
          min (gpt q l) t = gpt q l := by
        intro t ht
        have hkt : gpt r k ≤ t := by
          rcases ht with rfl | rfl
          · exact le_rfl
          · exact (gpt_le_iff _ _ _).2 (Nat.le_succ k)
        have hb : gpt q (l + 1) ≤ gpt r k := by
          rw [gpt_lift hqr]; refine (gpt_le_iff _ _ _).2 (le_trans ?_ hlo)
          exact Nat.mul_le_mul_right _ hlt
        have hb' : gpt q l ≤ gpt q (l + 1) := (gpt_le_iff _ _ _).2 (Nat.le_succ l)
        exact ⟨min_eq_left (hb.trans hkt), min_eq_left ((hb'.trans hb).trans hkt)⟩
      obtain ⟨a1, a2⟩ := hA (gpt r (k + 1)) (by simp)
      obtain ⟨b1, b2⟩ := hA (gpt r k) (by simp)
      rw [a1, a2, b1, b2]; ring
    · have hb : gpt r (k + 1) ≤ gpt q l := by
        rw [gpt_lift hqr]; refine (gpt_le_iff _ _ _).2 (le_trans (Nat.succ_le_of_lt hhi) ?_)
        exact Nat.mul_le_mul_right _ hgt
      have hb' : gpt q l ≤ gpt q (l + 1) := (gpt_le_iff _ _ _).2 (Nat.le_succ l)
      have hk1 : gpt r k ≤ gpt r (k + 1) := (gpt_le_iff _ _ _).2 (Nat.le_succ k)
      rw [min_eq_right (hb.trans hb'), min_eq_right hb, min_eq_right ((hk1.trans hb).trans hb'),
        min_eq_right (hk1.trans hb)]
      ring
  · intro h; exact absurd (Finset.mem_range.2 hl0q) h

theorem stepM_zero (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) (q : ℕ) (ω : Ω) :
    stepM W j H q 0 ω = 0 := by
  unfold stepM
  exact Finset.sum_eq_zero fun l _ => by simp

/-- `stepM` at fine grid points is a discrete martingale sum. -/
theorem stepM_grid (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {q r : ℕ}
    (hqr : q ≤ r) {k : ℕ} (hk : k ≤ q * 2 ^ r) (ω : Ω) :
    stepM W j H q (gpt r k) ω =
      dsum W j r (fun i ω => H (gpt q (i / 2 ^ (r - q))) ω) k ω := by
  induction k with
  | zero =>
    have : gpt r 0 = 0 := by simp [gpt]
    rw [this, stepM_zero]; simp [dsum]
  | succ k ih =>
    have h1 := stepM_succ W j H hqr (k := k) (by omega) ω
    rw [dsum, Finset.sum_range_succ, ← dsum, ← ih (by omega)]
    linarith

theorem dsum_sub (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (r : ℕ) (φ ψ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    dsum W j r φ k ω - dsum W j r ψ k ω = dsum W j r (fun i ω => φ i ω - ψ i ω) k ω := by
  unfold dsum; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem div_mul_le_div_mul' {i a b : ℕ} (hb : 0 < b) (hba : b ∣ a) : i / a * a ≤ i / b * b := by
  obtain ⟨c, rfl⟩ := hba
  have h1 : i / (b * c) * c ≤ i / b := by
    rw [Nat.le_div_iff_mul_le hb]
    calc i / (b * c) * c * b = i / (b * c) * (b * c) := by ring
      _ ≤ i := Nat.div_mul_le_self _ _
  calc i / (b * c) * (b * c) = (i / (b * c) * c) * b := by ring
    _ ≤ i / b * b := Nat.mul_le_mul_right _ h1

/-- Discrete Kolmogorov maximal inequality for a scalar level-`r` martingale sum. -/
theorem dsum_max [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    (r : ℕ) {φ : ℕ → Ω → ℝ}
    (hφ : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) (gpt r i)] (φ i))
    (hφa : ∀ i, Measurable (φ i)) {K : ℝ} (hK : ∀ i ω, |φ i ω| ≤ K) (m : ℕ) {lam : ℝ}
    (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ k ≤ m, lam ≤ |dsum W j r φ k ω|} ≤
      ∑ i ∈ Finset.range m, 2 * d * (hm r : ℝ) * ∫ ω, φ i ω ^ 2 ∂P := by
  let A : ℕ → Ω → SDEDiffusion d := fun i ω => EuclideanSpace.single (j, j) (φ i ω)
  let B : ℕ → Ω → SDEDiffusion d := fun _ _ => 0
  have hAm : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀)
      ((l : ℝ) * (hm r : ℝ)).toNNReal] fun ω => A l ω p := by
    intro l p
    simp only [A, EuclideanSpace.single_apply]
    split_ifs
    · exact hφ l
    · exact measurable_const
  have hBm : ∀ (l : ℕ) p, Measurable[completedBrownianPast P W (fun _ => x₀)
      ((l : ℝ) * (hm r : ℝ)).toNNReal] fun ω => B l ω p := fun _ _ => measurable_const
  have hAa : ∀ (l : ℕ) p, Measurable fun ω => A l ω p := by
    intro l p
    simp only [A, EuclideanSpace.single_apply]
    split_ifs
    · exact hφa l
    · exact measurable_const
  have hBa : ∀ (l : ℕ) p, Measurable fun ω => B l ω p := fun _ _ => measurable_const
  have hAK : ∀ l ω, ‖A l ω‖ ≤ max K 0 := fun l ω => by
    simp only [A, EuclideanSpace.norm_single, Real.norm_eq_abs]
    exact (hK l ω).trans (le_max_left _ _)
  have hBK : ∀ l ω, ‖B l ω‖ ≤ max K 0 := fun l ω => by simp [B]
  have hh : 0 < (hm r : ℝ) := by rw [hm_coe]; positivity
  have key : ∀ k ω, ‖gmart W (hm r) A B k ω‖ = |dsum W j r φ k ω| := by
    intro k ω
    have : gmart W (hm r) A B k ω = EuclideanSpace.single j (dsum W j r φ k ω) := by
      ext i
      simp only [gmart, cellNoise, dsum, A, B, EuclideanSpace.single_apply, WithLp.ofLp_sum,
        Finset.sum_apply, PiLp.toLp_apply]
      have hs : ∀ l : ℕ, ((l : ℝ) * (hm r : ℝ)).toNNReal + hm r = gpt r (l + 1) :=
        fun l => (tnn_succ _ l).symm
      simp only [hs]
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_eq_single i]
        · simp [gpt]
        · intro b _ hb; simp [Prod.ext_iff, hb]
        · simp
      · simp only [hij, if_false]
        refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun b _ => ?_
        simp [Prod.ext_iff, hij]
    rw [this, EuclideanSpace.norm_single, Real.norm_eq_abs]
  have hmax := gmart_max hW x₀ hh hAm hBm hAK hBK hAa hBa m hlam
  have hset : {ω | ∃ k ≤ m, lam ≤ ‖gmart W (hm r) A B k ω‖} =
      {ω | ∃ k ≤ m, lam ≤ |dsum W j r φ k ω|} := by
    ext ω; simp only [Set.mem_setOf_eq, key]
  rw [hset] at hmax
  refine hmax.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp [A, B, EuclideanSpace.norm_single, sq_abs]

/-- Continuous-time maximal inequality for the difference of two step integrals of a bounded
adapted continuous integrand, given an `L²` modulus bound `β` at mesh `2^{-p}`. -/
theorem stepM_sup_max [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C) {N p q : ℕ}
    (hNp : N ≤ p) (hpq : p ≤ q) {β : ℝ}
    (hβ : ∀ s u : ℝ≥0, s ≤ u → u ≤ N → (u : ℝ) - s ≤ 1 / 2 ^ p →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ β) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧
      lam < |stepM W j H q t ω - stepM W j H p t ω|} ≤ 2 * d * N * β := by
  have hβ0 : 0 ≤ β := le_trans (integral_nonneg fun ω => sq_nonneg _)
    (hβ 0 0 le_rfl (by simp) (by simp))
  set D : ℝ≥0 → Ω → ℝ := fun t ω => stepM W j H q t ω - stepM W j H p t ω with hD
  have hDc : ∀ ω, Continuous fun t => D t ω := fun ω =>
    (stepM_continuous hW.2.1 j H q ω).sub (stepM_continuous hW.2.1 j H p ω)
  let A : ℕ → Set Ω := fun r => {ω | ∃ k ≤ N * 2 ^ r, lam ≤ |D (gpt r k) ω|}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun r ω hω => ?_
    obtain ⟨k, hk, hl⟩ := hω
    refine ⟨k * 2 ^ (r + 1 - r), ?_, ?_⟩
    · have h2 : 2 ^ (r + 1 - r) = 2 := by simp
      rw [h2, pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right 2 hk
    · rwa [← gpt_lift (Nat.le_succ r)]
  set Bd : ℝ := 2 * d * N * β / lam ^ 2 with hBd
  have hlev : ∀ r, q ≤ r → P.real (A r) ≤ Bd := by
    intro r hqr
    have hpr : p ≤ r := hpq.trans hqr
    set φ : ℕ → Ω → ℝ := fun i ω => H (gpt q (i / 2 ^ (r - q))) ω - H (gpt p (i / 2 ^ (r - p))) ω
      with hφ
    have hAeq : A r = {ω | ∃ k ≤ N * 2 ^ r, lam ≤ |dsum W j r φ k ω|} := by
      ext ω
      simp only [A, Set.mem_setOf_eq]
      refine exists_congr fun k => and_congr_right fun hk => ?_
      have h1 := stepM_grid W j H (le_refl q |>.trans hqr) (k := k)
        (hk.trans (Nat.mul_le_mul_right _ (hNp.trans hpq))) ω
      have h2 := stepM_grid W j H hpr (k := k) (hk.trans (Nat.mul_le_mul_right _ hNp)) ω
      simp only [hD]
      rw [h1, h2, dsum_sub]
    -- timing facts for the coefficient
    have htime : ∀ i, gpt p (i / 2 ^ (r - p)) ≤ gpt q (i / 2 ^ (r - q)) ∧
        gpt q (i / 2 ^ (r - q)) ≤ gpt r i ∧
        (gpt q (i / 2 ^ (r - q)) : ℝ) - gpt p (i / 2 ^ (r - p)) ≤ 1 / 2 ^ p := by
      intro i
      have hdv : 2 ^ (r - q) ∣ 2 ^ (r - p) := pow_dvd_pow 2 (by omega)
      have hle : i / 2 ^ (r - p) * 2 ^ (r - p) ≤ i / 2 ^ (r - q) * 2 ^ (r - q) :=
        div_mul_le_div_mul' (by positivity) hdv
      refine ⟨?_, ?_, ?_⟩
      · rw [gpt_lift hpr, gpt_lift hqr]; exact (gpt_le_iff _ _ _).2 hle
      · rw [gpt_lift hqr]; exact (gpt_le_iff _ _ _).2 (Nat.div_mul_le_self _ _)
      · rw [gpt_lift hpr, gpt_lift hqr, gpt_coe, gpt_coe]
        have hm1 : ((i / 2 ^ (r - q) * 2 ^ (r - q) : ℕ) : ℝ) ≤ i := by
          exact_mod_cast Nat.div_mul_le_self _ _
        have hm2 : (i : ℝ) < (i / 2 ^ (r - p) * 2 ^ (r - p) : ℕ) + 2 ^ (r - p) := by
          have h3 := Nat.div_add_mod' i (2 ^ (r - p))
          have h4 := Nat.mod_lt i (show 0 < 2 ^ (r - p) by positivity)
          have : i < i / 2 ^ (r - p) * 2 ^ (r - p) + 2 ^ (r - p) := by omega
          exact_mod_cast this
        have h2r : (2 : ℝ) ^ r = 2 ^ p * 2 ^ (r - p) := by
          rw [← pow_add, Nat.add_sub_cancel' hpr]
        rw [div_sub_div_same, div_le_div_iff₀ (by positivity) (by positivity), h2r]
        have : ((i / 2 ^ (r - q) * 2 ^ (r - q) : ℕ) : ℝ) - (i / 2 ^ (r - p) * 2 ^ (r - p) : ℕ)
            ≤ 2 ^ (r - p) := by push_cast at hm1 hm2 ⊢; linarith only [hm1, hm2]
        have h5 := mul_le_mul_of_nonneg_right this (pow_pos (show (0 : ℝ) < 2 by norm_num) p).le
        linarith only [h5]
    have hφm : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) (gpt r i)] (φ i) := by
      intro i
      obtain ⟨h1, h2, -⟩ := htime i
      exact ((hHm _).mono (completedBrownianPast_mono P W _ h2) le_rfl).sub
        ((hHm _).mono (completedBrownianPast_mono P W _ (h1.trans h2)) le_rfl)
    have hφa : ∀ i, Measurable (φ i) := fun i => (hHa _).sub (hHa _)
    have hφK : ∀ i ω, |φ i ω| ≤ 2 * C := fun i ω => by
      calc |φ i ω| ≤ |H (gpt q (i / 2 ^ (r - q))) ω| + |H (gpt p (i / 2 ^ (r - p))) ω| :=
            abs_sub _ _
        _ ≤ 2 * C := by linarith only [hC (gpt q (i / 2 ^ (r - q))) ω, hC (gpt p (i / 2 ^ (r - p))) ω]
    have hmax := dsum_max hW x₀ j r hφm hφa hφK (N * 2 ^ r) hlam
    rw [← hAeq] at hmax
    have hsum : ∑ i ∈ Finset.range (N * 2 ^ r), 2 * d * (hm r : ℝ) * ∫ ω, φ i ω ^ 2 ∂P ≤
        2 * d * N * β := by
      calc ∑ i ∈ Finset.range (N * 2 ^ r), 2 * d * (hm r : ℝ) * ∫ ω, φ i ω ^ 2 ∂P
          ≤ ∑ i ∈ Finset.range (N * 2 ^ r), 2 * d * (hm r : ℝ) * β := by
            refine Finset.sum_le_sum fun i hi => ?_
            refine mul_le_mul_of_nonneg_left ?_ (by rw [hm_coe]; positivity)
            obtain ⟨h1, h2, h3⟩ := htime i
            refine hβ _ _ h1 ?_ h3
            refine h2.trans ?_
            rw [← gpt_nat r N]
            exact (gpt_le_iff _ _ _).2 (Finset.mem_range.1 hi).le
        _ = 2 * d * N * β := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hm_coe]
            push_cast
            have e : (2 : ℝ) ^ r * (1 / 2 ^ r) = 1 := mul_one_div_cancel (pow_ne_zero _ two_ne_zero)
            linear_combination (2 * (d : ℝ) * N * β) * e
    have := hmax.trans hsum
    rw [hBd, le_div_iff₀ (by positivity)]
    linarith only [this]
  have hall : ∀ r, P.real (A r) ≤ Bd := fun r =>
    (measureReal_mono (hAmono (le_max_left r q))).trans (hlev _ (le_max_right r q))
  -- the continuous-time event is inside the union of the grid events
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ⊆ ⋃ r, A r := by
    rintro ω ⟨t, htN, hlt⟩
    let kr : ℕ → ℕ := fun r => ⌊(t : ℝ) * 2 ^ r⌋₊
    have hconv : Tendsto (fun r => gpt r (kr r)) atTop (𝓝 t) := by
      rw [← NNReal.tendsto_coe]
      have hup : ∀ r, (gpt r (kr r) : ℝ) ≤ t := fun r => by
        rw [gpt_coe, div_le_iff₀ (by positivity)]
        exact Nat.floor_le (by positivity)
      have hlo : ∀ r, (t : ℝ) - 1 / 2 ^ r ≤ gpt r (kr r) := fun r => by
        rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div,
          inv_mul_cancel₀ (by positivity)]
        linarith only [Nat.lt_floor_add_one ((t : ℝ) * 2 ^ r)]
      have hl : Tendsto (fun r : ℕ => (t : ℝ) - 1 / 2 ^ r) atTop (𝓝 t) := by
        have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / 2 ^ r) atTop (𝓝 0) := by
          simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        simpa using h0.const_sub (t : ℝ)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup
    have hev := ((continuous_abs.comp (hDc ω)).tendsto t).comp hconv
    obtain ⟨r, hr⟩ := (hev.eventually (lt_mem_nhds hlt)).exists
    refine Set.mem_iUnion.2 ⟨r, kr r, ?_, hr.le⟩
    have : (t : ℝ) * 2 ^ r ≤ ((N * 2 ^ r : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htN) (by positivity)
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  have hU : P (⋃ r, A r) ≤ ENNReal.ofReal Bd := by
    rw [hAmono.measure_iUnion]
    refine iSup_le fun r => ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hall r)
  have hS : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ≤ Bd := by
    have h1 := (measure_mono hsub).trans hU
    have hB0 : 0 ≤ Bd := by rw [hBd]; positivity
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  have := mul_le_mul_of_nonneg_left hS (sq_nonneg lam)
  rw [hBd, mul_div_cancel₀ _ (by positivity)] at this
  exact this

end QA
end ItoLib

end FlatM_QA
-- ===== QB =====
section FlatM_QB
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

theorem osc_L2 [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω)
    {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C) (N : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s u : ℝ≥0, s ≤ N → u ≤ N → |(u : ℝ) - s| < δ →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P < ε := by
  let F : ℝ≥0 × ℝ≥0 → ℝ := fun p => ∫ ω, (H p.2 ω - H p.1 ω) ^ 2 ∂P
  have hF : Continuous F := by
    refine continuous_of_dominated (bound := fun _ => (2 * C) ^ 2)
      (fun p => (((hHa p.2).sub (hHa p.1)).pow_const 2).aestronglyMeasurable)
      (fun p => ae_of_all _ fun ω => ?_) (integrable_const _) (ae_of_all _ fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |H p.2 ω - H p.1 ω| ≤ |H p.2 ω| + |H p.1 ω| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC p.2 ω, hC p.1 ω]
    · exact (((hHc ω).comp continuous_snd).sub ((hHc ω).comp continuous_fst)).pow 2
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) N ×ˢ Set.Icc (0 : ℝ≥0) N) :=
    isCompact_Icc.prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  refine ⟨δ, hδ, fun s u hs hu hsu => ?_⟩
  have hmem1 : (s, u) ∈ Set.Icc (0 : ℝ≥0) N ×ˢ Set.Icc (0 : ℝ≥0) N :=
    ⟨⟨by positivity, hs⟩, ⟨by positivity, hu⟩⟩
  have hmem2 : (s, s) ∈ Set.Icc (0 : ℝ≥0) N ×ˢ Set.Icc (0 : ℝ≥0) N :=
    ⟨⟨by positivity, hs⟩, ⟨by positivity, hs⟩⟩
  have hd : dist (s, u) (s, s) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, NNReal.dist_eq]; exact hsu
  have := hδ' _ hmem1 _ hmem2 hd
  have h0 : F (s, s) = 0 := by simp [F]
  rw [h0, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

theorem sum_Ico_telescope (w : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (w (i + 1) - w i) = w b - w a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring

/-- Index of the first level-`r` point of the `t`-grid at or after `x`, capped at `2^r`. -/
noncomputable def idxT (t : ℝ≥0) (r : ℕ) (x : ℝ≥0) : ℕ := min (2 ^ r) ⌈(x : ℝ) * 2 ^ r / t⌉₊

theorem idxT_le (t : ℝ≥0) (r : ℕ) (x : ℝ≥0) : idxT t r x ≤ 2 ^ r := min_le_left _ _

theorem idxT_mono (t : ℝ≥0) (r : ℕ) {x y : ℝ≥0} (hxy : x ≤ y) : idxT t r x ≤ idxT t r y := by
  unfold idxT
  refine min_le_min le_rfl (Nat.ceil_mono ?_)
  have : (x : ℝ) ≤ y := hxy
  have ht : (0 : ℝ) ≤ t := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)) ht

/-- For `i < 2^r`: `x ≤ i t / 2^r ↔ idxT x ≤ i`. -/
theorem le_grid_iff {t : ℝ≥0} (ht : 0 < (t : ℝ)) (r : ℕ) (x : ℝ≥0) {i : ℕ} (hi : i < 2 ^ r) :
    (x : ℝ) ≤ i * t / 2 ^ r ↔ idxT t r x ≤ i := by
  unfold idxT
  rw [min_le_iff, Nat.ceil_le, div_le_iff₀ ht]
  constructor
  · intro h; right
    rw [le_div_iff₀ (by positivity)] at h; linarith
  · rintro (h | h)
    · omega
    · rw [le_div_iff₀ (by positivity)]; linarith

theorem floor_eq_iff_gpt {v : ℝ} (hv : 0 ≤ v) (q l : ℕ) :
    ⌊v * 2 ^ q⌋₊ = l ↔ (gpt q l : ℝ) ≤ v ∧ v < gpt q (l + 1) := by
  rw [Nat.floor_eq_iff (by positivity), gpt_coe, gpt_coe, div_le_iff₀ (by positivity),
    lt_div_iff₀ (by positivity)]
  push_cast; exact Iff.rfl

/-- Regrouping a `t`-grid Riemann sum with level-`q` left coefficients by level-`q` cells. -/
theorem regroup (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) {q : ℕ} (htq : (t : ℝ) ≤ q) (r : ℕ) (ω : Ω) :
    itoStepSum (fun s ω => W s ω j) t r
      (fun i ω => H (gpt q ⌊(i : ℝ) * t / 2 ^ r * 2 ^ q⌋₊) ω) ω =
    ∑ l ∈ Finset.range (q * 2 ^ q), H (gpt q l) ω *
      (W ((idxT t r (gpt q (l + 1)) : ℝ≥0) * t / (2 : ℝ≥0) ^ r) ω j -
        W ((idxT t r (gpt q l) : ℝ≥0) * t / (2 : ℝ≥0) ^ r) ω j) := by
  set w : ℕ → ℝ := fun i => W ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ r) ω j with hw
  have hstep : ∀ i : ℕ, W (((i : ℝ≥0) + 1) * t / (2 : ℝ≥0) ^ r) ω j = w (i + 1) := by
    intro i; simp only [hw]; push_cast; rfl
  set fl : ℕ → ℕ := fun i => ⌊(i : ℝ) * t / 2 ^ r * 2 ^ q⌋₊ with hfl
  have hvnn : ∀ i : ℕ, (0 : ℝ) ≤ (i : ℝ) * t / 2 ^ r := fun i => by positivity
  have hflt : ∀ i ∈ Finset.range (2 ^ r), fl i < q * 2 ^ q := by
    intro i hi
    have hi' : (i : ℝ) < 2 ^ r := by exact_mod_cast Finset.mem_range.1 hi
    have hv : (i : ℝ) * t / 2 ^ r < t := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    rw [hfl, Nat.floor_lt (by have := hvnn i; positivity)]
    push_cast
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) q]
  unfold itoStepSum
  simp only [hstep]
  have hc : ∀ i ∈ Finset.range (2 ^ r), H (gpt q (fl i)) ω =
      ∑ l ∈ Finset.range (q * 2 ^ q), if fl i = l then H (gpt q l) ω else 0 := by
    intro i hi
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (hflt i hi))]
  rw [Finset.sum_congr rfl fun i hi => by rw [hc i hi]]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  have hfil : (Finset.range (2 ^ r)).filter (fun i => fl i = l) =
      Finset.Ico (idxT t r (gpt q l)) (idxT t r (gpt q (l + 1))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hi, hfi⟩
      rw [hfl, floor_eq_iff_gpt (hvnn i)] at hfi
      refine ⟨(le_grid_iff ht r _ hi).1 hfi.1, ?_⟩
      by_contra hcon
      exact absurd ((le_grid_iff ht r _ hi).2 (not_lt.1 hcon)) (not_le.2 hfi.2)
    · rintro ⟨h1, h2⟩
      have hi : i < 2 ^ r := lt_of_lt_of_le h2 (idxT_le _ _ _)
      refine ⟨hi, ?_⟩
      rw [hfl, floor_eq_iff_gpt (hvnn i)]
      refine ⟨(le_grid_iff ht r _ hi).2 h1, ?_⟩
      by_contra hcon
      exact absurd ((le_grid_iff ht r _ hi).1 (not_lt.1 hcon)) (not_le.2 h2)
  rw [hfil, sum_Ico_telescope w (idxT_mono t r ((gpt_le_iff _ _ _).2 (Nat.le_succ l)))]

theorem idxT_tendsto {t : ℝ≥0} (ht : 0 < (t : ℝ)) (x : ℝ≥0) :
    Tendsto (fun r : ℕ => (idxT t r x : ℝ≥0) * t / (2 : ℝ≥0) ^ r) atTop (𝓝 (min x t)) := by
  rw [← NNReal.tendsto_coe]
  have hlo : ∀ r : ℕ, ((min x t : ℝ≥0) : ℝ) ≤ (((idxT t r x : ℝ≥0) * t / (2 : ℝ≥0) ^ r : ℝ≥0) : ℝ) := by
    intro r
    push_cast
    rw [le_div_iff₀ (by positivity)]
    unfold idxT
    rcases le_total (2 ^ r) ⌈(x : ℝ) * 2 ^ r / t⌉₊ with h | h
    · rw [min_eq_left h]; push_cast
      have : min (x : ℝ) t ≤ t := min_le_right _ _
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
    · rw [min_eq_right h]
      have h1 := Nat.le_ceil ((x : ℝ) * 2 ^ r / t)
      rw [div_le_iff₀ ht] at h1
      have : min (x : ℝ) t ≤ x := min_le_left _ _
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
  have hhi : ∀ r : ℕ, (((idxT t r x : ℝ≥0) * t / (2 : ℝ≥0) ^ r : ℝ≥0) : ℝ) ≤
      ((min x t : ℝ≥0) : ℝ) + t / 2 ^ r := by
    intro r
    push_cast
    have hA : (idxT t r x : ℝ) * t / 2 ^ r ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      have : (idxT t r x : ℝ) ≤ 2 ^ r := by exact_mod_cast idxT_le t r x
      nlinarith
    have hB : (idxT t r x : ℝ) * t / 2 ^ r ≤ x + t / 2 ^ r := by
      have : (idxT t r x : ℝ) < (x : ℝ) * 2 ^ r / t + 1 := by
        unfold idxT
        calc ((min (2 ^ r) ⌈(x : ℝ) * 2 ^ r / t⌉₊ : ℕ) : ℝ) ≤ (⌈(x : ℝ) * 2 ^ r / t⌉₊ : ℝ) := by
              exact_mod_cast min_le_right _ _
          _ < _ := Nat.ceil_lt_add_one (by positivity)
      have h' : (idxT t r x : ℝ) * t < x * 2 ^ r + t := by
        have := mul_lt_mul_of_pos_right this ht
        rwa [add_mul, div_mul_cancel₀ _ ht.ne', one_mul] at this
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      linarith
    rcases le_total x t with hxt | hxt
    · rw [min_eq_left (show (x : ℝ) ≤ t by exact_mod_cast hxt)]; exact hB
    · rw [min_eq_right (show (t : ℝ) ≤ x by exact_mod_cast hxt)]; linarith [div_nonneg ht.le (show (0:ℝ) ≤ 2 ^ r by positivity)]
  have hl : Tendsto (fun r : ℕ => ((min x t : ℝ≥0) : ℝ) + t / 2 ^ r) atTop
      (𝓝 ((min x t : ℝ≥0) : ℝ)) := by
    have h0 : Tendsto (fun r : ℕ => (t : ℝ) / 2 ^ r) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (t : ℝ)
      simpa [div_eq_mul_inv, one_div_pow] using this
    simpa using h0.const_add ((min x t : ℝ≥0) : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl hlo hhi

/-- Grid comparison, pathwise part: the `t`-grid sums with level-`q` left coefficients converge
to `stepM q t` as the `t`-grid is refined. -/
theorem regroup_tendsto {W : ℝ≥0 → Ω → SDEState d} (hWc : ∀ ω, Continuous fun s => W s ω)
    (j : Fin d) (H : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : 0 < (t : ℝ)) {q : ℕ} (htq : (t : ℝ) ≤ q)
    (ω : Ω) :
    Tendsto (fun r => itoStepSum (fun s ω => W s ω j) t r
      (fun i ω => H (gpt q ⌊(i : ℝ) * t / 2 ^ r * 2 ^ q⌋₊) ω) ω) atTop
      (𝓝 (stepM W j H q t ω)) := by
  simp only [regroup W j H ht htq]
  unfold stepM
  refine tendsto_finset_sum _ fun l _ => tendsto_const_nhds.mul ?_
  have hWj : Continuous fun s => W s ω j :=
    (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp (hWc ω))
  exact ((hWj.tendsto _).comp (idxT_tendsto ht _)).sub ((hWj.tendsto _).comp (idxT_tendsto ht _))

end QB
end ItoLib

end FlatM_QB
-- ===== QC =====
section FlatM_QC
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

theorem stepM_measurable (hW : IsStandardBrownian P W) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHa : ∀ s, Measurable (H s)) (q : ℕ) (t : ℝ≥0) : Measurable (stepM W j H q t) := by
  unfold stepM
  exact Finset.measurable_sum _ fun l _ => (hHa _).mul
    ((stdBrownian_coord_measurable hW _ j).sub (stdBrownian_coord_measurable hW _ j))

theorem itoStepSum_measurable' (hW : IsStandardBrownian P W) (j : Fin d) (t : ℝ≥0) (n : ℕ)
    {a : ℕ → Ω → ℝ} (ha : ∀ k, Measurable (a k)) :
    Measurable (itoStepSum (fun s ω => W s ω j) t n a) := by
  unfold itoStepSum
  exact Finset.measurable_sum _ fun l _ => (ha _).mul
    ((stdBrownian_coord_measurable hW _ j).sub (stdBrownian_coord_measurable hW _ j))

/-- `L²` grid comparison: `stepM q t` versus the `t`-grid left sum of level `q`. -/
theorem stepM_S_lint (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C) {t : ℝ≥0}
    (ht : 0 < (t : ℝ)) {q : ℕ} (htq : (t : ℝ) ≤ q) (hCq : C ≤ q) {β : ℝ}
    (hβ : ∀ s u : ℝ≥0, s ≤ t → u ≤ t → |(u : ℝ) - s| ≤ (1 + t) / 2 ^ q →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ β) :
    ∫⁻ ω, ENNReal.ofReal ((stepM W j H q t ω -
      itoStepSum (fun s ω => W s ω j) t q (leftCoef (clampH H q) t q) ω) ^ 2) ∂P ≤
      ENNReal.ofReal (t * β) := by
  set S : Ω → ℝ := itoStepSum (fun s ω => W s ω j) t q (leftCoef (clampH H q) t q) with hS
  -- level-(q+m) coefficients
  let c : ℕ → ℕ → Ω → ℝ := fun m i ω => H (gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊) ω
  let a : ℕ → ℕ → Ω → ℝ := fun m i ω => leftCoef (clampH H q) t q (i / 2 ^ m) ω
  let R : ℕ → Ω → ℝ := fun m => itoStepSum (fun s ω => W s ω j) t (q + m) (c m)
  have hlim : ∀ ω, Tendsto (fun m => R m ω) atTop (𝓝 (stepM W j H q t ω)) := by
    intro ω
    have h1 := regroup_tendsto hW.2.1 j H ht htq ω
    have h2 : Tendsto (fun m : ℕ => q + m) atTop atTop := by
      simpa [add_comm] using tendsto_add_atTop_nat q
    exact h1.comp h2
  have hSref : ∀ m ω, S ω = itoStepSum (fun s ω => W s ω j) t (q + m) (a m) ω := fun m ω =>
    itoStepSum_refine _ t q m _ ω
  -- times of the coefficients
  have hcpt : ∀ m i : ℕ, gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊ ≤
      (i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) := by
    intro m i
    rw [← NNReal.coe_le_coe, gpt_coe, div_le_iff₀ (by positivity)]
    push_cast
    exact Nat.floor_le (by positivity)
  have hcpt2 : ∀ m i : ℕ, ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ) - 1 / 2 ^ q ≤
      gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊ := by
    intro m i
    rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div, inv_mul_cancel₀ (by positivity)]
    push_cast
    linarith [Nat.lt_floor_add_one ((i : ℝ) * t / 2 ^ (q + m) * 2 ^ q)]
  have hdiff : ∀ m ω, R m ω - S ω =
      itoStepSum (fun s ω => W s ω j) t (q + m) (fun i ω => c m i ω - a m i ω) ω := by
    intro m ω; rw [hSref m ω]; exact itoStepSum_sub _ _ _ _ _ ω
  have hem : ∀ m, ∀ i : ℕ, i < 2 ^ (q + m) → Measurable[completedBrownianPast P W (fun _ => x₀)
      ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m))] (fun ω => c m i ω - a m i ω) := by
    intro m i _
    refine ((hHm _).mono (completedBrownianPast_mono P W _ (hcpt m i)) le_rfl).sub ?_
    exact (clampH_measurable (hHm _) _).mono
      (completedBrownianPast_mono P W _ (dyTime_coarse t q m i).1) le_rfl
  have heK : ∀ m, ∀ i : ℕ, i < 2 ^ (q + m) → ∀ ω, |c m i ω - a m i ω| ≤ 2 * C := by
    intro m i _ ω
    have h1 := hC (gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊) ω
    have h2 : |a m i ω| ≤ C :=
      (abs_clampH_le_abs H (Nat.cast_nonneg q) _ ω).trans (hC _ ω)
    calc |c m i ω - a m i ω| ≤ |c m i ω| + |a m i ω| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hbnd : ∀ m, ∫ ω, (R m ω - S ω) ^ 2 ∂P ≤ t * β := by
    intro m
    simp_rw [hdiff m]
    rw [itoStepSum_isometry hW x₀ t (q + m) j _ (hem m) (2 * C) (heK m)]
    have hterm : ∀ i ∈ Finset.range (2 ^ (q + m)), ∫ ω, (c m i ω - a m i ω) ^ 2 ∂P ≤ β := by
      intro i hi
      set u := gpt q ⌊(i : ℝ) * t / 2 ^ (q + m) * 2 ^ q⌋₊ with hu
      set s := dyTime t q (i / 2 ^ m) with hs
      have hv : ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) ≤ t := by
        have := dyTime_le t (N := q + m) (j := i) (Finset.mem_range.1 hi).le
        exact this
      have hsv := (dyTime_coarse t q m i)
      have hus : |(u : ℝ) - s| ≤ (1 + t) / 2 ^ q := by
        have e1 : (u : ℝ) ≤ ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) := hcpt m i
        have e2 := hcpt2 m i
        have e3 : (s : ℝ) ≤ ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) :=
          NNReal.coe_le_coe.2 hsv.1
        have e4 : ((i : ℝ≥0) * t / (2 : ℝ≥0) ^ (q + m) : ℝ≥0) - (s : ℝ) ≤ t / 2 ^ q := hsv.2
        push_cast at e1 e2 e3 e4
        rw [abs_le, add_div]
        have h0 : (0 : ℝ) ≤ t / 2 ^ q := by positivity
        have h0' : (0 : ℝ) ≤ 1 / 2 ^ q := by positivity
        constructor <;> linarith
      have hcl : ∀ ω, a m i ω = H s ω := fun ω => by
        simp only [a, leftCoef]
        exact clampH_eq_of_abs_le H ((hC _ ω).trans hCq)
      have := hβ s u (dyTime_le t (Nat.div_le_of_le_mul (by
          have := (Finset.mem_range.1 hi).le; rw [pow_add] at this; linarith))) ((hcpt m i).trans hv) hus
      simpa [c, hcl] using this
    calc ∑ i ∈ Finset.range (2 ^ (q + m)), (∫ ω, (c m i ω - a m i ω) ^ 2 ∂P) *
          (((t / (2 : ℝ≥0) ^ (q + m)) : ℝ≥0) : ℝ)
        ≤ ∑ i ∈ Finset.range (2 ^ (q + m)), β * (((t / (2 : ℝ≥0) ^ (q + m)) : ℝ≥0) : ℝ) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hterm i hi) (by positivity)
      _ = t * β := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
  -- Fatou
  have hRm : ∀ m, Measurable (R m) := fun m =>
    itoStepSum_measurable' hW j t _ fun i => hHa _
  have hSm : Measurable S := itoStepSum_measurable' hW j t q fun i => clampH_measurable (hHa _) _
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop)
    (f := fun m ω => ENNReal.ofReal ((R m ω - S ω) ^ 2))
    (fun m => (ENNReal.measurable_ofReal.comp (((hRm m).sub hSm).pow_const 2)).aemeasurable)
  have hpt : ∀ ω, liminf (fun m => ENNReal.ofReal ((R m ω - S ω) ^ 2)) atTop =
      ENNReal.ofReal ((stepM W j H q t ω - S ω) ^ 2) := by
    intro ω
    have : Tendsto (fun m => ENNReal.ofReal ((R m ω - S ω) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((stepM W j H q t ω - S ω) ^ 2))) :=
      ENNReal.tendsto_ofReal (((hlim ω).sub tendsto_const_nhds).pow 2)
    exact this.liminf_eq
  simp only [hpt] at hfat
  refine hfat.trans (liminf_le_of_frequently_le' (Eventually.frequently
    (Eventually.of_forall fun m => ?_)))
  have hint : Integrable (fun ω => (R m ω - S ω) ^ 2) P := by
    have := (itoStepSum_memLp hW t (q + m) j (fun i ω => c m i ω - a m i ω)
      (fun i _ => ((hHa _).sub (clampH_measurable (hHa _) _)).aestronglyMeasurable)
      (2 * C) (heK m)).integrable_sq
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [hdiff m ω]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hbnd m)

/-- For a bounded continuous adapted integrand, the horizon-free step integrals converge in
probability to the Ito integral at every fixed time. -/
theorem stepM_tendsto (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    TendstoInMeasure P (fun q => stepM W j H q t) atTop (J t) := by
  have hS := clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ t
  set S : ℕ → Ω → ℝ := fun q =>
    itoStepSum (fun s ω => W s ω j) t q (leftCoef (clampH H q) t q) with hSdef
  rcases (NNReal.coe_nonneg t).eq_or_lt with h0 | hpos
  · have ht0 : t = 0 := NNReal.coe_eq_zero.1 h0.symm
    subst ht0
    refine hS.congr_left (fun q => ae_of_all _ fun ω => ?_)
    rw [stepM_zero]; simp [hSdef, itoStepSum]
  have hX : TendstoInMeasure P (fun q ω => stepM W j H q t ω - S q ω) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    rcases eq_or_ne e ⊤ with rfl | hetop
    · exact Eventually.of_forall fun _ => le_top
    set η := e.toReal with hηdef
    have hη : 0 < η := ENNReal.toReal_pos he.ne' hetop
    set β := η * ε ^ 2 / (t + 1) with hβdef
    have hβ : 0 < β := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := osc_L2 (P := P) hHa hHc hC t hβ
    have ev1 : ∀ᶠ q : ℕ in atTop, ((1 : ℝ) + t) / 2 ^ q < δ := by
      have h0 : Tendsto (fun q : ℕ => ((1 : ℝ) + t) / 2 ^ q) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((1 : ℝ) + t)
        simpa [div_eq_mul_inv, one_div_pow] using this
      exact h0.eventually (gt_mem_nhds hδ)
    have ev2 : ∀ᶠ q : ℕ in atTop, (t : ℝ) ≤ q ∧ C ≤ q := by
      obtain ⟨n, hn⟩ := exists_nat_ge (max (t : ℝ) C)
      filter_upwards [eventually_ge_atTop n] with q hq
      have : (n : ℝ) ≤ q := by exact_mod_cast hq
      exact ⟨by linarith [le_max_left (t : ℝ) C], by linarith [le_max_right (t : ℝ) C]⟩
    filter_upwards [ev1, ev2] with q hq1 hq2
    obtain ⟨htq, hCq⟩ := hq2
    have hb := stepM_S_lint hW x₀ j hHm hHa hC hpos htq hCq (β := β)
      (fun s u hs hu hsu => (hδ' s u hs hu (lt_of_le_of_lt hsu hq1)).le)
    have hSm : Measurable (S q) := itoStepSum_measurable' hW j t q fun i => clampH_measurable (hHa _) _
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal ((stepM W j H q t ω - S q ω) ^ 2)) P :=
      (ENNReal.measurable_ofReal.comp
        (((stepM_measurable hW j hHa q t).sub hSm).pow_const 2)).aemeasurable
    refine le_trans (measure_mono (t := {ω | ENNReal.ofReal (ε ^ 2) ≤
      ENNReal.ofReal ((stepM W j H q t ω - S q ω) ^ 2)}) ?_) ?_
    · intro ω hω
      simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω ⊢
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow_le_pow_left₀ hε.le hω 2
      rwa [sq_abs] at this
    · refine (meas_ge_le_lintegral_div hmeas (ENNReal.ofReal_pos.2 (by positivity)).ne'
        ENNReal.ofReal_ne_top).trans ?_
      calc (∫⁻ ω, ENNReal.ofReal ((stepM W j H q t ω - S q ω) ^ 2) ∂P) / ENNReal.ofReal (ε ^ 2)
          ≤ ENNReal.ofReal (t * β) / ENNReal.ofReal (ε ^ 2) := ENNReal.div_le_div_right hb _
        _ = ENNReal.ofReal (t * β / ε ^ 2) := (ENNReal.ofReal_div_of_pos (by positivity)).symm
        _ ≤ ENNReal.ofReal η := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_le_iff₀ (by positivity), hβdef]
            have ht1 : (0 : ℝ) < t + 1 := by positivity
            rw [mul_div_assoc', div_le_iff₀ ht1]
            linarith only [mul_pos hη (pow_pos hε 2)]
        _ = e := ENNReal.ofReal_toReal hetop
  rw [tendstoInMeasure_real_iff_sub]
  have h2 := tendstoInMeasure_real_iff_sub.1 hS
  have h3 := tendstoInMeasure_add_real hX h2
  have h4 : (fun _ : Ω => (0 : ℝ) + 0) = fun _ => 0 := by simp
  rw [h4] at h3
  refine TendstoInMeasure.congr_left (fun q => ae_of_all _ fun ω => ?_) h3
  simp only [hSdef]
  ring

end QC
end ItoLib

end FlatM_QC
-- ===== QD =====
section FlatM_QD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

theorem geom_cauchy_limit {F : ℕ → ℝ≥0 → ℝ} (hF : ∀ k, Continuous (F k)) {K : ℕ}
    (hK : ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ k → |F (k + 1) t - F k t| ≤ (1 / 2 : ℝ) ^ k) :
    (∀ t, CauchySeq fun k => F k t) ∧
    (∀ (t : ℝ≥0) (m : ℕ), K ≤ m → t ≤ m →
      |F m t - limUnder atTop (fun k => F k t)| ≤ 2 * (1 / 2 : ℝ) ^ m) ∧
    Continuous (fun t => limUnder atTop fun k => F k t) := by
  have hstep : ∀ (t : ℝ≥0) (m : ℕ), K ≤ m → t ≤ m → ∀ n : ℕ,
      dist (F (n + m) t) (F (n + 1 + m) t) ≤ 2 * (1 / 2 : ℝ) ^ m / 2 / 2 ^ n := by
    intro t m hKm htm n
    rw [dist_comm, Real.dist_eq, show n + 1 + m = n + m + 1 by omega]
    have h1 := hK (n + m) (by omega) t (htm.trans (by exact_mod_cast Nat.le_add_left m n))
    have h2 : (1 / 2 : ℝ) ^ (n + m) = 2 * (1 / 2 : ℝ) ^ m / 2 / 2 ^ n := by
      rw [pow_add, div_pow, one_pow]; field_simp
    linarith
  have hcau : ∀ t, CauchySeq fun k => F k t := by
    intro t
    set m := max K ⌈t⌉₊
    have htm : t ≤ (m : ℝ≥0) := (Nat.le_ceil t).trans (by exact_mod_cast le_max_right K ⌈t⌉₊)
    exact (cauchySeq_shift m).1 (cauchySeq_of_le_geometric_two (C := 2 * (1 / 2 : ℝ) ^ m)
      (hstep t m (le_max_left _ _) htm))
  have hbd : ∀ (t : ℝ≥0) (m : ℕ), K ≤ m → t ≤ m →
      |F m t - limUnder atTop (fun k => F k t)| ≤ 2 * (1 / 2 : ℝ) ^ m := by
    intro t m hKm htm
    have hlim : Tendsto (fun n => F (n + m) t) atTop (𝓝 (limUnder atTop fun k => F k t)) :=
      (hcau t).tendsto_limUnder.comp (tendsto_add_atTop_nat m)
    have := dist_le_of_le_geometric_two_of_tendsto (C := 2 * (1 / 2 : ℝ) ^ m)
      (hstep t m hKm htm) hlim 0
    simpa [Real.dist_eq] using this
  refine ⟨hcau, hbd, ?_⟩
  refine continuous_iff_continuousAt.2 fun t0 => ?_
  refine continuousAt_of_locally_uniform_approx_of_continuousAt fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  set m := max (max K (⌈t0⌉₊ + 1)) n0
  refine ⟨{t | t < ((⌈t0⌉₊ + 1 : ℕ) : ℝ≥0)}, ?_, F m, (hF m).continuousAt, fun y hy => ?_⟩
  · refine (isOpen_lt continuous_id continuous_const).mem_nhds ?_
    show t0 < ((⌈t0⌉₊ + 1 : ℕ) : ℝ≥0)
    exact (Nat.le_ceil t0).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
  · apply hεu
    have hym : y ≤ (m : ℝ≥0) := (le_of_lt hy).trans (by
      exact_mod_cast (le_max_right K (⌈t0⌉₊ + 1)).trans (le_max_left _ n0))
    have h1 := hbd y m ((le_max_left _ _).trans (le_max_left _ _)) hym
    have h2 : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ n0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    rw [dist_comm, Real.dist_eq]
    linarith

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

theorem stepM_adapted (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) (q : ℕ)
    (t : ℝ≥0) : Measurable[completedBrownianPast P W (fun _ => x₀) t] (stepM W j H q t) := by
  unfold stepM
  refine Finset.measurable_sum _ fun l _ => ?_
  by_cases h : gpt q l ≤ t
  · exact ((hHm _).mono (completedBrownianPast_mono P W _ h) le_rfl).mul
      ((coord_measurable_completedPast P W _ (min_le_right _ _) j).sub
        (coord_measurable_completedPast P W _ (min_le_right _ _) j))
  · push_neg at h
    have h1 : min (gpt q l) t = t := min_eq_right h.le
    have h2 : min (gpt q (l + 1)) t = t :=
      min_eq_right (h.le.trans ((gpt_le_iff q l (l + 1)).2 (Nat.le_succ l)))
    simp only [h1, h2, sub_self, mul_zero]
    exact measurable_const

/-- Fast subsequence of dyadic levels: the sup over `[0,k]` of successive differences
exceeds `2^{-k}` with probability at most `2^{-k}`. -/
theorem stepM_fast_levels (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    ∃ p : ℕ → ℕ, Monotone p ∧ (∀ k, k ≤ p k) ∧ ∀ k : ℕ,
      P.real {ω | ∃ t : ℝ≥0, t ≤ k ∧ (1 / 2 : ℝ) ^ k <
        |stepM W j H (p (k + 1)) t ω - stepM W j H (p k) t ω|} ≤ (1 / 2 : ℝ) ^ k := by
  set ε : ℕ → ℝ := fun k => ((1 / 2 : ℝ) ^ k) ^ 2 * (1 / 2 : ℝ) ^ k / (2 * d * k + 1) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by
    simp only [hε]; positivity
  have hr : ∀ k : ℕ, ∃ r : ℕ, ∀ s u : ℝ≥0, s ≤ u → u ≤ k →
      (u : ℝ) - s ≤ (1 / 2 : ℝ) ^ r → ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ ε k := by
    intro k
    obtain ⟨δ, hδ, hδb⟩ := osc_L2 (P := P) hHa hHc hC (k : ℝ≥0) (hεpos k)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨r, fun s u hsu hu hus => (hδb s u (hsu.trans hu) hu ?_).le⟩
    have : (s : ℝ) ≤ u := by exact_mod_cast hsu
    rw [abs_of_nonneg (by linarith)]
    linarith
  choose r hr using hr
  set p : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), (r i + 1) with hp
  have hpmono : Monotone p := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hprk : ∀ k, r k + 1 ≤ p k := fun k =>
    Finset.single_le_sum (f := fun i => r i + 1) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
  have hpk : ∀ k, k ≤ p k := by
    intro k
    have : ∑ i ∈ Finset.range (k + 1), 1 ≤ p k :=
      Finset.sum_le_sum fun i _ => Nat.le_add_left 1 (r i)
    simp at this; omega
  refine ⟨p, hpmono, hpk, fun k => ?_⟩
  have hlam : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  have hβ : ∀ s u : ℝ≥0, s ≤ u → u ≤ (k : ℕ) → (u : ℝ) - s ≤ 1 / 2 ^ p k →
      ∫ ω, (H u ω - H s ω) ^ 2 ∂P ≤ ε k := by
    intro s u hsu hu hus
    refine hr k s u hsu hu (hus.trans ?_)
    rw [← one_div_pow]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by have := hprk k; omega)
  have hmax := stepM_sup_max hW x₀ j hHm hHa hC (hpk k) (hpmono (Nat.le_succ k)) hβ hlam
  have hX : 0 ≤ ((1 / 2 : ℝ) ^ k) ^ 2 * (1 / 2 : ℝ) ^ k := by positivity
  have hD : (0 : ℝ) ≤ 2 * d * k := by positivity
  have hle : 2 * (d : ℝ) * k * ε k ≤ ((1 / 2 : ℝ) ^ k) ^ 2 * (1 / 2 : ℝ) ^ k := by
    have he : 2 * (d : ℝ) * k * ε k =
        (2 * d * k / (2 * d * k + 1)) * (((1 / 2 : ℝ) ^ k) ^ 2 * (1 / 2 : ℝ) ^ k) := by
      simp only [hε]; ring
    rw [he]
    exact mul_le_of_le_one_left hX (div_le_one_of_le₀ (by linarith) (by linarith))
  have hfin : ((1 / 2 : ℝ) ^ k) ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ k ∧ (1 / 2 : ℝ) ^ k <
        |stepM W j H (p (k + 1)) t ω - stepM W j H (p k) t ω|} ≤
      ((1 / 2 : ℝ) ^ k) ^ 2 * (1 / 2 : ℝ) ^ k := hmax.trans hle
  exact le_of_mul_le_mul_left hfin (by positivity)

/-- **Continuous version of the Ito integral** of a bounded continuous adapted integrand. -/
theorem contIto_bdd (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H Jc := by
  classical
  obtain ⟨p, hpmono, hpk, hpB⟩ := stepM_fast_levels hW x₀ j hHm hHa hHc hC
  set B : ℕ → Set Ω := fun k => {ω | ∃ t : ℝ≥0, t ≤ k ∧ (1 / 2 : ℝ) ^ k <
        |stepM W j H (p (k + 1)) t ω - stepM W j H (p k) t ω|} with hB
  have hsum : ∑' k, P (B k) ≠ ∞ := by
    have h1 : ∀ k, P (B k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := fun k => by
      rw [← ofReal_measureReal (measure_ne_top P (B k))]
      exact ENNReal.ofReal_le_ofReal (hpB k)
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' k, (1 / 2 : ℝ) ^ k)) ENNReal.ofReal_ne_top ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.tsum_le_tsum h1
  have hlim0 : P (limsup B atTop) = 0 := measure_limsup_atTop_eq_zero hsum
  set N0 := toMeasurable P (limsup B atTop) with hN0
  have hN0null : P N0 = 0 := by rw [hN0, measure_toMeasurable]; exact hlim0
  set G : Set Ω := N0ᶜ with hG
  have hGgood : ∀ ω ∈ G, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ t : ℝ≥0, t ≤ k →
      |stepM W j H (p (k + 1)) t ω - stepM W j H (p k) t ω| ≤ (1 / 2 : ℝ) ^ k := by
    intro ω hω
    have hn : ω ∉ limsup B atTop := fun h => hω (subset_toMeasurable P _ h)
    rw [mem_limsup_iff_frequently_mem, not_frequently, eventually_atTop] at hn
    obtain ⟨K, hK⟩ := hn
    refine ⟨K, fun k hk t ht => ?_⟩
    have := hK k hk
    simp only [hB, mem_setOf_eq, not_exists, not_and, not_lt] at this
    exact this t ht
  have hGF : ∀ ω ∈ G, (∀ t, CauchySeq fun k => stepM W j H (p k) t ω) ∧
      Continuous (fun t => limUnder atTop fun k => stepM W j H (p k) t ω) := by
    intro ω hω
    obtain ⟨K, hK⟩ := hGgood ω hω
    have h := geom_cauchy_limit (F := fun k t => stepM W j H (p k) t ω)
      (fun k => stepM_continuous hW.2.1 j H (p k) ω) hK
    exact ⟨h.1, h.2.2⟩
  set Jc : ℝ≥0 → Ω → ℝ := fun t ω =>
    if ω ∈ G then limUnder atTop (fun k => stepM W j H (p k) t ω) else 0 with hJc
  have hGtend : ∀ ω ∈ G, ∀ t,
      Tendsto (fun k => stepM W j H (p k) t ω) atTop (𝓝 (Jc t ω)) := by
    intro ω hω t
    simp only [hJc, hω, if_true]
    exact ((hGF ω hω).1 t).tendsto_limUnder
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]; simpa [hG] using hN0null
  obtain ⟨J, hJ⟩ := exists_hasBrownianItoIntegral hW x₀ j hHm hHc
  have hEq : ∀ t, J t =ᵐ[P] Jc t := by
    intro t
    have hS := (stepM_tendsto hW x₀ j hHm hHa hHc hC hJ t).comp
      (tendsto_atTop_mono hpk tendsto_id)
    obtain ⟨ns, hns, hae⟩ := hS.exists_seq_tendsto_ae
    filter_upwards [hae, hGae] with ω h1 h2
    exact tendsto_nhds_unique h1 ((hGtend ω h2 t).comp hns.tendsto_atTop)
  refine ⟨Jc, fun ω => ?_, fun t => ?_, fun t => ?_, fun ω => ?_, ⟨hJ.1, fun t => (hJ.2 t).imp
    fun a ha => ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.congr_right (hEq t)⟩⟩⟩
  · by_cases hω : ω ∈ G
    · simp only [hJc, hω, if_true]
      exact (hGF ω hω).2
    · simp only [hJc, hω, if_false]
      exact continuous_const
  · have hGm : MeasurableSet[completedBrownianPast P W (fun _ => x₀) t] G := by
      refine MeasurableSet.compl ?_
      refine (le_sup_right : MeasurableSpace.generateFrom
        {A | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ A ⊆ N} ≤ _) _ ?_
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨N0, measurableSet_toMeasurable P _, hN0null, subset_rfl⟩
    have hfm : ∀ k, Measurable[completedBrownianPast P W (fun _ => x₀) t]
        (G.indicator (stepM W j H (p k) t)) := fun k =>
      (stepM_adapted x₀ j hHm (p k) t).indicator hGm
    refine @measurable_of_tendsto_metrizable Ω ℝ
      (completedBrownianPast P W (fun _ => x₀) t) _ _ _ _ _ _ hfm ?_
    refine tendsto_pi_nhds.2 fun ω => ?_
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
      exact hGtend ω hω t
    · simp only [indicator_of_notMem hω, hJc, hω, if_false]
      exact tendsto_const_nhds
  · have hGm : MeasurableSet G := (measurableSet_toMeasurable P _).compl
    have hfm : ∀ k, Measurable (G.indicator (stepM W j H (p k) t)) := fun k =>
      (stepM_measurable hW j hHa (p k) t).indicator hGm
    refine measurable_of_tendsto_metrizable hfm (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
      exact hGtend ω hω t
    · simp only [indicator_of_notMem hω, hJc, hω, if_false]
      exact tendsto_const_nhds
  · by_cases hω : ω ∈ G
    · refine tendsto_nhds_unique (hGtend ω hω 0) ?_
      simp only [stepM_zero]
      exact tendsto_const_nhds
    · simp only [hJc, hω, if_false]

end QD

end ItoLib

end FlatM_QD
-- ===== Q =====
section FlatM_Q
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

end FlatM_Q
-- ===== R =====
section FlatM_R
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

end FlatM_R
-- ===== S =====
section FlatM_S
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

end FlatM_S
-- ===== U =====
section FlatM_U
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

end FlatM_U
-- ===== QE =====
section FlatM_QE
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

end FlatM_QE
-- ===== QF =====
section FlatM_QF
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

end FlatM_QF
-- ===== QG =====
section FlatM_QG
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

end FlatM_QG
-- ===== QH =====
section FlatM_QH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- Ito isometry (upper bound) for the difference of two Ito integrals. -/
theorem ito_sq_le2 {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J H₁ J₁ : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hHm₁ : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s))
    (hHc₁ : ∀ ω, Continuous fun s => H₁ s ω) (hC₁ : ∀ s ω, |H₁ s ω| ≤ C)
    (hJ₁ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H₁ J₁) (t : ℝ≥0) :
    ∫ ω, (J t ω - J₁ t ω) ^ 2 ∂P ≤
      ∫ ω, (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P := by
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : ∀ s ω, |H s ω| ≤ C' := fun s ω => (hC s ω).trans (le_max_left _ _)
  have hC'1 : ∀ s ω, |H₁ s ω| ≤ C' := fun s ω => (hC₁ s ω).trans (le_max_left _ _)
  have hC' : ∀ s ω, |H s ω - H₁ s ω| ≤ 2 * C' := fun s ω =>
    (abs_sub _ _).trans (by linarith [hC'0 s ω, hC'1 s ω])
  set S : ℕ → Ω → ℝ := fun n =>
    itoStepSum (fun s ω => W s ω j) t n
      (fun k ω => leftCoef (clampH H n) t n k ω - leftCoef (clampH H₁ n) t n k ω) with hSdef
  have hconv : TendstoInMeasure P S atTop (fun ω => J t ω - J₁ t ω) := by
    refine (tendstoInMeasure_sub_real
      (clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm hHc hJ t)
      (clampLeft_tendsto_of_hasBrownianItoIntegral hW x₀ j hHm₁ hHc₁ hJ₁ t)).congr_left
      (fun n => ae_of_all _ fun ω => ?_)
    exact itoStepSum_sub _ _ _ _ _ _
  have ham : ∀ (n k : ℕ), Measurable[completedBrownianPast P W (fun _ => x₀)
      ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)]
      (fun ω => leftCoef (clampH H n) t n k ω - leftCoef (clampH H₁ n) t n k ω) :=
    fun n k => (clampH_measurable (hHm _) _).sub (clampH_measurable (hHm₁ _) _)
  have hab : ∀ (n k : ℕ) ω,
      |leftCoef (clampH H n) t n k ω - leftCoef (clampH H₁ n) t n k ω| ≤ 2 * C' := fun n k ω => by
    have h1 := (abs_clampH_le_abs H (Nat.cast_nonneg n) (dyTime t n k) ω).trans (hC'0 _ ω)
    have h2 := (abs_clampH_le_abs H₁ (Nat.cast_nonneg n) (dyTime t n k) ω).trans (hC'1 _ ω)
    exact (abs_sub _ _).trans (by simp only [leftCoef]; linarith)
  have hSm : ∀ n, MemLp (S n) 2 P := fun n =>
    itoStepSum_memLp hW t n j _
      (fun k _ => aestronglyMeasurable_of_completedPast hW x₀ _ (ham n k)) (2 * C')
      (fun k _ ω => hab n k ω)
  have hHae : ∀ s, AEStronglyMeasurable (fun ω => H s ω - H₁ s ω) P := fun s =>
    aestronglyMeasurable_of_completedPast hW x₀ s ((hHm s).sub (hHm₁ s))
  -- Riemann sums of `H²`
  set R : ℕ → Ω → ℝ := fun n ω => (∑ k ∈ Finset.range (2 ^ n), (H (dyTime t n k) ω - H₁ (dyTime t n k) ω) ^ 2) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) with hR
  have hRlim : ∀ ω, Tendsto (fun n => R n ω) atTop
      (𝓝 (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2)) :=
    fun ω => riemann_tendsto (H := fun s ω => (H s ω - H₁ s ω) ^ 2) (fun ω => ((hHc ω).sub (hHc₁ ω)).pow 2) t ω
  have hRm : ∀ n, AEStronglyMeasurable (R n) P := fun n =>
    (Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hHae _).pow 2).mul_const _
  have hsq : ∀ s ω, (H s ω - H₁ s ω) ^ 2 ≤ (2 * C') ^ 2 := fun s ω => by
    have := hC' s ω
    nlinarith [abs_nonneg (H s ω - H₁ s ω), sq_abs (H s ω - H₁ s ω)]
  have hRb : ∀ n ω, ‖R n ω‖ ≤ (2 * C') ^ 2 * t := by
    intro n ω
    have h0 : 0 ≤ R n ω :=
      mul_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (NNReal.coe_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc R n ω ≤ (∑ k ∈ Finset.range (2 ^ n), (2 * C') ^ 2) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) :=
          mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun k _ => hsq _ _) (NNReal.coe_nonneg _)
      _ = (2 * C') ^ 2 * t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
  have hERlim : Tendsto (fun n => ∫ ω, R n ω ∂P) atTop
      (𝓝 (∫ ω, (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (2 * C') ^ 2 * t) hRm (integrable_const _)
      (fun n => ae_of_all _ (hRb n)) (ae_of_all _ hRlim)
  have hint : ∀ s, Integrable (fun ω => (H s ω - H₁ s ω) ^ 2) P := fun s =>
    Integrable.of_bound ((hHae s).pow 2) ((2 * C') ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq s ω)
  have hSR : ∀ n : ℕ, C' ≤ n → ∫ ω, S n ω ^ 2 ∂P = ∫ ω, R n ω ∂P := by
    intro n hn
    have e1 : ∫ ω, S n ω ^ 2 ∂P = ∑ k ∈ Finset.range (2 ^ n),
        (∫ ω, (leftCoef (clampH H n) t n k ω - leftCoef (clampH H₁ n) t n k ω) ^ 2 ∂P) *
          ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) :=
      itoStepSum_isometry hW x₀ t n j _ (fun k _ => ham n k) (2 * C') (fun k _ ω => hab n k ω)
    have e2 : ∫ ω, R n ω ∂P = ∑ k ∈ Finset.range (2 ^ n),
        (∫ ω, (H (dyTime t n k) ω - H₁ (dyTime t n k) ω) ^ 2 ∂P) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
      simp only [hR]
      rw [integral_mul_const, integral_finset_sum _ (fun k _ => hint _), Finset.sum_mul]
    rw [e1, e2]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [leftCoef]
    rw [clampH_eq_of_abs_le H ((hC'0 _ ω).trans hn), clampH_eq_of_abs_le H₁ ((hC'1 _ ω).trans hn)]
  set I : ℝ := ∫ ω, (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P with hI
  have hlim2 : Tendsto (fun n => ∫ ω, S n ω ^ 2 ∂P) atTop (𝓝 I) := by
    refine hERlim.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈C'⌉₊] with n hn
    exact (hSR n ((Nat.le_ceil _).trans (Nat.cast_le.2 hn))).symm
  have hI0 : 0 ≤ I := integral_nonneg fun ω =>
    intervalIntegral.integral_nonneg t.2 (fun u _ => sq_nonneg _)
  have hSaesm : ∀ n, AEStronglyMeasurable (S n) P := fun n => (hSm n).1
  have hJm : AEStronglyMeasurable (fun ω => J t ω - J₁ t ω) P := hconv.aestronglyMeasurable hSaesm
  obtain ⟨φ, hφ, hae⟩ := hconv.exists_seq_tendsto_ae
  have hlin : ∀ n, ∫⁻ ω, ENNReal.ofReal (S n ω ^ 2) ∂P = ENNReal.ofReal (∫ ω, S n ω ^ 2 ∂P) :=
    fun n => (ofReal_integral_eq_lintegral_ofReal (hSm n).integrable_sq
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)).symm
  have hfatou : ∫⁻ ω, ENNReal.ofReal ((J t ω - J₁ t ω) ^ 2) ∂P ≤ ENNReal.ofReal I := by
    calc ∫⁻ ω, ENNReal.ofReal ((J t ω - J₁ t ω) ^ 2) ∂P
        = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (S (φ k) ω ^ 2)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            ((continuous_pow 2).continuousAt.tendsto.comp hω)).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (S (φ k) ω ^ 2) ∂P) atTop :=
          lintegral_liminf_le' fun k =>
            (ENNReal.measurable_ofReal.comp_aemeasurable ((hSaesm (φ k)).aemeasurable.pow_const 2))
      _ = ENNReal.ofReal I := by
          simp_rw [hlin]
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            (hlim2.comp hφ.tendsto_atTop)).liminf_eq
  have hJint2 : Integrable (fun ω => (J t ω - J₁ t ω) ^ 2) P := by
    refine ⟨hJm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact hfatou.trans_lt ENNReal.ofReal_lt_top
  rw [← ofReal_integral_eq_lintegral_ofReal hJint2
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hI0).1 hfatou

end QH

end ItoLib

end FlatM_QH
-- ===== QI =====
section FlatM_QI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem stepM_sub' (W : ℝ≥0 → Ω → SDEState d) (j : Fin d) (H H₁ : ℝ≥0 → Ω → ℝ) (q : ℕ)
    (t : ℝ≥0) (ω : Ω) :
    stepM W j H q t ω - stepM W j H₁ q t ω = stepM W j (fun s ω => H s ω - H₁ s ω) q t ω := by
  simp only [stepM, ← Finset.sum_sub_distrib, sub_mul]

/-- Discrete maximal inequality for the step integral on its own grid. -/
theorem stepM_grid_max {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {G : ℝ≥0 → Ω → ℝ} (hGm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (G s))
    (hGa : ∀ s, Measurable (G s)) {C : ℝ} (hC : ∀ s ω, |G s ω| ≤ C) {N q : ℕ} (hNq : N ≤ q)
    {β : ℝ} (hβ : ∀ s : ℝ≥0, s ≤ N → ∫ ω, G s ω ^ 2 ∂P ≤ β) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ k ≤ N * 2 ^ q, lam ≤ |stepM W j G q (gpt q k) ω|} ≤
      2 * d * N * β := by
  set φ : ℕ → Ω → ℝ := fun i ω => G (gpt q i) ω with hφ
  have hset : {ω | ∃ k ≤ N * 2 ^ q, lam ≤ |stepM W j G q (gpt q k) ω|} =
      {ω | ∃ k ≤ N * 2 ^ q, lam ≤ |dsum W j q φ k ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun k => and_congr_right fun hk => ?_
    rw [stepM_grid W j G (le_refl q) (hk.trans (Nat.mul_le_mul_right _ hNq)) ω]
    simp [hφ]
  have hφm : ∀ i, Measurable[completedBrownianPast P W (fun _ => x₀) (gpt q i)] (φ i) :=
    fun i => hGm _
  have hφa : ∀ i, Measurable (φ i) := fun i => hGa _
  have hφK : ∀ i ω, |φ i ω| ≤ C := fun i ω => hC _ ω
  have hmax := dsum_max hW x₀ j q hφm hφa hφK (N * 2 ^ q) hlam
  rw [hset]
  refine hmax.trans ?_
  have hβ0 : 0 ≤ β := le_trans (integral_nonneg fun ω => sq_nonneg _) (hβ 0 (by simp))
  calc ∑ i ∈ Finset.range (N * 2 ^ q), 2 * d * (hm q : ℝ) * ∫ ω, φ i ω ^ 2 ∂P
      ≤ ∑ i ∈ Finset.range (N * 2 ^ q), 2 * d * (hm q : ℝ) * β := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by rw [hm_coe]; positivity)
        refine hβ _ ?_
        rw [← gpt_nat q N]
        exact (gpt_le_iff _ _ _).2 (Finset.mem_range.1 hi).le
    _ = 2 * d * N * β := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hm_coe]
        push_cast
        field_simp

set_option maxHeartbeats 1000000 in
/-- **Weak maximal inequality** for the difference of continuous versions of two Ito integrals
of bounded continuous adapted integrands, with a uniform `L²` bound `β` on the difference of
the integrands over `[0, N]`. -/
theorem contIto_max {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H H₁ J J₁ : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C)
    (hHm₁ : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s))
    (hHa₁ : ∀ s, Measurable (H₁ s)) (hHc₁ : ∀ ω, Continuous fun s => H₁ s ω) {C₁ : ℝ}
    (hC₁ : ∀ s ω, |H₁ s ω| ≤ C₁)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ₁ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H₁ J₁)
    (hJc : ∀ ω, Continuous fun t => J t ω) (hJc₁ : ∀ ω, Continuous fun t => J₁ t ω)
    {N : ℕ} {β : ℝ} (hβ : ∀ s : ℝ≥0, s ≤ N → ∫ ω, (H s ω - H₁ s ω) ^ 2 ∂P ≤ β)
    {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω - J₁ t ω|} ≤ 2 * d * N * β := by
  have hβ0 : 0 ≤ β := le_trans (integral_nonneg fun ω => sq_nonneg _) (hβ 0 (by simp))
  set G : ℝ≥0 → Ω → ℝ := fun s ω => H s ω - H₁ s ω with hGdef
  set D : ℝ≥0 → Ω → ℝ := fun t ω => J t ω - J₁ t ω with hD
  have hDc : ∀ ω, Continuous fun t => D t ω := fun ω => (hJc ω).sub (hJc₁ ω)
  set S : ℕ → ℝ≥0 → Ω → ℝ := fun q t ω => stepM W j G q t ω with hS
  have hconv : ∀ t, TendstoInMeasure P (fun q => S q t) atTop (D t) := by
    intro t
    have h := tendstoInMeasure_sub_real (stepM_tendsto hW x₀ j hHm hHa hHc hC hJ t)
      (stepM_tendsto hW x₀ j hHm₁ hHa₁ hHc₁ hC₁ hJ₁ t)
    refine h.congr_left (fun q => ae_of_all _ fun ω => ?_)
    simp only [hS, hGdef]
    exact stepM_sub' W j H H₁ q t ω
  have hGm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (G s) :=
    fun s => (hHm s).sub (hHm₁ s)
  have hGa : ∀ s, Measurable (G s) := fun s => (hHa s).sub (hHa₁ s)
  have hGC : ∀ s ω, |G s ω| ≤ C + C₁ := fun s ω =>
    (abs_sub _ _).trans (add_le_add (hC s ω) (hC₁ s ω))
  let A : ℕ → Set Ω := fun r => {ω | ∃ k ≤ N * 2 ^ r, lam < |D (gpt r k) ω|}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun r ω hω => ?_
    obtain ⟨k, hk, hl⟩ := hω
    refine ⟨k * 2 ^ (r + 1 - r), ?_, ?_⟩
    · have h2 : 2 ^ (r + 1 - r) = 2 := by simp
      rw [h2, pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right 2 hk
    · rwa [← gpt_lift (Nat.le_succ r)]
  -- level bound for every `lam' < lam`
  have hlev : ∀ r, ∀ lam' : ℝ, 0 < lam' → lam' < lam →
      P (A r) ≤ ENNReal.ofReal (2 * d * N * β / lam' ^ 2) := by
    intro r lam' hl0 hll
    set Bd' : ℝ := 2 * d * N * β / lam' ^ 2 with hBd'
    set E : ℕ → ℕ → Set Ω := fun q k =>
      {ω | lam - lam' ≤ dist (S q (gpt r k) ω) (D (gpt r k) ω)} with hE
    have hEt : ∀ k, Tendsto (fun q => P (E q k)) atTop (𝓝 0) := fun k =>
      tendstoInMeasure_iff_dist.1 (hconv (gpt r k)) (lam - lam') (by linarith)
    have hsumt : Tendsto (fun q => ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k)) atTop
        (𝓝 0) := by
      simpa using tendsto_finset_sum (Finset.range (N * 2 ^ r + 1)) fun k _ => hEt k
    have hle : ∀ q, max N r ≤ q →
        P (A r) ≤ ENNReal.ofReal Bd' + ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k) := by
      intro q hq
      have hNq : N ≤ q := (le_max_left _ _).trans hq
      have hrq : r ≤ q := (le_max_right _ _).trans hq
      set Gq : Set Ω := {ω | ∃ k ≤ N * 2 ^ q, lam' ≤ |stepM W j G q (gpt q k) ω|} with hGq
      have hGqb : P Gq ≤ ENNReal.ofReal Bd' := by
        have h := stepM_grid_max hW x₀ j hGm hGa hGC hNq (β := β) (fun s hs => hβ s hs) hl0
        rw [← ofReal_measureReal (measure_ne_top P _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hBd', le_div_iff₀ (by positivity)]
        linarith
      have hsub : A r ⊆ Gq ∪ ⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k := by
        rintro ω ⟨k, hk, hlt⟩
        by_cases hEk : ω ∈ E q k
        · exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hEk)
        · left
          simp only [hE, Set.mem_setOf_eq, not_le, Real.dist_eq] at hEk
          refine ⟨k * 2 ^ (q - r), ?_, ?_⟩
          · calc k * 2 ^ (q - r) ≤ N * 2 ^ r * 2 ^ (q - r) := Nat.mul_le_mul_right _ hk
              _ = N * 2 ^ q := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hrq]
          · rw [← gpt_lift hrq]
            have h1 : |D (gpt r k) ω| ≤ |S q (gpt r k) ω| + |S q (gpt r k) ω - D (gpt r k) ω| := by
              have h0 := abs_sub_abs_le_abs_sub (D (gpt r k) ω) (S q (gpt r k) ω)
              have h0' := abs_sub_comm (D (gpt r k) ω) (S q (gpt r k) ω)
              linarith
            have : lam' ≤ |S q (gpt r k) ω| := by linarith
            simpa [hS] using this
      calc P (A r) ≤ P (Gq ∪ ⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k) := measure_mono hsub
        _ ≤ P Gq + P (⋃ k ∈ Finset.range (N * 2 ^ r + 1), E q k) := measure_union_le _ _
        _ ≤ ENNReal.ofReal Bd' + ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k) :=
            add_le_add hGqb (measure_biUnion_finset_le _ _)
    have hlim : Tendsto (fun q => ENNReal.ofReal Bd' +
        ∑ k ∈ Finset.range (N * 2 ^ r + 1), P (E q k)) atTop (𝓝 (ENNReal.ofReal Bd' + 0)) :=
      tendsto_const_nhds.add hsumt
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨max N r, hle⟩)
  -- pass `lam' → lam`
  have hlevR : ∀ r, lam ^ 2 * P.real (A r) ≤ 2 * d * N * β := by
    intro r
    have hev : ∀ᶠ l in 𝓝[<] lam, l ^ 2 * P.real (A r) ≤ 2 * d * N * β := by
      filter_upwards [Ioo_mem_nhdsLT hlam] with l hl
      have h := hlev r l hl.1 hl.2
      have h2 : P.real (A r) ≤ 2 * d * N * β / l ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (by have := hl.1; positivity) h
      rw [le_div_iff₀ (by have := hl.1; positivity)] at h2
      linarith
    have ht : Tendsto (fun l : ℝ => l ^ 2 * P.real (A r)) (𝓝[<] lam)
        (𝓝 (lam ^ 2 * P.real (A r))) :=
      ((continuous_pow 2).mul continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto ht hev
  set Bd : ℝ := 2 * d * N * β / lam ^ 2 with hBd
  have hall : ∀ r, P.real (A r) ≤ Bd := fun r => by
    rw [hBd, le_div_iff₀ (by positivity)]; linarith [hlevR r]
  -- the continuous-time event is inside the union of the grid events
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ⊆ ⋃ r, A r := by
    rintro ω ⟨t, htN, hlt⟩
    let kr : ℕ → ℕ := fun r => ⌊(t : ℝ) * 2 ^ r⌋₊
    have hconv' : Tendsto (fun r => gpt r (kr r)) atTop (𝓝 t) := by
      rw [← NNReal.tendsto_coe]
      have hup : ∀ r, (gpt r (kr r) : ℝ) ≤ t := fun r => by
        rw [gpt_coe, div_le_iff₀ (by positivity)]
        exact Nat.floor_le (by positivity)
      have hlo : ∀ r, (t : ℝ) - 1 / 2 ^ r ≤ gpt r (kr r) := fun r => by
        rw [gpt_coe, le_div_iff₀ (by positivity), sub_mul, one_div,
          inv_mul_cancel₀ (by positivity)]
        linarith only [Nat.lt_floor_add_one ((t : ℝ) * 2 ^ r)]
      have hl : Tendsto (fun r : ℕ => (t : ℝ) - 1 / 2 ^ r) atTop (𝓝 t) := by
        have h0 : Tendsto (fun r : ℕ => (1 : ℝ) / 2 ^ r) atTop (𝓝 0) := by
          simpa [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        simpa using h0.const_sub (t : ℝ)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup
    have hev := ((continuous_abs.comp (hDc ω)).tendsto t).comp hconv'
    obtain ⟨r, hr⟩ := (hev.eventually (lt_mem_nhds hlt)).exists
    refine Set.mem_iUnion.2 ⟨r, kr r, ?_, hr⟩
    have : (t : ℝ) * 2 ^ r ≤ ((N * 2 ^ r : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htN) (by positivity)
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  have hU : P (⋃ r, A r) ≤ ENNReal.ofReal Bd := by
    rw [hAmono.measure_iUnion]
    refine iSup_le fun r => ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hall r)
  have hS' : P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |D t ω|} ≤ Bd := by
    have h1 := (measure_mono hsub).trans hU
    have hB0 : 0 ≤ Bd := by rw [hBd]; positivity
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  have := mul_le_mul_of_nonneg_left hS' (sq_nonneg lam)
  rw [hBd, mul_div_cancel₀ _ (by positivity)] at this
  exact this

end QI
end ItoLib

end FlatM_QI
-- ===== QJ =====
section FlatM_QJ
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

end FlatM_QJ
-- ===== QK =====
section FlatM_QK
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

end FlatM_QK
-- ===== QL =====
section FlatM_QL
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

end FlatM_QL
-- ===== QM =====
section FlatM_QM
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

end FlatM_QM
-- ===== QN =====
section FlatM_QN
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

end FlatM_QN
-- ===== QO =====
section FlatM_QO
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

end FlatM_QO
-- ===== QP =====
section FlatM_QP
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

end FlatM_QP
-- ===== QZ4 =====
section FlatM_QZ4
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

end FlatM_QZ4
-- ===== E5A =====
section FlatM_E5A
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

end FlatM_E5A
-- ===== E5B =====
section FlatM_E5B
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

end FlatM_E5B
-- ===== E6F =====
section FlatM_E6F
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6F
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6F

end ItoLib

end FlatM_E6F
-- ===== E6P =====
section FlatM_E6P
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6P
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6P

end ItoLib

end FlatM_E6P
-- ===== E6Q =====
section FlatM_E6Q
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6Q
/-! Clause 1 toolkit (E6, part 2): a solution of a Kolmogorov-structured SDE started in the
orthant stays in the orthant for all times, almost surely. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6Q

end ItoLib

end FlatM_E6Q
-- ===== E6T =====
section FlatM_E6T
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6T
/-! Clause 1 toolkit (E6, part 3): a Kolmogorov-structured truncation of the coefficients:
evaluate the true coefficients at the box projection `boxP (-R) R y`. It is bounded, globally
Lipschitz, equal to the true coefficients on the box, and of the form `y_k * (bounded)`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6T

end ItoLib

end FlatM_E6T
-- ===== V =====
section FlatM_V
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

end FlatM_V
-- ===== W =====
section FlatM_W
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

end FlatM_W
-- ===== Y =====
section FlatM_Y
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

end FlatM_Y
-- ===== E6L =====
section FlatM_E6L
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6L
/-! Clause 1 toolkit (E6, part 4): the saturated Lyapunov profile `lyS m = hsat m ∘ psiK`,
derivatives of `y ↦ ψ(cᵀy)`, and the time-slot test function
`F(x,y,a) = e^{-a} (Φ(y) + K (T - x_{i0}) - λ) + λ` with its generator. -/
open StochKolmogorov.Persist

variable {n : ℕ}

end E6L

section E6Lb
variable {d : ℕ}

end E6Lb

end ItoLib

end FlatM_E6L
-- ===== E6M =====
section FlatM_E6M
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6M
/-! Clause 1 toolkit (E6, part 5): a maximal inequality without martingale theory. Along a
solution `Y` that stays in a set `D` on which the generator of `Φ ≥ 0` is at most `K`, the
probability that `Φ(Y_s) > λ` for some `s < t` is at most `(Φ(x) + K t) / (λ (1 - e⁻¹))`.
Proof: the Ito formula for `F = e^{-a}(Φ(y) + K (T - s) - λ) + λ`, where the clock `a` runs at
rate `M (Φ(Y) + K (T - s) - λ)⁺` (the time `s` is carried in the `X` slot), and `M → ∞`. -/
variable {n : ℕ}

end E6M

end ItoLib

end FlatM_E6M
-- ===== X41 =====
section FlatM_X41
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

end ItoLib

end FlatM_X41
-- ===== E6A =====
section FlatM_E6A
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6A
/-! Clause 1 (E6, assembly): non-explosion of the truncated Kolmogorov systems via the saturated
Lyapunov function `lyS m (cᵀy)` and `exceed_prob_le`, then `glue_solution`. -/

open StochKolmogorov.Persist

variable {n : ℕ}

end E6A

end ItoLib

end FlatM_E6A
-- ===== L31 =====
section FlatM_L31
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz StochKolmogorov.Persist

end ItoLib


end FlatM_L31

open EthierKurtz in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) :
    (∀ (j : Fin d) (H H' J J' : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s)) →
      (∀ ω, Continuous fun s => H' s ω) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H' J' →
      ∀ (s : ℝ≥0) (E : Set Ω),
      (∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N →
        H ((i : ℝ≥0) * s / 2 ^ N) ω = H' ((i : ℝ≥0) * s / 2 ^ N) ω) →
      ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H J H₁ J₁ : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) → ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s)) →
      (∀ ω, Continuous fun s => H₁ s ω) → (∀ s ω, |H₁ s ω| ≤ C) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H₁ J₁ →
      ∀ t : ℝ≥0, ∫ ω, (J t ω - J₁ t ω) ^ 2 ∂P ≤
        ∫ ω, (∫ u in (0 : ℝ)..t.val, (H u.toNNReal ω - H₁ u.toNNReal ω) ^ 2) ∂P) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
        (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
        (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
        HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
          (fun s ω => W s ω j) H Jc) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H H₁ J J₁ : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H₁ s)) →
      (∀ s, Measurable (H₁ s)) → (∀ ω, Continuous fun s => H₁ s ω) →
      ∀ C₁ : ℝ, (∀ s ω, |H₁ s ω| ≤ C₁) →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H J →
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H₁ J₁ →
      (∀ ω, Continuous fun t => J t ω) → (∀ ω, Continuous fun t => J₁ t ω) →
      ∀ (N : ℕ) (β : ℝ), (∀ s : ℝ≥0, s ≤ N → ∫ ω, (H s ω - H₁ s ω) ^ 2 ∂P ≤ β) →
      ∀ lam : ℝ, 0 < lam →
      lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω - J₁ t ω|} ≤ 2 * d * N * β) := by
  exact ⟨fun j H H' J J' hHm hHc hH'm hH'c hJ hJ' s E hE =>
      ItoLib.hasBrownianItoIntegral_eq_on hW x₀ j hHm hHc hH'm hH'c hJ hJ' s E hE,
    fun j H J H₁ J₁ hHm hHc C hC hJ hHm₁ hHc₁ hC₁ hJ₁ t =>
      ItoLib.ito_sq_le2 hW x₀ j hHm hHc hC hJ hHm₁ hHc₁ hC₁ hJ₁ t,
    fun j H hHm hHa hHc C hC => ItoLib.contIto_bdd hW x₀ j hHm hHa hHc hC,
    fun j H H₁ J J₁ hHm hHa hHc C hC hHm₁ hHa₁ hHc₁ C₁ hC₁ hJ hJ₁ hJc hJc₁ N β hβ lam hlam =>
      ItoLib.contIto_max hW x₀ j hHm hHa hHc hC hHm₁ hHa₁ hHc₁ hC₁ hJ hJ₁ hJc hJc₁ hβ hlam⟩
