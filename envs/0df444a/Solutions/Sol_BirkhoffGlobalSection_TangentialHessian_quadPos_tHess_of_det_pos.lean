-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.quadPos_tHess_of_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:56:46.599984+00:00
-- url     : https://prove2.me/submissions/3b64b5d9-917c-41cd-b885-696fe58ffdc9

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_quadPos_tHess_leftCollisionPoint
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_left_energy_component_barrier_ball
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

noncomputable section

/-- The quadratic form of `tHess μ c x` at `a`. -/
def tForm (μ c : ℝ) (x : Phase) (a : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * tHess μ c x i j

/-- The left collision point lies on the selected component for `0 ≤ μ ≤ 1`,
so in particular at the `μ = 0` edge of Proposition 4.4 (the platform lemma
`leftCollisionPoint_mem_leftEnergyComponent` needs `0 < μ`). -/
theorem leftCollisionPoint_mem_of_le (μ c : ℝ) (hμ1 : μ ≤ 1) :
    leftCollisionPoint μ ∈ leftEnergyComponent μ c := by
  apply mem_connectedComponentIn
  refine ⟨?_, ?_⟩
  · have h : Real.sqrt (1 - μ) ^ 2 = 1 - μ := Real.sq_sqrt (by linarith)
    simp [leviCivitaHamiltonian, leftCollisionPoint, wNormSq, zNormSq,
      secondCollisionDistanceSq, h]
  · simp [leftCollisionPoint, secondCollisionDistanceSq]

theorem tHess_symm (μ c : ℝ) (s : Phase) (i j : Fin 3) :
    tHess μ c s i j = tHess μ c s j i := by
  simp only [tHess, tHessR]
  ring

theorem sq_one_sub_two_zNormSq_le (s : Phase) :
    (1 - 2 * zNormSq s) ^ 2 ≤ secondCollisionDistanceSq s := by
  unfold zNormSq secondCollisionDistanceSq
  nlinarith [sq_nonneg (s 1)]

theorem mem_U_of_two_zNormSq_le {s : Phase} (hz : 2 * zNormSq s ≤ 3 / 5) : s ∈ U := by
  show 0 < secondCollisionDistanceSq s
  have h1 : (2 : ℝ) / 5 ≤ 1 - 2 * zNormSq s := by linarith
  nlinarith [sq_one_sub_two_zNormSq_le s]

theorem continuous_secondCollisionDistanceSq : Continuous secondCollisionDistanceSq := by
  unfold secondCollisionDistanceSq; fun_prop

theorem isOpen_U : IsOpen U :=
  isOpen_lt continuous_const continuous_secondCollisionDistanceSq

theorem continuousOn_kGrad' (μ c : ℝ) : ContinuousOn (kGrad μ c) U :=
  (leviCivita_explicit_derivatives μ c).2.2.1

theorem continuousOn_kHess' (μ c : ℝ) : ContinuousOn (kHess μ c) U :=
  (leviCivita_explicit_derivatives μ c).2.2.2

/-- A symmetric `3 × 3` matrix with nonzero determinant that is not positive definite
takes a negative value. -/
theorem exists_neg_of_not_quadPos {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : ∀ i j, A i j = A j i) (hdet : A.det ≠ 0) (h : ¬ QuadPos A) :
    ∃ a : Fin 3 → ℝ, ∑ i, ∑ j, a i * a j * A i j < 0 := by
  by_contra hneg
  simp only [not_exists, not_lt] at hneg
  simp only [QuadPos, not_forall, not_lt] at h
  obtain ⟨a, ha, hle⟩ := h
  have hQa : ∑ i, ∑ j, a i * a j * A i j = 0 := le_antisymm hle (hneg a)
  set b := A.mulVec a with hb
  have hsym10 := hsym 1 0
  have hsym20 := hsym 2 0
  have hsym21 := hsym 2 1
  -- `Q(a + t b) = 2 t |b|² + t² Q(b)` because `b = A a` and `A` is symmetric
  have key : ∀ t : ℝ,
      0 ≤ 2 * t * (b ⬝ᵥ b) + t ^ 2 * ∑ i, ∑ j, b i * b j * A i j := by
    intro t
    have h1 := hneg (a + t • b)
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 hQa ⊢
    simp only [hb, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at h1 ⊢
    rw [hsym10, hsym20, hsym21] at h1 hQa ⊢
    linear_combination h1 + hQa
  have hbb : b ⬝ᵥ b = 0 := by
    set q := ∑ i, ∑ j, b i * b j * A i j
    have hq : 0 ≤ q := hneg b
    have hbb0 : 0 ≤ b ⬝ᵥ b := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (b i)
    have := key (-(b ⬝ᵥ b) / (q + 1))
    have hq1 : 0 < q + 1 := by linarith
    rw [div_pow, neg_sq] at this
    have e : 2 * (-(b ⬝ᵥ b) / (q + 1)) * (b ⬝ᵥ b) + (b ⬝ᵥ b) ^ 2 / (q + 1) ^ 2 * q =
        -((b ⬝ᵥ b) ^ 2 * (q + 2)) / (q + 1) ^ 2 := by
      field_simp; ring
    rw [e] at this
    have hden : 0 < (q + 1) ^ 2 := by positivity
    have h3 : 0 ≤ -((b ⬝ᵥ b) ^ 2 * (q + 2)) := by
      have := mul_nonneg this hden.le
      rwa [div_mul_cancel₀ _ hden.ne'] at this
    have h4 : (b ⬝ᵥ b) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (b ⬝ᵥ b)]
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h4 (sq_nonneg _))
  have hb0 : A.mulVec a = 0 := dotProduct_self_eq_zero.mp hbb
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨a, ha, hb0⟩)

theorem continuous_frameHess (i j : Fin 3) :
    Continuous fun p : Phase × Matrix (Fin 4) (Fin 4) ℝ => frameHess p.1 p.2 i j := by
  fin_cases i <;> fin_cases j <;>
    simp [frameHess, frame, qI, qJ, qK, dotProduct, Fin.sum_univ_four] <;>
    fun_prop

theorem continuousAt_tHess (μ c : ℝ) {s : Phase} (hs : s ∈ U) (i j : Fin 3) :
    ContinuousAt (fun x => tHess μ c x i j) s := by
  have hg : ContinuousAt (kGrad μ c) s :=
    (continuousOn_kGrad' μ c).continuousAt (isOpen_U.mem_nhds hs)
  have hH : ContinuousAt (kHess μ c) s :=
    (continuousOn_kHess' μ c).continuousAt (isOpen_U.mem_nhds hs)
  have hp : ContinuousAt (fun x => (kGrad μ c x, kHess μ c x)) s := hg.prodMk hH
  have e : (fun x => tHess μ c x i j) = fun x =>
      (frameHess (kGrad μ c x, kHess μ c x).1 (kGrad μ c x, kHess μ c x).2 i j
        + frameHess (kGrad μ c x, kHess μ c x).1 (kGrad μ c x, kHess μ c x).2 j i) / 2 :=
    rfl
  rw [e]
  exact (((continuous_frameHess i j).continuousAt.comp hp).add
    ((continuous_frameHess j i).continuousAt.comp hp)).div_const 2

theorem continuousAt_tForm (μ c : ℝ) {s : Phase} (hs : s ∈ U) (a : Fin 3 → ℝ) :
    ContinuousAt (fun x => tForm μ c x a) s := by
  unfold tForm
  have := fun i j => continuousAt_tHess μ c hs i j
  simp only [Fin.sum_univ_three]
  fun_prop

theorem continuousAt_tForm_prod (μ c : ℝ) {s : Phase} (hs : s ∈ U) (a : Fin 3 → ℝ) :
    ContinuousAt (fun z : Phase × (Fin 3 → ℝ) => tForm μ c z.1 z.2) (s, a) := by
  unfold tForm
  have h := fun i j => (continuousAt_tHess μ c hs i j).comp (x := (s, a)) continuousAt_fst
  simp only [Function.comp_def] at h
  simp only [Fin.sum_univ_three]
  fun_prop

theorem tForm_smul (μ c : ℝ) (x : Phase) (k : ℝ) (a : Fin 3 → ℝ) :
    tForm μ c x (k • a) = k ^ 2 * tForm μ c x a := by
  simp only [tForm, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

/-- Positive definiteness persists near a point of `U` (tube lemma over the sphere). -/
theorem eventually_quadPos (μ c : ℝ) {s : Phase} (hs : s ∈ U) (hQ : QuadPos (tHess μ c s)) :
    ∀ᶠ x in 𝓝 s, QuadPos (tHess μ c x) := by
  have hK : IsCompact (Metric.sphere (0 : Fin 3 → ℝ) 1) := isCompact_sphere 0 1
  have hev : ∀ᶠ x in 𝓝 s, ∀ a ∈ Metric.sphere (0 : Fin 3 → ℝ) 1, 0 < tForm μ c x a := by
    refine hK.eventually_forall_of_forall_eventually fun a ha => ?_
    have ha0 : a ≠ 0 := by
      rintro rfl; simp at ha
    exact (continuousAt_tForm_prod μ c hs a).eventually (lt_mem_nhds (hQ a ha0))
  filter_upwards [hev] with x hx
  intro a ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hmem : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : Fin 3 → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have h1 := hx _ hmem
  rw [tForm_smul] at h1
  have h2 : 0 < tForm μ c x a := by
    have : 0 < (‖a‖⁻¹) ^ 2 := by positivity
    exact (pos_iff_pos_of_mul_pos h1).mp this
  exact h2

theorem eventually_neg (μ c : ℝ) {s : Phase} (hs : s ∈ U) {a : Fin 3 → ℝ}
    (ha : tForm μ c s a < 0) : ∀ᶠ x in 𝓝 s, tForm μ c x a < 0 :=
  (continuousAt_tForm μ c hs a).eventually (gt_mem_nhds ha)

/-- Step 5: the tangential Hessian is positive definite on the whole left component. -/
theorem quadPos_tHess_of_det {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c)
    (hdet : ∀ s ∈ leftEnergyComponent μ c, 0 < (tHess μ c s).det) :
    ∀ s ∈ leftEnergyComponent μ c, QuadPos (tHess μ c s) := by
  have memU : ∀ {s}, s ∈ leftEnergyComponent μ c → s ∈ U := fun hs =>
    mem_U_of_two_zNormSq_le (by
      linarith [left_energy_component_barrier_ball μ c hμ0 hμhalf hc0 _ hs])
  set S := leftEnergyComponent μ c
  set u := interior {x | QuadPos (tHess μ c x)}
  set v := interior {x | ∃ a, tForm μ c x a < 0}
  have hsu : ∀ s ∈ S, QuadPos (tHess μ c s) → s ∈ u := fun s hs hQ =>
    mem_interior_iff_mem_nhds.mpr
      (eventually_quadPos μ c (memU hs) hQ)
  have hsv : ∀ s ∈ S, ¬ QuadPos (tHess μ c s) → s ∈ v := by
    intro s hs hQ
    obtain ⟨a, ha⟩ := exists_neg_of_not_quadPos (tHess_symm μ c s)
      (hdet s hs).ne' hQ
    exact mem_interior_iff_mem_nhds.mpr
      ((eventually_neg μ c (memU hs) ha).mono
        fun x hx => ⟨a, hx⟩)
  have hcover : S ⊆ u ∪ v := fun s hs => by
    by_cases hQ : QuadPos (tHess μ c s)
    · exact Or.inl (hsu s hs hQ)
    · exact Or.inr (hsv s hs hQ)
  have hs₀ := leftCollisionPoint_mem_of_le μ c (by linarith)
  have hu : (S ∩ u).Nonempty :=
    ⟨_, hs₀, hsu _ hs₀ (quadPos_tHess_leftCollisionPoint μ c hμ0 hμhalf hc0)⟩
  have huv : (S ∩ (u ∩ v)) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hxu hxv
    have hQ : QuadPos (tHess μ c x) := interior_subset hxu
    have hxv' : x ∈ {x | ∃ a, tForm μ c x a < 0} := interior_subset hxv
    obtain ⟨a, ha⟩ := hxv'
    by_cases ha0 : a = 0
    · subst ha0; simp [tForm] at ha
    · exact absurd (hQ a ha0) (not_lt.mpr ha.le)
  have hv : ¬ (S ∩ v).Nonempty := fun hne => by
    have := (show IsPreconnected S from isPreconnected_connectedComponentIn) u v isOpen_interior isOpen_interior
      hcover hu hne
    rw [huv] at this
    exact Set.not_nonempty_empty this
  intro s hs
  by_contra hQ
  exact hv ⟨s, hs, hsv s hs hQ⟩

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c)
    (hdet : ∀ s ∈ leftEnergyComponent μ c, 0 < (tHess μ c s).det) :
    ∀ s ∈ leftEnergyComponent μ c, QuadPos (tHess μ c s) := by
  exact quadPos_tHess_of_det hμ0 hμhalf hc0 hdet
