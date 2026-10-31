-- Prove2me | solution 1 for DisclosureStatics.Aggregation.demand_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:48:20.615086+00:00
-- url     : https://prove2.me/submissions/bbfa2e0a-dd45-44ff-b955-5ece3373cf42

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model
open DisclosureStatics.Aggregation

namespace DiscCore

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

set_option linter.unusedSectionVars false

lemma hasDerivAt_cara {γ : ℝ} (hγ : γ ≠ 0) (x d : ℝ) :
    HasDerivAt (fun t : ℝ => cara γ (x + t * d)) (Real.exp (-γ * x) * d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => -γ * (x + t * d)) (-γ * d) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).mul_const d).const_add x
    simpa using this.const_mul (-γ)
  have h2 := (h1.exp.const_sub 1).div_const γ
  unfold cara
  have e : -(Real.exp (-γ * (x + 0 * d)) * (-γ * d)) / γ = Real.exp (-γ * x) * d := by
    rw [zero_mul, add_zero]; field_simp
  exact h2.congr_deriv e

lemma cara_lt {γ : ℝ} (hγ : 0 < γ) (x : ℝ) : cara γ x < 1 / γ := by
  unfold cara
  have := Real.exp_pos (-γ * x)
  apply div_lt_div_of_pos_right _ hγ; linarith

lemma probE_pos (M : Market Ω) (hM : M.Standing) {S : Finset Ω} (hS : S.Nonempty) :
    0 < probE M S := Finset.sum_pos (fun i _ => hM.1 i) hS

lemma sum_weights (M : Market Ω) (hM : M.Standing) {S : Finset Ω} (hS : S.Nonempty) :
    ∑ i ∈ S, M.P i / probE M S = 1 := by
  rw [← Finset.sum_div]; exact div_self (probE_pos M hM hS).ne'

lemma V_lt (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {S : Finset Ω}
    (hS : S.Nonempty) (y : Ω → ℝ) : V M (cara γ) S y < 1 / γ := by
  unfold V
  calc ∑ i ∈ S, M.P i / probE M S * cara γ (y i) < ∑ i ∈ S, M.P i / probE M S * (1 / γ) := by
        apply Finset.sum_lt_sum_of_nonempty hS
        intro i _
        exact mul_lt_mul_of_pos_left (cara_lt hγ _) (div_pos (hM.1 i) (probE_pos M hM hS))
    _ = 1 / γ := by rw [← Finset.sum_mul, sum_weights M hM hS, one_mul]

lemma hasDerivAt_V (M : Market Ω) {γ : ℝ} (hγ : γ ≠ 0) (S : Finset Ω) (x d : Ω → ℝ) :
    HasDerivAt (fun t : ℝ => V M (cara γ) S (fun k => x k + t * d k))
      (∑ k ∈ S, M.P k / probE M S * (Real.exp (-γ * x k) * d k)) 0 := by
  unfold V
  apply HasDerivAt.fun_sum
  intro k _
  exact (hasDerivAt_cara hγ (x k) (d k)).const_mul _

lemma regular_diff {φ : ℝ → ℝ} {γ : ℝ} (hφ : Regular φ (Set.Iio (1 / γ))) {v : ℝ}
    (hv : v < 1 / γ) : HasDerivAt φ (deriv φ v) v := by
  have hd : DifferentiableOn ℝ φ (Set.Iio (1 / γ)) :=
    hφ.1.differentiableOn (by norm_num)
  exact (hd.differentiableAt (Iio_mem_nhds hv)).hasDerivAt

/-- Perturbation direction moving `1/pᵢ` into state `i` and out of state `j`. -/
noncomputable def dir (M : Market Ω) (i j : Ω) : Ω → ℝ :=
  fun k => (if k = i then 1 / M.p i else 0) - (if k = j then 1 / M.p j else 0)

lemma sum_mul_dir (M : Market Ω) (R : Finset Ω) (f : Ω → ℝ) (i j : Ω) :
    ∑ k ∈ R, f k * dir M i j k =
      (if i ∈ R then f i / M.p i else 0) - (if j ∈ R then f j / M.p j else 0) := by
  unfold dir
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    mul_one_div]

lemma foc_line (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ}
    (hφ : Regular φ (Set.Iio (1 / γ))) (Ps : Finset (Finset Ω))
    (hdisj : ∀ S ∈ Ps, ∀ T ∈ Ps, S ≠ T → Disjoint S T) (hne : ∀ S ∈ Ps, S.Nonempty)
    (x : Ω → ℝ) {S T : Finset Ω} (hS : S ∈ Ps) (hT : T ∈ Ps) {i j : Ω} (hi : i ∈ S) (hj : j ∈ T)
    (hmax : ∀ t : ℝ, ∑ R ∈ Ps, probE M R * φ (V M (cara γ) R (fun k => x k + t * dir M i j k))
      ≤ ∑ R ∈ Ps, probE M R * φ (V M (cara γ) R x)) :
    deriv φ (V M (cara γ) S x) * Real.exp (-γ * x i) * (M.P i / M.p i) =
      deriv φ (V M (cara γ) T x) * Real.exp (-γ * x j) * (M.P j / M.p j) := by
  set d := dir M i j
  have hx0 : (fun k => x k + (0:ℝ) * d k) = x := by funext k; simp
  have hD : HasDerivAt (fun t : ℝ => ∑ R ∈ Ps, probE M R *
      φ (V M (cara γ) R (fun k => x k + t * d k)))
      (∑ R ∈ Ps, probE M R * (deriv φ (V M (cara γ) R x) *
        ∑ k ∈ R, M.P k / probE M R * (Real.exp (-γ * x k) * d k))) 0 := by
    apply HasDerivAt.fun_sum
    intro R hR
    apply HasDerivAt.const_mul
    have h1 := hasDerivAt_V M hγ.ne' R x d
    have h2 := regular_diff hφ (V_lt M hM hγ (hne R hR) x)
    rw [← hx0] at h2
    have := h2.comp (0:ℝ) h1
    rw [hx0] at this
    exact this
  have hloc : IsLocalMax (fun t : ℝ => ∑ R ∈ Ps, probE M R *
      φ (V M (cara γ) R (fun k => x k + t * d k))) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [hx0]
    exact hmax t
  have h0 := hloc.hasDerivAt_eq_zero hD
  -- simplify the derivative
  have hterm : ∀ R ∈ Ps, probE M R * (deriv φ (V M (cara γ) R x) *
        ∑ k ∈ R, M.P k / probE M R * (Real.exp (-γ * x k) * d k)) =
      deriv φ (V M (cara γ) R x) *
        ((if i ∈ R then M.P i * Real.exp (-γ * x i) / M.p i else 0) -
         (if j ∈ R then M.P j * Real.exp (-γ * x j) / M.p j else 0)) := by
    intro R hR
    have hpR := (probE_pos M hM (hne R hR)).ne'
    have : ∑ k ∈ R, M.P k / probE M R * (Real.exp (-γ * x k) * d k) =
        (∑ k ∈ R, (M.P k * Real.exp (-γ * x k)) * d k) / probE M R := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro k _; field_simp
    rw [this, sum_mul_dir]
    field_simp
  rw [Finset.sum_congr rfl hterm] at h0
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero] at h0
  have hsel : ∀ (U : Finset Ω) (hU : U ∈ Ps) (a : Ω) (ha : a ∈ U) (g : Finset Ω → ℝ),
      ∑ R ∈ Ps, (if a ∈ R then g R else 0) = g U := by
    intro U hU a ha g
    rw [Finset.sum_eq_single_of_mem U hU]
    · simp [ha]
    · intro R hR hRU
      have := hdisj R hR U hU hRU
      have : a ∉ R := fun h => Finset.disjoint_left.1 this h ha
      simp [this]
  rw [hsel S hS i hi, hsel T hT j hj] at h0
  have : deriv φ (V M (cara γ) S x) * (M.P i * Real.exp (-γ * x i) / M.p i) =
      deriv φ (V M (cara γ) T x) * (M.P j * Real.exp (-γ * x j) / M.p j) := by linarith
  calc _ = deriv φ (V M (cara γ) S x) * (M.P i * Real.exp (-γ * x i) / M.p i) := by ring
    _ = _ := this
    _ = _ := by ring

lemma dir_p_sum (M : Market Ω) (hM : M.Standing) (R : Finset Ω) {i j : Ω} (hi : i ∈ R)
    (hj : j ∈ R) : ∑ k ∈ R, M.p k * dir M i j k = 0 := by
  rw [sum_mul_dir]; simp [hi, hj, div_self (hM.2.2.1 i).ne', div_self (hM.2.2.1 j).ne']

lemma dir_eq_zero (M : Market Ω) {i j k : Ω} (hi : k ≠ i) (hj : k ≠ j) : dir M i j k = 0 := by
  simp [dir, hi, hj]

lemma budget_line (M : Market Ω) (hM : M.Standing) {c : Ω → ℝ} (hc : Budget M c) {i j : Ω}
    (hi : i ≠ M.s₁) (hj : j ≠ M.s₁) (t : ℝ) :
    Budget M (fun k => c k + t * dir M i j k) := by
  unfold Budget at *
  have h1 : dir M i j M.s₁ = 0 := dir_eq_zero M (Ne.symm hi) (Ne.symm hj)
  have h2 := dir_p_sum M hM (Finset.univ.erase M.s₁) (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
  simp only [h1, mul_zero, add_zero]
  have : ∑ k ∈ Finset.univ.erase M.s₁, (M.l k - (c M.s₁ - (c k + t * dir M i j k))) * M.p k =
      ∑ k ∈ Finset.univ.erase M.s₁, (M.l k - (c M.s₁ - c k)) * M.p k +
        t * ∑ k ∈ Finset.univ.erase M.s₁, M.p k * dir M i j k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [this, h2, mul_zero, add_zero]; exact hc

lemma demand_pair (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ}
    (hφ : Regular φ (Set.Iio (1 / γ))) (π : PDS Ω) {c : Ω → ℝ}
    (hc : IsDemand M (cara γ) φ π c) {S T : Finset Ω} (hS : S ∈ π.parts) (hT : T ∈ π.parts)
    {i j : Ω} (hi : i ∈ S) (hj : j ∈ T) (hi1 : i ≠ M.s₁) (hj1 : j ≠ M.s₁) :
    deriv φ (V M (cara γ) S c) * Real.exp (-γ * c i) * (M.P i / M.p i) =
      deriv φ (V M (cara γ) T c) * Real.exp (-γ * c j) * (M.P j / M.p j) := by
  apply foc_line M hM hγ hφ π.parts _ (fun S hS => π.nonempty_of_mem_parts hS) c hS hT hi hj
  · intro t
    exact hc.2 _ (budget_line M hM hc.1 hi1 hj1 t)
  · intro S hS T hT hST
    exact π.disjoint hS hT hST

lemma inter_pair (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ}
    (hφ : Regular φ (Set.Iio (1 / γ))) {B : Finset Ω} {c cs : Ω → ℝ}
    (hcs : IsIntermediate M (cara γ) φ B c cs) {i j : Ω} (hi : i ∈ B) (hj : j ∈ B) :
    deriv φ (V M (cara γ) B cs) * Real.exp (-γ * cs i) * (M.P i / M.p i) =
      deriv φ (V M (cara γ) B cs) * Real.exp (-γ * cs j) * (M.P j / M.p j) := by
  apply foc_line M hM hγ hφ {B} (by simp) (by simp; exact ⟨i, hi⟩) cs
    (Finset.mem_singleton_self B) (Finset.mem_singleton_self B) hi hj
  intro t
  simp only [Finset.sum_singleton]
  apply hcs.2.2
  · intro k hk
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    have hkj : k ≠ j := fun h => hk (h ▸ hj)
    rw [dir_eq_zero M hki hkj, mul_zero, add_zero]; exact hcs.1 k hk
  · rw [← hcs.2.1]
    have h2 := dir_p_sum M hM B hi hj
    have : ∑ k ∈ B, M.p k * (cs k + t * dir M i j k) =
        ∑ k ∈ B, M.p k * cs k + t * ∑ k ∈ B, M.p k * dir M i j k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [this, h2, mul_zero, add_zero]

lemma budget_lhs (M : Market Ω) (hM : M.Standing) (y : Ω → ℝ) :
    y M.s₁ + ∑ k ∈ Finset.univ.erase M.s₁, (M.l k - (y M.s₁ - y k)) * M.p k =
      ∑ k, M.p k * y k + ∑ k ∈ Finset.univ.erase M.s₁, M.l k * M.p k := by
  have h1 : ∑ k ∈ Finset.univ.erase M.s₁, (M.l k - (y M.s₁ - y k)) * M.p k =
      ∑ k ∈ Finset.univ.erase M.s₁, M.l k * M.p k - y M.s₁ * ∑ k ∈ Finset.univ.erase M.s₁, M.p k
        + ∑ k ∈ Finset.univ.erase M.s₁, M.p k * y k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have h2 := Finset.add_sum_erase Finset.univ M.p (Finset.mem_univ M.s₁)
  have h3 := Finset.add_sum_erase Finset.univ (fun k => M.p k * y k) (Finset.mem_univ M.s₁)
  rw [hM.2.2.2] at h2
  rw [h1, ← h3]
  have : ∑ k ∈ Finset.univ.erase M.s₁, M.p k = 1 - M.p M.s₁ := by linarith
  rw [this]; ring

lemma budget_line' (M : Market Ω) (hM : M.Standing) {c : Ω → ℝ} (hc : Budget M c) (i j : Ω)
    (t : ℝ) : Budget M (fun k => c k + t * dir M i j k) := by
  unfold Budget at *
  rw [budget_lhs M hM] at hc
  rw [budget_lhs M hM (fun k => c k + t * dir M i j k)]
  have h2 := dir_p_sum M hM Finset.univ (Finset.mem_univ i) (Finset.mem_univ j)
  have : ∑ k, M.p k * (c k + t * dir M i j k) = ∑ k, M.p k * c k + t * ∑ k, M.p k * dir M i j k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [this, h2, mul_zero, add_zero]; exact hc

lemma demand_pair' (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ}
    (hφ : Regular φ (Set.Iio (1 / γ))) (π : PDS Ω) {c : Ω → ℝ}
    (hc : IsDemand M (cara γ) φ π c) {S T : Finset Ω} (hS : S ∈ π.parts) (hT : T ∈ π.parts)
    {i j : Ω} (hi : i ∈ S) (hj : j ∈ T) :
    deriv φ (V M (cara γ) S c) * Real.exp (-γ * c i) * (M.P i / M.p i) =
      deriv φ (V M (cara γ) T c) * Real.exp (-γ * c j) * (M.P j / M.p j) := by
  apply foc_line M hM hγ hφ π.parts _ (fun S hS => π.nonempty_of_mem_parts hS) c hS hT hi hj
  · intro t
    exact hc.2 _ (budget_line' M hM hc.1 i j t)
  · intro S hS T hT hST
    exact π.disjoint hS hT hST

lemma deriv_strictAnti {φ : ℝ → ℝ} {γ : ℝ} (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    StrictAntiOn (deriv φ) (Set.Iio (1 / γ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iio _)
  · exact hφ.1.1.continuousOn_deriv_of_isOpen isOpen_Iio (by norm_num)
  · intro x hx; rw [interior_Iio] at hx; exact hφ.2.1 x hx

/-- `G(v) = φ'(v) (1 - γ v)`. -/
lemma G_strictAnti {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ) (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    StrictAntiOn (fun v => deriv φ v * (1 - γ * v)) (Set.Iio (1 / γ)) := by
  intro v hv w hw hvw
  have hv' : v < 1 / γ := hv
  have hw' : w < 1 / γ := hw
  have h1 := deriv_strictAnti hφ hv hw hvw
  have h2 : 0 < deriv φ w := hφ.1.2 w hw
  have h3 : 0 < 1 - γ * w := by
    have : γ * w < γ * (1 / γ) := mul_lt_mul_of_pos_left hw' hγ
    rw [mul_one_div_cancel hγ.ne'] at this; linarith
  have h4 : 1 - γ * w < 1 - γ * v := by nlinarith
  simp only
  calc deriv φ w * (1 - γ * w) < deriv φ v * (1 - γ * w) := mul_lt_mul_of_pos_right h1 h3
    _ < deriv φ v * (1 - γ * v) := mul_lt_mul_of_pos_left h4 (h2.trans h1)

lemma G_eq (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ} {S : Finset Ω}
    (hS : S.Nonempty) (c : Ω → ℝ) (K : ℝ)
    (hd : 0 < deriv φ (V M (cara γ) S c))
    (hK : ∀ k ∈ S, deriv φ (V M (cara γ) S c) * Real.exp (-γ * c k) * (M.P k / M.p k) = K) :
    deriv φ (V M (cara γ) S c) * (1 - γ * V M (cara γ) S c) = K * rE M S := by
  set d := deriv φ (V M (cara γ) S c)
  have hPS := probE_pos M hM hS
  have he : ∀ k ∈ S, Real.exp (-γ * c k) = K * M.p k / (M.P k * d) := by
    intro k hk
    have := hK k hk
    have hP := hM.1 k; have hp := hM.2.2.1 k
    rw [← this]
    field_simp
  have hV : γ * V M (cara γ) S c = 1 - K * priceE M S / (probE M S * d) := by
    unfold V
    rw [Finset.mul_sum]
    have : ∀ k ∈ S, γ * (M.P k / probE M S * cara γ (c k)) =
        M.P k / probE M S - K * M.p k / (probE M S * d) := by
      intro k hk
      unfold cara
      rw [he k hk]
      have hP := hM.1 k
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, sum_weights M hM hS, priceE,
      Finset.mul_sum, Finset.sum_div]
  rw [hV, rE]
  field_simp
  ring

end DiscCore

namespace DiscCore

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma loss_eq (M : Market Ω) (hM : M.Standing) (x : Ω → ℝ) :
    Loss M x = ∑ k, (M.P k - M.p k) * x k := by
  unfold Loss
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ M.s₁)]
  have h2 := Finset.add_sum_erase Finset.univ M.p (Finset.mem_univ M.s₁)
  have h3 := Finset.add_sum_erase Finset.univ M.P (Finset.mem_univ M.s₁)
  rw [hM.2.2.2] at h2; rw [hM.2.1] at h3
  have : ∑ k ∈ Finset.univ.erase M.s₁, (x M.s₁ - x k) * (M.p k - M.P k) =
      x M.s₁ * (∑ k ∈ Finset.univ.erase M.s₁, M.p k - ∑ k ∈ Finset.univ.erase M.s₁, M.P k) +
      ∑ k ∈ Finset.univ.erase M.s₁, (M.P k - M.p k) * x k := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [this]
  have e1 : ∑ k ∈ Finset.univ.erase M.s₁, M.p k = 1 - M.p M.s₁ := by linarith
  have e2 : ∑ k ∈ Finset.univ.erase M.s₁, M.P k = 1 - M.P M.s₁ := by linarith
  rw [e1, e2]; ring

lemma priceE_pos (M : Market Ω) (hM : M.Standing) {S : Finset Ω} (hS : S.Nonempty) :
    0 < priceE M S := Finset.sum_pos (fun i _ => hM.2.2.1 i) hS

end DiscCore


namespace DiscCore

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma hasDerivAt_cara' {γ : ℝ} (hγ : γ ≠ 0) (x : ℝ) :
    HasDerivAt (cara γ) (Real.exp (-γ * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -γ * y) (-γ * 1) x := (hasDerivAt_id x).const_mul (-γ)
  have h2 := (h1.exp.const_sub 1).div_const γ
  have e : -(Real.exp (-γ * x) * (-γ * 1)) / γ = Real.exp (-γ * x) := by field_simp
  rw [e] at h2
  exact h2

lemma deriv_cara {γ : ℝ} (hγ : γ ≠ 0) (x : ℝ) : deriv (cara γ) x = Real.exp (-γ * x) :=
  (hasDerivAt_cara' hγ x).deriv

lemma cara_tangent {γ : ℝ} (hγ : 0 < γ) (x y : ℝ) :
    cara γ y ≤ cara γ x + Real.exp (-γ * x) * (y - x) := by
  unfold cara
  have h := Real.add_one_le_exp (-γ * (y - x))
  have e : Real.exp (-γ * y) = Real.exp (-γ * x) * Real.exp (-γ * (y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have hx := Real.exp_pos (-γ * x)
  have key : Real.exp (-γ * x) * (1 - γ * (y - x)) ≤ Real.exp (-γ * y) := by
    rw [e]; nlinarith
  rw [div_add' _ _ _ hγ.ne', div_le_div_iff_of_pos_right hγ]
  nlinarith

lemma phi_tangent {φ : ℝ → ℝ} {γ : ℝ} (hφ : AggregationAverse φ (Set.Iio (1 / γ))) {v w : ℝ}
    (hv : v < 1 / γ) (hw : w < 1 / γ) : φ w ≤ φ v + deriv φ v * (w - v) := by
  have hcont : ContinuousOn φ (Set.Iio (1 / γ)) := hφ.1.1.continuousOn
  have hdiff : DifferentiableOn ℝ φ (Set.Iio (1 / γ)) := hφ.1.1.differentiableOn (by norm_num)
  have hanti := deriv_strictAnti hφ
  rcases lt_trichotomy v w with h | h | h
  · obtain ⟨ξ, hξ, hξe⟩ := exists_deriv_eq_slope φ h
      (hcont.mono (fun z hz => lt_of_le_of_lt hz.2 hw))
      (hdiff.mono (fun z hz => lt_trans hz.2 hw))
    have h1 : deriv φ ξ < deriv φ v := hanti hv (lt_trans hξ.2 hw) hξ.1
    have h2 : φ w - φ v = deriv φ ξ * (w - v) := by
      rw [hξe]; field_simp [sub_ne_zero.2 h.ne']
    nlinarith
  · subst h; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_deriv_eq_slope φ h
      (hcont.mono (fun z hz => lt_of_le_of_lt hz.2 hv))
      (hdiff.mono (fun z hz => lt_trans hz.2 hv))
    have h1 : deriv φ v < deriv φ ξ := hanti (lt_trans hξ.2 hv) hv hξ.2
    have h2 : φ v - φ w = deriv φ ξ * (v - w) := by
      rw [hξe]; field_simp [sub_ne_zero.2 h.ne']
    nlinarith

/-- Linearization bound for the value of an event. -/
lemma V_tangent (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {S : Finset Ω}
    (hS : S.Nonempty) (x y : Ω → ℝ) :
    V M (cara γ) S y ≤ V M (cara γ) S x +
      (∑ k ∈ S, M.P k * Real.exp (-γ * x k) * (y k - x k)) / probE M S := by
  unfold V
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hw : 0 ≤ M.P k / probE M S := (div_pos (hM.1 k) (probE_pos M hM hS)).le
  have := mul_le_mul_of_nonneg_left (cara_tangent hγ (x k) (y k)) hw
  have hP := (probE_pos M hM hS).ne'
  calc M.P k / probE M S * cara γ (y k) ≤ M.P k / probE M S * (cara γ (x k) +
        Real.exp (-γ * x k) * (y k - x k)) := this
    _ = _ := by field_simp

end DiscCore


namespace DiscCore

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `ψ(y) = φ'((1-y)/γ) y`. -/
noncomputable def psi (φ : ℝ → ℝ) (γ : ℝ) (y : ℝ) : ℝ := deriv φ ((1 - y) / γ) * y

lemma v_lt {γ : ℝ} (hγ : 0 < γ) {y : ℝ} (hy : 0 < y) : (1 - y) / γ < 1 / γ :=
  div_lt_div_of_pos_right (by linarith) hγ

lemma hasDerivAt_dphi {φ : ℝ → ℝ} {γ : ℝ} (hφ : AggregationAverse φ (Set.Iio (1 / γ))) {v : ℝ}
    (hv : v < 1 / γ) : HasDerivAt (deriv φ) (deriv (deriv φ) v) v := by
  have h3 : ContDiffOn ℝ (2 + 1) φ (Set.Iio (1 / γ)) := hφ.1.1
  have h := ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio).1 h3).2.2
  have hd : DifferentiableOn ℝ (deriv φ) (Set.Iio (1 / γ)) := h.differentiableOn (by norm_num)
  exact (hd.differentiableAt (Iio_mem_nhds hv)).hasDerivAt

/-- `A(v) = -φ''(v)/φ'(v)`. -/
noncomputable def Aφ (φ : ℝ → ℝ) (v : ℝ) : ℝ := -deriv (deriv φ) v / deriv φ v

lemma A_pos {φ : ℝ → ℝ} {γ : ℝ} (hφ : AggregationAverse φ (Set.Iio (1 / γ))) {v : ℝ}
    (hv : v < 1 / γ) : 0 < Aφ φ v :=
  div_pos (neg_pos.2 (hφ.2.1 v hv)) (hφ.1.2 v hv)

/-- `ψ'(y) = φ'(v) (1 + y A(v)/γ)` with `v = (1-y)/γ`. -/
noncomputable def psi' (φ : ℝ → ℝ) (γ : ℝ) (y : ℝ) : ℝ :=
  deriv φ ((1 - y) / γ) * (1 + y * Aφ φ ((1 - y) / γ) / γ)

lemma hasDerivAt_psi {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (psi φ γ) (psi' φ γ y) y := by
  have hv := v_lt hγ hy
  have h1 : HasDerivAt (fun y : ℝ => (1 - y) / γ) (-1 / γ) y := by
    have := ((hasDerivAt_id y).const_sub 1).div_const γ
    simpa using this
  have h2 := (hasDerivAt_dphi hφ hv).comp y h1
  have h3 := h2.mul (hasDerivAt_id y)
  have hd := (hφ.1.2 _ hv).ne'
  rw [show psi φ γ = fun y => (deriv φ ∘ fun y : ℝ => (1 - y) / γ) y * id y from rfl]
  refine h3.congr_deriv ?_
  unfold psi' Aφ
  simp only [Function.comp, id]
  field_simp
  ring

lemma psi'_pos {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    {y : ℝ} (hy : 0 < y) : 0 < psi' φ γ y := by
  have hv := v_lt hγ hy
  unfold psi'
  have := A_pos hφ hv
  have := hφ.1.2 _ hv
  positivity

lemma psi_pos {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    {y : ℝ} (hy : 0 < y) : 0 < psi φ γ y := mul_pos (hφ.1.2 _ (v_lt hγ hy)) hy

lemma psi_cont {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ) (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    ContinuousOn (psi φ γ) (Set.Ioi 0) :=
  fun y hy => (hasDerivAt_psi hγ hφ hy).continuousAt.continuousWithinAt

lemma deriv_psi {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    {y : ℝ} (hy : 0 < y) : deriv (psi φ γ) y = psi' φ γ y := (hasDerivAt_psi hγ hφ hy).deriv

lemma psi_strictMono {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) : StrictMonoOn (psi φ γ) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (psi_cont hγ hφ)
  intro y hy; rw [interior_Ioi] at hy
  rw [deriv_psi hγ hφ hy]; exact psi'_pos hγ hφ hy

lemma psi_convex {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) : ConvexOn ℝ (Set.Ioi 0) (psi φ γ) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0) (psi_cont hγ hφ)
  · rw [interior_Ioi]; exact fun y hy => (hasDerivAt_psi hγ hφ hy).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro y1 hy1 y2 hy2 h12
    have hy1' : 0 < y1 := hy1
    have hy2' : 0 < y2 := hy2
    rw [deriv_psi hγ hφ hy1', deriv_psi hγ hφ hy2']
    unfold psi'
    have hv1 := v_lt hγ hy1'
    have hv2 := v_lt hγ hy2'
    have hvv : (1 - y2) / γ ≤ (1 - y1) / γ := div_le_div_of_nonneg_right (by linarith) hγ.le
    have hd : deriv φ ((1 - y1) / γ) ≤ deriv φ ((1 - y2) / γ) :=
      (deriv_strictAnti hφ).antitoneOn hv2 hv1 hvv
    have hA : Aφ φ ((1 - y1) / γ) ≤ Aφ φ ((1 - y2) / γ) := hφ.2.2 hv2 hv1 hvv
    have hA1 := A_pos hφ hv1
    have hd1 := hφ.1.2 _ hv1
    apply mul_le_mul hd _ (by positivity) (hd1.le.trans hd)
    have : y1 * Aφ φ ((1 - y1) / γ) ≤ y2 * Aφ φ ((1 - y2) / γ) :=
      mul_le_mul h12 hA hA1.le hy2'.le
    have := div_le_div_of_nonneg_right this hγ.le
    linarith

/-- `M(z) = log ψ(e^z)`. -/
noncomputable def Mf (φ : ℝ → ℝ) (γ : ℝ) (z : ℝ) : ℝ := Real.log (psi φ γ (Real.exp z))

lemma hasDerivAt_Mf {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) (z : ℝ) :
    HasDerivAt (Mf φ γ) (1 + Real.exp z * Aφ φ ((1 - Real.exp z) / γ) / γ) z := by
  have hy := Real.exp_pos z
  have h1 := (hasDerivAt_psi hγ hφ hy).comp z (Real.hasDerivAt_exp z)
  have hp := psi_pos hγ hφ hy
  have h2 := h1.log hp.ne'
  rw [show Mf φ γ = fun z => Real.log ((psi φ γ ∘ Real.exp) z) from rfl]
  refine h2.congr_deriv ?_
  simp only [Function.comp]
  unfold psi psi' Aφ
  have hd := (hφ.1.2 _ (v_lt hγ hy)).ne'
  field_simp

lemma Mf_strictConvex {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) : StrictConvexOn ℝ Set.univ (Mf φ γ) := by
  apply StrictMonoOn.strictConvexOn_of_deriv convex_univ
  · exact fun z _ => (hasDerivAt_Mf hγ hφ z).continuousAt.continuousWithinAt
  · intro z1 _ z2 _ h12
    rw [(hasDerivAt_Mf hγ hφ z1).deriv, (hasDerivAt_Mf hγ hφ z2).deriv]
    have he := Real.exp_lt_exp.2 h12
    have hy1 := Real.exp_pos z1
    have hv1 := v_lt hγ hy1
    have hv2 := v_lt hγ (Real.exp_pos z2)
    have hvv : (1 - Real.exp z2) / γ ≤ (1 - Real.exp z1) / γ :=
      div_le_div_of_nonneg_right (by linarith) hγ.le
    have hA : Aφ φ ((1 - Real.exp z1) / γ) ≤ Aφ φ ((1 - Real.exp z2) / γ) := hφ.2.2 hv2 hv1 hvv
    have hA1 := A_pos hφ hv1
    have : Real.exp z1 * Aφ φ ((1 - Real.exp z1) / γ) < Real.exp z2 * Aφ φ ((1 - Real.exp z2) / γ) :=
      calc _ < Real.exp z2 * Aφ φ ((1 - Real.exp z1) / γ) := mul_lt_mul_of_pos_right he hA1
        _ ≤ _ := mul_le_mul_of_nonneg_left hA (Real.exp_pos z2).le
    have := div_lt_div_of_pos_right this hγ
    linarith

end DiscCore

namespace DiscCore

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma ev_facts (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ}
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) {S : Finset Ω} (hS : S.Nonempty) (x : Ω → ℝ)
    (lam : ℝ) (hfoc : ∀ i ∈ S, deriv φ (V M (cara γ) S x) * deriv (cara γ) (x i) =
      lam * (M.p i / M.P i)) :
    0 < 1 - γ * V M (cara γ) S x ∧
    psi φ γ (1 - γ * V M (cara γ) S x) = lam * rE M S ∧
    ∀ i ∈ S, -γ * x i = Real.log ((1 - γ * V M (cara γ) S x) / rE M S) +
      Real.log (M.p i / M.P i) := by
  have hV := V_lt M hM hγ hS x
  have hY : 0 < 1 - γ * V M (cara γ) S x := by
    have : γ * V M (cara γ) S x < γ * (1 / γ) := mul_lt_mul_of_pos_left hV hγ
    rw [mul_one_div_cancel hγ.ne'] at this; linarith
  have hd := hφ.1.2 _ hV
  have hdc := deriv_cara hγ.ne'
  have hG := G_eq M hM hγ hS x lam hd (fun k hk => by
    have h := hfoc k hk
    rw [hdc] at h
    rw [h]; have := (hM.1 k).ne'; have := (hM.2.2.1 k).ne'; field_simp)
  have hvY : (1 - (1 - γ * V M (cara γ) S x)) / γ = V M (cara γ) S x := by
    field_simp; ring
  have hr : 0 < rE M S := div_pos (Finset.sum_pos (fun i _ => hM.2.2.1 i) hS)
    (probE_pos M hM hS)
  refine ⟨hY, ?_, ?_⟩
  · unfold psi; rw [hvY]; exact hG
  · intro i hi
    have h := hfoc i hi
    rw [hdc] at h
    have hpP : 0 < M.p i / M.P i := div_pos (hM.2.2.1 i) (hM.1 i)
    have he : Real.exp (-γ * x i) = ((1 - γ * V M (cara γ) S x) / rE M S) * (M.p i / M.P i) := by
      have hlam : lam = deriv φ (V M (cara γ) S x) * (1 - γ * V M (cara γ) S x) / rE M S := by
        rw [hG]; field_simp
      rw [hlam] at h
      have hd' := hd.ne'
      field_simp at h ⊢
      linarith
    rw [← Real.log_mul (div_pos hY hr).ne' hpP.ne', ← he, Real.log_exp]

lemma s1_notin_B (M : Market Ω) (π : PDS Ω) (hπ : IsPDS M π) {𝒮 : Finset (Finset Ω)}
    {B : Finset Ω} (hB : IsMergedEvent M π 𝒮 B) : M.s₁ ∉ B := by
  obtain ⟨h𝒮, -, hs1, hBdef⟩ := hB
  intro h
  rw [hBdef, Finset.mem_sup] at h
  obtain ⟨S, hS, hsS⟩ := h
  have := π.eq_of_mem_parts (h𝒮 hS) hπ hsS (Finset.mem_singleton_self _)
  exact hs1 (this ▸ hS)

lemma lemma3_core (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct)
    (lπ lB lρ : ℝ) (hlπ : IsFOC M (cara γ) φ π c lπ) (hlB : IsFOCB M (cara γ) φ B cs lB)
    (hlρ : IsFOC M (cara γ) φ ρ ct lρ) :
    lB < lρ ∧ lρ < lπ ∧ (∀ i ∈ B, ct i - cs i < 0) ∧ (∀ j ∉ B, 0 < ct j - cs j) := by
  have hs1B := s1_notin_B M π hπ hagg.1
  obtain ⟨⟨h𝒮, hcard, hs1, hBdef⟩, hρ⟩ := hagg
  have hdisj : (𝒮 : Set (Finset Ω)).PairwiseDisjoint id := π.disjoint.subset h𝒮
  have hBU : B = 𝒮.biUnion id := by rw [hBdef, Finset.sup_eq_biUnion]
  have hne : ∀ S ∈ 𝒮, S.Nonempty := fun S hS => π.nonempty_of_mem_parts (h𝒮 hS)
  have hsplit : ∀ f : Ω → ℝ, ∑ k ∈ B, f k = ∑ S ∈ 𝒮, ∑ k ∈ S, f k := by
    intro f; rw [hBU, Finset.sum_biUnion hdisj]; rfl
  have hmemB : ∀ S ∈ 𝒮, ∀ k ∈ S, k ∈ B := by
    intro S hS k hk; rw [hBU]; exact Finset.mem_biUnion.2 ⟨S, hS, hk⟩
  obtain ⟨S₀, hS₀, S₀', hS₀', hne0⟩ := hhet
  have hBne : B.Nonempty := by
    obtain ⟨k, hk⟩ := hne S₀ hS₀; exact ⟨k, hmemB S₀ hS₀ k hk⟩
  have hr : ∀ S : Finset Ω, S.Nonempty → 0 < rE M S := fun S hS =>
    div_pos (Finset.sum_pos (fun i _ => hM.2.2.1 i) hS) (probE_pos M hM hS)
  have hpsi := psi_strictMono hγ hφ
  -- off-B events of ρ
  have hoffparts : ∀ S ∈ ρ.parts, S ≠ B → S ∈ π.parts ∧ S ∉ 𝒮 := by
    intro S hS hSB
    rw [hρ] at hS
    rcases Finset.mem_insert.1 hS with h | h
    · exact absurd h hSB
    · exact Finset.mem_sdiff.1 h
  have hoffB : ∀ S ∈ π.parts, S ∉ 𝒮 → ∀ k ∈ S, k ∉ B := by
    intro S hSπ hS𝒮 k hk hkB
    rw [hBdef, Finset.mem_sup] at hkB
    obtain ⟨S', hS', hkS'⟩ := hkB
    have := π.eq_of_mem_parts (h𝒮 hS') hSπ hkS' hk
    exact hS𝒮 (this ▸ hS')
  -- event facts
  have evc : ∀ S ∈ π.parts, _ := fun S hS =>
    ev_facts M hM hγ hφ (π.nonempty_of_mem_parts hS) c lπ (hlπ S hS)
  have evt : ∀ S ∈ ρ.parts, _ := fun S hS =>
    ev_facts M hM hγ hφ (ρ.nonempty_of_mem_parts hS) ct lρ (hlρ S hS)
  have evB := ev_facts M hM hγ hφ hBne cs lB hlB
  have hVcs : ∀ S ∈ π.parts, S ∉ 𝒮 → V M (cara γ) S cs = V M (cara γ) S c := by
    intro S hSπ hS𝒮
    unfold V; apply Finset.sum_congr rfl; intro k hk
    rw [hcs.1 k (hoffB S hSπ hS𝒮 k hk)]
  have evoff : ∀ S ∈ π.parts, S ∉ 𝒮 → _ := fun S hSπ hS𝒮 =>
    ev_facts M hM hγ hφ (π.nonempty_of_mem_parts hSπ) cs lπ (fun i hi => by
      rw [hVcs S hSπ hS𝒮, hcs.1 i (hoffB S hSπ hS𝒮 i hi)]; exact hlπ S hSπ i hi)
  -- Step 1 : lB < lπ
  set Yc : Finset Ω → ℝ := fun S => 1 - γ * V M (cara γ) S c
  set Ys : Finset Ω → ℝ := fun S => 1 - γ * V M (cara γ) S cs
  set Yt : Finset Ω → ℝ := fun S => 1 - γ * V M (cara γ) S ct
  have hlπpos : 0 < lπ := by
    have h := (evc {M.s₁} hπ).2.1
    have := psi_pos hγ hφ (evc {M.s₁} hπ).1
    have := hr {M.s₁} (Finset.singleton_nonempty _)
    by_contra hneg; push Not at hneg
    have : lπ * rE M {M.s₁} ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    linarith
  have step1 : lB < lπ := by
    set X : Finset Ω → ℝ := fun S => Yc S / rE M S
    set XB := Ys B / rE M B
    have hXpos : ∀ S ∈ 𝒮, 0 < X S := fun S hS =>
      div_pos (evc S (h𝒮 hS)).1 (hr S (hne S hS))
    have hXB : 0 < XB := div_pos evB.1 (hr B hBne)
    -- expenditure identity
    have hdiff : ∀ S ∈ 𝒮, ∀ i ∈ S, γ * (cs i - c i) = Real.log (X S) - Real.log XB := by
      intro S hS i hi
      have h1 := (evc S (h𝒮 hS)).2.2 i hi
      have h2 := evB.2.2 i (hmemB S hS i hi)
      simp only [X, XB, Yc, Ys]; linarith
    have hpS : ∀ S ∈ 𝒮, 0 < priceE M S := fun S hS => priceE_pos M hM (hne S hS)
    have hpB : priceE M B = ∑ S ∈ 𝒮, priceE M S := by unfold priceE; rw [hsplit]
    have hPB : probE M B = ∑ S ∈ 𝒮, probE M S := by unfold probE; rw [hsplit]
    have hpBpos : 0 < priceE M B := priceE_pos M hM hBne
    have hPBpos : 0 < probE M B := probE_pos M hM hBne
    have hsum0 : ∑ S ∈ 𝒮, priceE M S * (Real.log (X S) - Real.log XB) = 0 := by
      have h0 : ∑ k ∈ B, M.p k * (γ * (cs k - c k)) = 0 := by
        have : ∑ k ∈ B, M.p k * (γ * (cs k - c k)) =
            γ * (∑ k ∈ B, M.p k * cs k - ∑ k ∈ B, M.p k * c k) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [this, hcs.2.1, sub_self, mul_zero]
      rw [← h0, hsplit]; apply Finset.sum_congr rfl; intro S hS
      unfold priceE; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k hk
      rw [hdiff S hS k hk]
    set w : Finset Ω → ℝ := fun S => priceE M S / priceE M B
    have hw1 : ∑ S ∈ 𝒮, w S = 1 := by
      simp only [w]; rw [← Finset.sum_div, ← hpB, div_self hpBpos.ne']
    have hwpos : ∀ S ∈ 𝒮, 0 < w S := fun S hS => div_pos (hpS S hS) hpBpos
    have hlogXB : Real.log XB = ∑ S ∈ 𝒮, w S • Real.log (X S) := by
      have : ∑ S ∈ 𝒮, priceE M S * Real.log (X S) = priceE M B * Real.log XB := by
        have := hsum0
        rw [Finset.sum_congr rfl (fun S _ => mul_sub (priceE M S) _ _), Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← hpB] at this
        linarith
      simp only [w, smul_eq_mul]
      rw [show ∑ S ∈ 𝒮, priceE M S / priceE M B * Real.log (X S) =
        (∑ S ∈ 𝒮, priceE M S * Real.log (X S)) / priceE M B by
          rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro S _; ring, this]
      field_simp
    -- heterogeneity of the X
    have hXne : ∃ S ∈ 𝒮, ∃ T ∈ 𝒮, X S ≠ X T := by
      refine ⟨S₀, hS₀, S₀', hS₀', fun hX => hne0 ?_⟩
      have hS := evc S₀ (h𝒮 hS₀); have hT := evc S₀' (h𝒮 hS₀')
      have hrS := hr S₀ (hne S₀ hS₀); have hrT := hr S₀' (hne S₀' hS₀')
      -- lπ = φ'(V) X
      have k1 : lπ = deriv φ ((1 - Yc S₀) / γ) * X S₀ := by
        have := hS.2.1; unfold psi at this
        simp only [X, Yc] at *; field_simp; linarith
      have k2 : lπ = deriv φ ((1 - Yc S₀') / γ) * X S₀' := by
        have := hT.2.1; unfold psi at this
        simp only [X, Yc] at *; field_simp; linarith
      have hXS := hXpos S₀ hS₀
      have hd : deriv φ ((1 - Yc S₀) / γ) = deriv φ ((1 - Yc S₀') / γ) := by
        rw [hX] at k1
        have := k1.symm.trans k2
        exact mul_right_cancel₀ (hX ▸ hXS).ne' this
      have hv := (deriv_strictAnti hφ).injOn (v_lt hγ hS.1) (v_lt hγ hT.1) hd
      have hY : Yc S₀ = Yc S₀' := by
        field_simp at hv; linarith
      have := hS.2.1; have h2 := hT.2.1
      simp only [Yc] at hY
      rw [hY] at this
      have := this.symm.trans h2
      exact mul_left_cancel₀ hlπpos.ne' this
    have hjen := strictConcaveOn_log_Ioi.lt_map_sum hwpos hw1 (fun S hS => hXpos S hS) hXne
    rw [← hlogXB] at hjen
    have hsumpos : 0 < ∑ S ∈ 𝒮, w S • X S :=
      Finset.sum_pos (fun S hS => by simp only [smul_eq_mul]; exact mul_pos (hwpos S hS) (hXpos S hS))
        ⟨S₀, hS₀⟩
    have hXlt : XB < ∑ S ∈ 𝒮, w S • X S := (Real.log_lt_log_iff hXB hsumpos).1 hjen
    -- Jensen for ψ
    set α : Finset Ω → ℝ := fun S => probE M S / probE M B
    have hα1 : ∑ S ∈ 𝒮, α S = 1 := by
      simp only [α]; rw [← Finset.sum_div, ← hPB, div_self hPBpos.ne']
    have hαnn : ∀ S ∈ 𝒮, 0 ≤ α S := fun S hS => (div_pos (probE_pos M hM (hne S hS)) hPBpos).le
    have hJ := (psi_convex hγ hφ).map_sum_le hαnn hα1 (fun S hS => (evc S (h𝒮 hS)).1)
    have hmid : ∑ S ∈ 𝒮, α S • Yc S = rE M B * ∑ S ∈ 𝒮, w S • X S := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S hS
      simp only [α, w, X, smul_eq_mul, rE]
      have := probE_pos M hM (hne S hS); have := priceE_pos M hM (hne S hS)
      field_simp
    have hright : ∑ S ∈ 𝒮, α S • psi φ γ (Yc S) = lπ * rE M B := by
      rw [Finset.sum_congr rfl (fun S hS => by rw [(evc S (h𝒮 hS)).2.1])]
      simp only [α, smul_eq_mul, rE]
      rw [show ∑ S ∈ 𝒮, probE M S / probE M B * (lπ * (priceE M S / probE M S)) =
          lπ * (∑ S ∈ 𝒮, priceE M S) / probE M B by
        rw [Finset.mul_sum, Finset.sum_div]; apply Finset.sum_congr rfl; intro S hS
        have := probE_pos M hM (hne S hS); field_simp, ← hpB]
      field_simp
    have hYB : Ys B < ∑ S ∈ 𝒮, α S • Yc S := by
      rw [hmid]
      have := mul_lt_mul_of_pos_left hXlt (hr B hBne)
      simp only [XB] at this
      rwa [mul_div_cancel₀ _ (hr B hBne).ne'] at this
    have hmidpos : (∑ S ∈ 𝒮, α S • Yc S) ∈ Set.Ioi 0 := lt_trans evB.1 hYB
    have := hpsi evB.1 hmidpos hYB
    rw [evB.2.1] at this
    have := lt_of_lt_of_le this (hJ.trans_eq hright)
    exact lt_of_mul_lt_mul_right this (hr B hBne).le
  -- Step 2 : budget comparison across ρ
  have hΔ : ∀ S ∈ ρ.parts, ∀ i ∈ S, γ * (ct i - cs i) = Real.log (Ys S) - Real.log (Yt S) := by
    intro S hS i hi
    have h1 := (evt S hS).2.2 i hi
    have hYt := (evt S hS).1
    have hrS := hr S (ρ.nonempty_of_mem_parts hS)
    by_cases hSB : S = B
    · subst hSB
      have h2 := evB.2.2 i hi
      rw [Real.log_div hYt.ne' hrS.ne'] at h1
      rw [Real.log_div evB.1.ne' hrS.ne'] at h2
      simp only [Ys, Yt]; linarith
    · obtain ⟨hSπ, hS𝒮⟩ := hoffparts S hS hSB
      have h2 := (evoff S hSπ hS𝒮).2.2 i hi
      rw [Real.log_div hYt.ne' hrS.ne'] at h1
      rw [Real.log_div (evoff S hSπ hS𝒮).1.ne' hrS.ne'] at h2
      simp only [Ys, Yt]; linarith
  have hbud : ∑ S ∈ ρ.parts, priceE M S * (Real.log (Ys S) - Real.log (Yt S)) = 0 := by
    have hct1 := hct.1; have hc1 := hc.1
    unfold Budget at hct1 hc1
    rw [budget_lhs M hM] at hct1 hc1
    have hcs_sum : ∑ k, M.p k * cs k = ∑ k, M.p k * c k := by
      rw [← Finset.sum_add_sum_compl B, ← Finset.sum_add_sum_compl B (fun k => M.p k * c k),
        hcs.2.1]
      congr 1; apply Finset.sum_congr rfl; intro k hk
      rw [hcs.1 k (Finset.mem_compl.1 hk)]
    have h0 : ∑ k, M.p k * (γ * (ct k - cs k)) = 0 := by
      have : ∑ k, M.p k * (γ * (ct k - cs k)) = γ * (∑ k, M.p k * ct k - ∑ k, M.p k * cs k) := by
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [this, hcs_sum]; have : ∑ k, M.p k * ct k = ∑ k, M.p k * c k := by linarith
      rw [this, sub_self, mul_zero]
    have e := Finset.sum_biUnion (f := fun k => M.p k * (γ * (ct k - cs k))) ρ.disjoint
    rw [ρ.biUnion_parts] at e
    rw [← h0, e]
    apply Finset.sum_congr rfl; intro S hS
    unfold priceE; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k hk
    rw [hΔ S hS k hk]
  -- comparison of multipliers
  have hpsiYs : ∀ S ∈ ρ.parts, S ≠ B → psi φ γ (Ys S) = lπ * rE M S := by
    intro S hS hSB; obtain ⟨hSπ, hS𝒮⟩ := hoffparts S hS hSB
    exact (evoff S hSπ hS𝒮).2.1
  have hYspos : ∀ S ∈ ρ.parts, 0 < Ys S := by
    intro S hS; by_cases hSB : S = B
    · subst hSB; exact evB.1
    · obtain ⟨hSπ, hS𝒮⟩ := hoffparts S hS hSB; exact (evoff S hSπ hS𝒮).1
  have hBρ : B ∈ ρ.parts := by rw [hρ]; exact Finset.mem_insert_self _ _
  have hs1ρ : {M.s₁} ∈ ρ.parts := by
    rw [hρ]; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hπ, hs1⟩)
  have hs1neB : ({M.s₁} : Finset Ω) ≠ B := by
    intro h; exact hs1B (h ▸ Finset.mem_singleton_self _)
  -- term at an event: sign of log Ys - log Yt from the multipliers
  have term_off : ∀ S ∈ ρ.parts, S ≠ B →
      (lρ < lπ → 0 < Real.log (Ys S) - Real.log (Yt S)) ∧
      (lπ ≤ lρ → Real.log (Ys S) - Real.log (Yt S) ≤ 0) := by
    intro S hS hSB
    have hrS := hr S (ρ.nonempty_of_mem_parts hS)
    have e1 := hpsiYs S hS hSB; have e2 := (evt S hS).2.1
    have p1 := hYspos S hS; have p2 := (evt S hS).1
    constructor
    · intro h
      have : psi φ γ (Yt S) < psi φ γ (Ys S) := by
        rw [e1]; simp only [Yt]; rw [e2]; exact mul_lt_mul_of_pos_right h hrS
      have := (hpsi.lt_iff_lt p2 p1).1 this
      have := Real.log_lt_log p2 this; linarith
    · intro h
      have : psi φ γ (Ys S) ≤ psi φ γ (Yt S) := by
        rw [e1]; simp only [Yt]; rw [e2]; exact mul_le_mul_of_nonneg_right h hrS.le
      have := (hpsi.le_iff_le p1 p2).1 this
      have := Real.log_le_log p1 this; linarith
  have hrB := hr B hBne
  have hsplitρ : ∑ S ∈ ρ.parts, priceE M S * (Real.log (Ys S) - Real.log (Yt S)) =
      priceE M B * (Real.log (Ys B) - Real.log (Yt B)) +
      ∑ S ∈ ρ.parts.erase B, priceE M S * (Real.log (Ys S) - Real.log (Yt S)) :=
    (Finset.add_sum_erase _ _ hBρ).symm
  have step2 : lρ < lπ := by
    by_contra hcon; push Not at hcon
    have hB : Real.log (Ys B) - Real.log (Yt B) < 0 := by
      have : psi φ γ (Ys B) < psi φ γ (Yt B) := by
        rw [evB.2.1]; simp only [Yt]; rw [(evt B hBρ).2.1]
        exact mul_lt_mul_of_pos_right (lt_of_lt_of_le step1 hcon) hrB
      have := (hpsi.lt_iff_lt evB.1 (evt B hBρ).1).1 this
      have := Real.log_lt_log evB.1 this; linarith
    have hrest : ∑ S ∈ ρ.parts.erase B, priceE M S * (Real.log (Ys S) - Real.log (Yt S)) ≤ 0 :=
      Finset.sum_nonpos (fun S hS => by
        obtain ⟨hSB, hS'⟩ := Finset.mem_erase.1 hS
        exact mul_nonpos_of_nonneg_of_nonpos (priceE_pos M hM (ρ.nonempty_of_mem_parts hS')).le
          ((term_off S hS' hSB).2 hcon))
    have := mul_neg_of_pos_of_neg (priceE_pos M hM hBne) hB
    linarith
  have hrest : 0 < ∑ S ∈ ρ.parts.erase B, priceE M S * (Real.log (Ys S) - Real.log (Yt S)) := by
    apply Finset.sum_pos'
    · intro S hS
      obtain ⟨hSB, hS'⟩ := Finset.mem_erase.1 hS
      exact (mul_pos (priceE_pos M hM (ρ.nonempty_of_mem_parts hS'))
        ((term_off S hS' hSB).1 step2)).le
    · exact ⟨{M.s₁}, Finset.mem_erase.2 ⟨hs1neB, hs1ρ⟩, mul_pos
        (priceE_pos M hM (Finset.singleton_nonempty _)) ((term_off _ hs1ρ hs1neB).1 step2)⟩
  have hBneg : Real.log (Ys B) - Real.log (Yt B) < 0 := by
    have h := hbud; rw [hsplitρ] at h
    by_contra hcon; push Not at hcon
    have := mul_nonneg (priceE_pos M hM hBne).le hcon
    linarith
  have hYBlt : Ys B < Yt B := by
    by_contra hcon; push Not at hcon
    have := Real.log_le_log (evt B hBρ).1 hcon; linarith
  refine ⟨?_, step2, ?_, ?_⟩
  · have := hpsi evB.1 (evt B hBρ).1 hYBlt
    rw [evB.2.1, (evt B hBρ).2.1] at this
    exact lt_of_mul_lt_mul_right this hrB.le
  · intro i hi
    have := hΔ B hBρ i hi
    have : γ * (ct i - cs i) < 0 := by linarith
    by_contra hcon; push Not at hcon
    have := mul_nonneg hγ.le hcon; linarith
  · intro j hj
    obtain ⟨S, hS, hjS⟩ := ρ.exists_mem (Finset.mem_univ j)
    have hSB : S ≠ B := fun h => hj (h ▸ hjS)
    have := hΔ S hS j hjS
    have h2 := (term_off S hS hSB).1 step2
    have : 0 < γ * (ct j - cs j) := by linarith
    by_contra hcon; push Not at hcon
    have := mul_nonpos_of_nonneg_of_nonpos hγ.le hcon; linarith

end DiscCore
theorem DiscCore.foc_char {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    (∀ π : PDS Ω, IsPDS M π → ∀ c : Ω → ℝ,
      (IsDemand M (cara γ) φ π c ↔
        Budget M c ∧ ∃ lam : ℝ, 0 < lam ∧ IsFOC M (cara γ) φ π c lam)) ∧
    (∀ B : Finset Ω, B.Nonempty → M.s₁ ∉ B → ∀ c cs : Ω → ℝ,
      (IsIntermediate M (cara γ) φ B c cs ↔
        (∀ i ∉ B, cs i = c i) ∧ ∑ i ∈ B, M.p i * cs i = ∑ i ∈ B, M.p i * c i ∧
          ∃ lam : ℝ, 0 < lam ∧ IsFOCB M (cara γ) φ B cs lam)) := by
  have hdc := deriv_cara hγ.ne'
  constructor
  · intro π hπ c
    constructor
    · intro hc
      refine ⟨hc.1, ?_⟩
      set K := deriv φ (V M (cara γ) {M.s₁} c) * Real.exp (-γ * c M.s₁) *
        (M.P M.s₁ / M.p M.s₁)
      have hK : 0 < K := by
        have := hφ.1.2 _ (V_lt M hM hγ (Finset.singleton_nonempty M.s₁) c)
        have := Real.exp_pos (-γ * c M.s₁)
        have := div_pos (hM.1 M.s₁) (hM.2.2.1 M.s₁)
        positivity
      refine ⟨K, hK, fun S hS i hi => ?_⟩
      have h := demand_pair' M hM hγ hφ.1 π hc hS hπ hi (Finset.mem_singleton_self _)
      rw [hdc]
      have hP := (hM.1 i).ne'; have hp := (hM.2.2.1 i).ne'
      calc _ = (deriv φ (V M (cara γ) S c) * Real.exp (-γ * c i) * (M.P i / M.p i)) *
            (M.p i / M.P i) := by field_simp
        _ = K * (M.p i / M.P i) := by rw [h]
    · rintro ⟨hb, lam, hlam, hfoc⟩
      refine ⟨hb, fun y hy => ?_⟩
      have step : ∀ S ∈ π.parts, probE M S * φ (V M (cara γ) S y) ≤
          probE M S * φ (V M (cara γ) S c) + lam * ∑ k ∈ S, M.p k * (y k - c k) := by
        intro S hS
        have hSne := π.nonempty_of_mem_parts hS
        have hPS := probE_pos M hM hSne
        have hd := hφ.1.2 _ (V_lt M hM hγ hSne c)
        have t1 := phi_tangent hφ (V_lt M hM hγ hSne c) (V_lt M hM hγ hSne y)
        have t2 := V_tangent M hM hγ hSne c y
        have e : ∑ k ∈ S, M.P k * Real.exp (-γ * c k) * (y k - c k) =
            (lam / deriv φ (V M (cara γ) S c)) * ∑ k ∈ S, M.p k * (y k - c k) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
          have hf := hfoc S hS k hk
          rw [hdc] at hf
          have hPk := (hM.1 k).ne'
          have he : Real.exp (-γ * c k) =
              lam * (M.p k / M.P k) / deriv φ (V M (cara γ) S c) := by
            rw [← hf]; field_simp
          rw [he]; field_simp
        rw [e] at t2
        set SS := ∑ k ∈ S, M.p k * (y k - c k)
        have t3 : deriv φ (V M (cara γ) S c) * (V M (cara γ) S y - V M (cara γ) S c) ≤
            lam * SS / probE M S := by
          have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.2 t2) hd.le
          calc _ ≤ deriv φ (V M (cara γ) S c) *
                (lam / deriv φ (V M (cara γ) S c) * SS / probE M S) := this
            _ = lam * SS / probE M S := by field_simp
        have t4 : φ (V M (cara γ) S y) ≤ φ (V M (cara γ) S c) + lam * SS / probE M S := by
          linarith
        have t5 := mul_le_mul_of_nonneg_left t4 hPS.le
        calc _ ≤ probE M S * (φ (V M (cara γ) S c) + lam * SS / probE M S) := t5
          _ = _ := by field_simp
      have hsum := Finset.sum_le_sum step
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
      have hpart : ∑ S ∈ π.parts, ∑ k ∈ S, M.p k * (y k - c k) = 0 := by
        rw [show ∑ S ∈ π.parts, ∑ k ∈ S, M.p k * (y k - c k) =
            ∑ k ∈ π.parts.biUnion id, M.p k * (y k - c k) from
            (Finset.sum_biUnion π.disjoint).symm, π.biUnion_parts]
        have hb' := hb; have hy' := hy
        unfold Budget at hb' hy'
        rw [budget_lhs M hM] at hb' hy'
        have : ∑ k, M.p k * (y k - c k) = ∑ k, M.p k * y k - ∑ k, M.p k * c k := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
        rw [this]; linarith
      rw [hpart, mul_zero, add_zero] at hsum
      exact hsum
  · intro B hBne hs1 c cs
    constructor
    · intro hcs
      refine ⟨hcs.1, hcs.2.1, ?_⟩
      obtain ⟨k₀, hk₀⟩ := hBne
      set K' := deriv φ (V M (cara γ) B cs) * Real.exp (-γ * cs k₀) * (M.P k₀ / M.p k₀)
      have hK' : 0 < K' := by
        have := hφ.1.2 _ (V_lt M hM hγ ⟨k₀, hk₀⟩ cs)
        have := Real.exp_pos (-γ * cs k₀)
        have := div_pos (hM.1 k₀) (hM.2.2.1 k₀)
        positivity
      refine ⟨K', hK', fun i hi => ?_⟩
      have h := inter_pair M hM hγ hφ.1 hcs hi hk₀
      rw [hdc]
      have hP := (hM.1 i).ne'; have hp := (hM.2.2.1 i).ne'
      calc _ = (deriv φ (V M (cara γ) B cs) * Real.exp (-γ * cs i) * (M.P i / M.p i)) *
            (M.p i / M.P i) := by field_simp
        _ = K' * (M.p i / M.P i) := by rw [h]
    · rintro ⟨hoff, hcon, lam, hlam, hfoc⟩
      refine ⟨hoff, hcon, fun y hy1 hy2 => ?_⟩
      have hPB := probE_pos M hM hBne
      apply mul_le_mul_of_nonneg_left _ hPB.le
      have hmono : MonotoneOn φ (Set.Iio (1 / γ)) :=
        (strictMonoOn_of_deriv_pos (convex_Iio _) hφ.1.1.continuousOn
          (fun x hx => by rw [interior_Iio] at hx; exact hφ.1.2 x hx)).monotoneOn
      apply hmono (V_lt M hM hγ hBne y) (V_lt M hM hγ hBne cs)
      have t := V_tangent M hM hγ hBne cs y
      have hd := hφ.1.2 _ (V_lt M hM hγ hBne cs)
      have e : ∑ k ∈ B, M.P k * Real.exp (-γ * cs k) * (y k - cs k) =
          (lam / deriv φ (V M (cara γ) B cs)) * ∑ k ∈ B, M.p k * (y k - cs k) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
        have hf := hfoc k hk
        rw [hdc] at hf
        have hPk := (hM.1 k).ne'
        have he : Real.exp (-γ * cs k) =
            lam * (M.p k / M.P k) / deriv φ (V M (cara γ) B cs) := by
          rw [← hf]; field_simp
        rw [he]; field_simp
      have hz : ∑ k ∈ B, M.p k * (y k - cs k) = 0 := by
        have : ∑ k ∈ B, M.p k * (y k - cs k) = ∑ k ∈ B, M.p k * y k - ∑ k ∈ B, M.p k * cs k := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
        rw [this, hy2, hcon, sub_self]
      rw [e, hz, mul_zero, zero_div, add_zero] at t
      exact t

namespace DiscCore

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma ev_build (M : Market Ω) (hM : M.Standing) {γ : ℝ} (hγ : 0 < γ) {φ : ℝ → ℝ}
    {S : Finset Ω} (hS : S.Nonempty) (z : ℝ) (x : Ω → ℝ)
    (hx : ∀ i ∈ S, x i = -(1 / γ) * (z - Real.log (rE M S) + Real.log (M.p i / M.P i))) :
    V M (cara γ) S x = (1 - Real.exp z) / γ ∧
    ∀ i ∈ S, deriv φ (V M (cara γ) S x) * deriv (cara γ) (x i) =
      (psi φ γ (Real.exp z) / rE M S) * (M.p i / M.P i) := by
  have hpS := Finset.sum_pos (fun i _ => hM.2.2.1 i) hS
  have hPS := probE_pos M hM hS
  have hr : 0 < rE M S := div_pos hpS hPS
  have he : ∀ i ∈ S, Real.exp (-γ * x i) = Real.exp z * (M.p i / M.P i) / rE M S := by
    intro i hi
    have hpP : 0 < M.p i / M.P i := div_pos (hM.2.2.1 i) (hM.1 i)
    rw [hx i hi, show -γ * (-(1 / γ) * (z - Real.log (rE M S) + Real.log (M.p i / M.P i))) =
      z - Real.log (rE M S) + Real.log (M.p i / M.P i) by field_simp,
      Real.exp_add, Real.exp_sub, Real.exp_log hr, Real.exp_log hpP]
    ring
  have hV : V M (cara γ) S x = (1 - Real.exp z) / γ := by
    unfold V cara
    have : ∀ i ∈ S, M.P i / probE M S * ((1 - Real.exp (-γ * x i)) / γ) =
        (M.P i / probE M S - Real.exp z * M.p i / (rE M S * probE M S)) / γ := by
      intro i hi; rw [he i hi]; have := (hM.1 i).ne'; field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, Finset.sum_sub_distrib, sum_weights M hM hS,
      ← Finset.sum_div, ← Finset.mul_sum]
    congr 1
    have : rE M S * probE M S = priceE M S := by
      unfold rE; field_simp
    rw [this]; unfold priceE; field_simp
  refine ⟨hV, fun i hi => ?_⟩
  rw [deriv_cara hγ.ne', he i hi, hV]
  unfold psi
  rw [show (1 - Real.exp z) / γ = (1 - Real.exp z) / γ from rfl]
  field_simp

lemma Mf_sub_strictMono {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) : StrictMono (fun z => Mf φ γ z - z) := by
  apply strictMono_of_deriv_pos
  intro z
  have h : deriv (fun z => Mf φ γ z - z) z = _ :=
    ((hasDerivAt_Mf hγ hφ z).fun_sub (hasDerivAt_id' z)).deriv
  rw [h]
  have := A_pos hφ (v_lt hγ (Real.exp_pos z))
  have := Real.exp_pos z
  have : 0 < Real.exp z * Aφ φ ((1 - Real.exp z) / γ) / γ := by positivity
  linarith

lemma Mf_strictMono {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) : StrictMono (Mf φ γ) := by
  intro a b hab
  have := Mf_sub_strictMono hγ hφ hab
  linarith

lemma Mf_surj {φ : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hφ : AggregationAverse φ (Set.Iio (1 / γ))) : Function.Surjective (Mf φ γ) := by
  intro y
  have hcont : Continuous (Mf φ γ) :=
    continuous_iff_continuousAt.2 fun z => (hasDerivAt_Mf hγ hφ z).continuousAt
  set t := |y - Mf φ γ 0|
  have ht : 0 ≤ t := abs_nonneg _
  have h1 : Mf φ γ 0 + t ≤ Mf φ γ t := by
    have := (Mf_sub_strictMono hγ hφ).monotone ht; linarith
  have h2 : Mf φ γ (-t) ≤ Mf φ γ 0 - t := by
    have := (Mf_sub_strictMono hγ hφ).monotone (neg_nonpos.2 ht); linarith
  have hy1 : y ≤ Mf φ γ t := by have := le_abs_self (y - Mf φ γ 0); linarith
  have hy2 : Mf φ γ (-t) ≤ y := by have := neg_abs_le (y - Mf φ γ 0); linarith
  obtain ⟨z, -, hz⟩ := intermediate_value_Icc (by linarith : -t ≤ t) hcont.continuousOn ⟨hy2, hy1⟩
  exact ⟨z, hz⟩

end DiscCore

open DiscCore in
theorem solution {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ))) :
    (∀ π : PDS Ω, IsPDS M π → ∃! c : Ω → ℝ, IsDemand M (cara γ) φ π c) ∧
    (∀ B : Finset Ω, B.Nonempty → M.s₁ ∉ B → ∀ c : Ω → ℝ,
      ∃! cs : Ω → ℝ, IsIntermediate M (cara γ) φ B c cs) := by
  have hFC := foc_char M hM γ hγ φ hφ
  have hr : ∀ S : Finset Ω, S.Nonempty → 0 < rE M S := fun S hS =>
    div_pos (Finset.sum_pos (fun i _ => hM.2.2.1 i) hS) (probE_pos M hM hS)
  have hpsi := psi_strictMono hγ hφ
  constructor
  · intro π hπ
    -- existence
    set e := StrictMono.orderIsoOfSurjective (Mf φ γ) (Mf_strictMono hγ hφ) (Mf_surj hγ hφ)
    have he : ∀ z, e z = Mf φ γ z := fun z => rfl
    have hes : ∀ y, Mf φ γ (e.symm y) = y := fun y => by rw [← he, e.apply_symm_apply]
    let R : Ω → ℝ := fun i => Real.log (rE M (π.part i))
    let q : Ω → ℝ := fun i => Real.log (M.p i / M.P i)
    let xℓ : ℝ → Ω → ℝ := fun ℓ i => -(1 / γ) * (e.symm (ℓ + R i) - R i + q i)
    set W := M.I - ∑ k ∈ Finset.univ.erase M.s₁, M.l k * M.p k
    let F : ℝ → ℝ := fun ℓ => ∑ i, M.p i * xℓ ℓ i
    have hFcont : Continuous F := by
      apply continuous_finset_sum; intro i _
      exact continuous_const.mul (continuous_const.mul
        (((e.symm.continuous.comp (continuous_id.add continuous_const)).sub
          continuous_const).add continuous_const))
    set K0 := ∑ i, M.p i * (-(1 / γ) * (- R i + q i))
    have hFform : ∀ ℓ, F ℓ = -(1 / γ) * ∑ i, M.p i * e.symm (ℓ + R i) + K0 := by
      intro ℓ; simp only [F, xℓ, K0]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    set Rb := ∑ i, |R i|
    have hRb : ∀ i, |R i| ≤ Rb := fun i =>
      Finset.single_le_sum (f := fun i => |R i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hpsum : ∑ i, M.p i = 1 := hM.2.2.2
    -- large ℓ gives small expenditure
    have hbig : ∀ Z, ∃ ℓ, F ℓ ≤ -(1 / γ) * Z + K0 := by
      intro Z
      refine ⟨e Z + Rb, ?_⟩
      rw [hFform]
      have : Z ≤ ∑ i, M.p i * e.symm (e Z + Rb + R i) := by
        calc Z = ∑ i, M.p i * Z := by rw [← Finset.sum_mul, hpsum, one_mul]
          _ ≤ _ := by
            apply Finset.sum_le_sum; intro i _
            apply mul_le_mul_of_nonneg_left _ (hM.2.2.1 i).le
            have h1 := neg_abs_le (R i); have h2 := hRb i
            have := e.symm.monotone (show e Z ≤ e Z + Rb + R i by linarith)
            rwa [e.symm_apply_apply] at this
      have hg : 0 < 1 / γ := by positivity
      nlinarith
    have hsmall : ∀ Z, ∃ ℓ, -(1 / γ) * Z + K0 ≤ F ℓ := by
      intro Z
      refine ⟨e Z - Rb, ?_⟩
      rw [hFform]
      have : ∑ i, M.p i * e.symm (e Z - Rb + R i) ≤ Z := by
        calc _ ≤ ∑ i, M.p i * Z := by
              apply Finset.sum_le_sum; intro i _
              apply mul_le_mul_of_nonneg_left _ (hM.2.2.1 i).le
              have h1 := le_abs_self (R i); have h2 := hRb i
              have := e.symm.monotone (show e Z - Rb + R i ≤ e Z by linarith)
              rwa [e.symm_apply_apply] at this
          _ = Z := by rw [← Finset.sum_mul, hpsum, one_mul]
      have hg : 0 < 1 / γ := by positivity
      nlinarith
    obtain ⟨ℓ1, hℓ1⟩ := hbig (γ * (K0 - W))
    obtain ⟨ℓ2, hℓ2⟩ := hsmall (γ * (K0 - W))
    have hval : -(1 / γ) * (γ * (K0 - W)) + K0 = W := by field_simp; ring
    rw [hval] at hℓ1 hℓ2
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, F ℓ = W := by
      rcases le_total ℓ1 ℓ2 with h | h
      · obtain ⟨ℓ, -, hℓ⟩ := intermediate_value_Icc h hFcont.continuousOn ⟨hℓ1, hℓ2⟩
        exact ⟨ℓ, hℓ⟩
      · obtain ⟨ℓ, -, hℓ⟩ := intermediate_value_Icc' h hFcont.continuousOn ⟨hℓ1, hℓ2⟩
        exact ⟨ℓ, hℓ⟩
    set c := xℓ ℓ
    have hcD : IsDemand M (cara γ) φ π c := by
      apply ((hFC.1 π hπ c).2)
      refine ⟨?_, Real.exp ℓ, Real.exp_pos ℓ, fun S hS i hi => ?_⟩
      · unfold Budget; rw [budget_lhs M hM]
        have : ∑ k, M.p k * c k = W := hℓ
        rw [this]; simp only [W]; ring
      · have hSne := π.nonempty_of_mem_parts hS
        have hpart : ∀ k ∈ S, π.part k = S := fun k hk => π.part_eq_of_mem hS hk
        have hb := ev_build (φ := φ) M hM hγ hSne (e.symm (ℓ + Real.log (rE M S))) c
          (fun k hk => by simp only [c, xℓ, R, q, hpart k hk])
        rw [hb.2 i hi]
        congr 1
        unfold psi
        have hz := hes (ℓ + Real.log (rE M S))
        unfold Mf at hz
        have hrS := hr S hSne
        have hpos := psi_pos hγ hφ (Real.exp_pos (e.symm (ℓ + Real.log (rE M S))))
        have : psi φ γ (Real.exp (e.symm (ℓ + Real.log (rE M S)))) = Real.exp ℓ * rE M S := by
          rw [← Real.exp_log hpos, hz, Real.exp_add, Real.exp_log hrS]
        unfold psi at this
        rw [this]; field_simp
    refine ⟨c, hcD, fun c' hc' => ?_⟩
    -- uniqueness
    obtain ⟨hb1, l1, hl1, hf1⟩ := (hFC.1 π hπ c').1 hc'
    obtain ⟨hb2, l2, hl2, hf2⟩ := (hFC.1 π hπ c).1 hcD
    have ev1 : ∀ S ∈ π.parts, _ := fun S hS =>
      ev_facts M hM hγ hφ (π.nonempty_of_mem_parts hS) c' l1 (hf1 S hS)
    have ev2 : ∀ S ∈ π.parts, _ := fun S hS =>
      ev_facts M hM hγ hφ (π.nonempty_of_mem_parts hS) c l2 (hf2 S hS)
    have hsum : ∑ k, M.p k * c' k = ∑ k, M.p k * c k := by
      unfold Budget at hb1 hb2; rw [budget_lhs M hM] at hb1 hb2; linarith
    -- compare multipliers
    have cmp : ∀ a b : ℝ, ∀ x y : Ω → ℝ,
        (∀ S ∈ π.parts, 0 < 1 - γ * V M (cara γ) S x ∧
          psi φ γ (1 - γ * V M (cara γ) S x) = a * rE M S ∧
          ∀ i ∈ S, -γ * x i = Real.log ((1 - γ * V M (cara γ) S x) / rE M S) +
            Real.log (M.p i / M.P i)) →
        (∀ S ∈ π.parts, 0 < 1 - γ * V M (cara γ) S y ∧
          psi φ γ (1 - γ * V M (cara γ) S y) = b * rE M S ∧
          ∀ i ∈ S, -γ * y i = Real.log ((1 - γ * V M (cara γ) S y) / rE M S) +
            Real.log (M.p i / M.P i)) →
        a < b → ∀ i, y i < x i := by
      intro a b x y hx hy hab i
      obtain ⟨S, hS, hiS⟩ := π.exists_mem (Finset.mem_univ i)
      obtain ⟨px, ex, fx⟩ := hx S hS
      obtain ⟨py, ey, fy⟩ := hy S hS
      have hrS := hr S (π.nonempty_of_mem_parts hS)
      have : 1 - γ * V M (cara γ) S x < 1 - γ * V M (cara γ) S y :=
        (hpsi.lt_iff_lt px py).1 (by rw [ex, ey]; exact mul_lt_mul_of_pos_right hab hrS)
      have hl := Real.log_lt_log (div_pos px hrS) (div_lt_div_of_pos_right this hrS)
      have h1 := fx i hiS; have h2 := fy i hiS
      have : -γ * x i < -γ * y i := by linarith
      nlinarith
    have hpos_sum : ∀ x y : Ω → ℝ, (∀ i, y i < x i) → ∑ k, M.p k * y k < ∑ k, M.p k * x k :=
      fun x y h => Finset.sum_lt_sum_of_nonempty ⟨M.s₁, Finset.mem_univ _⟩
        (fun i _ => mul_lt_mul_of_pos_left (h i) (hM.2.2.1 i))
    have heq : l1 = l2 := by
      rcases lt_trichotomy l1 l2 with h | h | h
      · have := hpos_sum c' c (cmp l1 l2 c' c ev1 ev2 h); linarith
      · exact h
      · have := hpos_sum c c' (cmp l2 l1 c c' ev2 ev1 h); linarith
    funext i
    obtain ⟨S, hS, hiS⟩ := π.exists_mem (Finset.mem_univ i)
    obtain ⟨p1, e1, f1⟩ := ev1 S hS
    obtain ⟨p2, e2, f2⟩ := ev2 S hS
    have hY : 1 - γ * V M (cara γ) S c' = 1 - γ * V M (cara γ) S c :=
      hpsi.injOn p1 p2 (by rw [e1, e2, heq])
    have h1 := f1 i hiS; have h2 := f2 i hiS
    rw [hY] at h1
    have : -γ * c' i = -γ * c i := by linarith
    have hγ' : -γ ≠ 0 := by linarith
    exact mul_left_cancel₀ hγ' this
  · intro B hBne hs1 c
    have hrB := hr B hBne
    have hpB : 0 < priceE M B := Finset.sum_pos (fun i _ => hM.2.2.1 i) hBne
    set E := ∑ i ∈ B, M.p i * c i
    set K1 := ∑ i ∈ B, M.p i * (-(1 / γ) * (- Real.log (rE M B) + Real.log (M.p i / M.P i)))
    set z := (E - K1) / (-(1 / γ) * priceE M B)
    let cs : Ω → ℝ := fun i => if i ∈ B then
      -(1 / γ) * (z - Real.log (rE M B) + Real.log (M.p i / M.P i)) else c i
    have hcsB : ∀ i ∈ B, cs i = -(1 / γ) * (z - Real.log (rE M B) + Real.log (M.p i / M.P i)) :=
      fun i hi => if_pos hi
    have hcsI : IsIntermediate M (cara γ) φ B c cs := by
      have hb := ev_build (φ := φ) M hM hγ hBne z cs hcsB
      apply (hFC.2 B hBne hs1 c cs).2
      refine ⟨fun i hi => if_neg hi, ?_, psi φ γ (Real.exp z) / rE M B,
        div_pos (psi_pos hγ hφ (Real.exp_pos z)) hrB, hb.2⟩
      rw [Finset.sum_congr rfl (fun i hi => by rw [hcsB i hi])]
      have : ∑ i ∈ B, M.p i * (-(1 / γ) * (z - Real.log (rE M B) + Real.log (M.p i / M.P i))) =
          -(1 / γ) * priceE M B * z + K1 := by
        simp only [K1]; unfold priceE
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this]; simp only [z]
      have : -(1 / γ) * priceE M B ≠ 0 := by
        have : 0 < 1 / γ := by positivity
        nlinarith
      field_simp; ring
    refine ⟨cs, hcsI, fun cs' hcs' => ?_⟩
    obtain ⟨hoff1, hcon1, l1, hl1, hf1⟩ := (hFC.2 B hBne hs1 c cs').1 hcs'
    obtain ⟨hoff2, hcon2, l2, hl2, hf2⟩ := (hFC.2 B hBne hs1 c cs).1 hcsI
    have ev1 := ev_facts M hM hγ hφ hBne cs' l1 hf1
    have ev2 := ev_facts M hM hγ hφ hBne cs l2 hf2
    -- the B-expenditures pin down Y
    have hsum : ∀ (x : Ω → ℝ) (Y : ℝ), (∀ i ∈ B, -γ * x i = Real.log (Y / rE M B) +
        Real.log (M.p i / M.P i)) → -γ * ∑ i ∈ B, M.p i * x i =
          priceE M B * Real.log (Y / rE M B) + ∑ i ∈ B, M.p i * Real.log (M.p i / M.P i) := by
      intro x Y hx
      rw [Finset.mul_sum]; unfold priceE; rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i hi
      rw [show -γ * (M.p i * x i) = M.p i * (-γ * x i) by ring, hx i hi]; ring
    have s1 := hsum cs' _ ev1.2.2
    have s2 := hsum cs _ ev2.2.2
    rw [hcon1] at s1; rw [hcon2] at s2
    have hlog : Real.log ((1 - γ * V M (cara γ) B cs') / rE M B) =
        Real.log ((1 - γ * V M (cara γ) B cs) / rE M B) := by
      have : priceE M B * Real.log ((1 - γ * V M (cara γ) B cs') / rE M B) =
          priceE M B * Real.log ((1 - γ * V M (cara γ) B cs) / rE M B) := by linarith
      exact mul_left_cancel₀ hpB.ne' this
    funext i
    by_cases hi : i ∈ B
    · have h1 := ev1.2.2 i hi; have h2 := ev2.2.2 i hi
      rw [hlog] at h1
      have : -γ * cs' i = -γ * cs i := by linarith
      have hγ' : -γ ≠ 0 := by linarith
      exact mul_left_cancel₀ hγ' this
    · rw [hoff1 i hi, hoff2 i hi]
