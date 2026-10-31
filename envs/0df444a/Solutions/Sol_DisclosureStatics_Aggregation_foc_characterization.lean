-- Prove2me | solution 1 for DisclosureStatics.Aggregation.foc_characterization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:31:22.246318+00:00
-- url     : https://prove2.me/submissions/eecdda7a-6e2e-4d2b-877f-25a59c77d56d

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

open DiscCore in
theorem solution {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
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
