-- Prove2me | solution 1 for DisclosureStatics.Aggregation.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:23:52.532992+00:00
-- url     : https://prove2.me/submissions/aae80430-749d-45eb-94f7-3cfc3faa9d3a

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

end DiscCore

open DiscCore in
theorem solution {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : Regular φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct) :
    ∀ S ∈ ρ.parts, ∀ i ∈ S, ∀ j ∈ S, ct i - cs i = ct j - cs j := by
  obtain ⟨⟨h𝒮, hcard, hs1, hB⟩, hρ⟩ := hagg
  intro S hS i hi j hj
  by_cases hij : i = j
  · rw [hij]
  have hρ1 : {M.s₁} ∈ ρ.parts := by
    rw [hρ]; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hπ, hs1⟩)
  have hs1S : M.s₁ ∉ S := by
    intro h
    have := ρ.eq_of_mem_parts hS hρ1 h (Finset.mem_singleton_self _)
    rw [this, Finset.mem_singleton] at hi hj
    exact hij (hi.trans hj.symm)
  have hi1 : i ≠ M.s₁ := fun h => hs1S (h ▸ hi)
  have hj1 : j ≠ M.s₁ := fun h => hs1S (h ▸ hj)
  have hdpos : ∀ v, v < 1 / γ → 0 < deriv φ v := fun v hv => hφ.2 v hv
  -- FOC for ct inside S
  have hA := demand_pair M hM hγ hφ ρ hct hS hS hi hj hi1 hj1
  have hdS := hdpos _ (V_lt M hM hγ (ρ.nonempty_of_mem_parts hS) ct)
  have hA' : Real.exp (-γ * ct i) * (M.P i / M.p i) = Real.exp (-γ * ct j) * (M.P j / M.p j) := by
    have := hA; rw [mul_assoc, mul_assoc] at this
    exact mul_left_cancel₀ hdS.ne' this
  -- FOC for cs inside S
  have hC : Real.exp (-γ * cs i) * (M.P i / M.p i) = Real.exp (-γ * cs j) * (M.P j / M.p j) := by
    by_cases hSB : S = B
    · subst hSB
      have := inter_pair M hM hγ hφ hcs hi hj
      have hd := hdpos _ (V_lt M hM hγ (ρ.nonempty_of_mem_parts hS) cs)
      rw [mul_assoc, mul_assoc] at this
      exact mul_left_cancel₀ hd.ne' this
    · have hSπ : S ∈ π.parts \ 𝒮 := by
        rw [hρ] at hS
        rcases Finset.mem_insert.1 hS with h | h
        · exact absurd h hSB
        · exact h
      obtain ⟨hSπ, hS𝒮⟩ := Finset.mem_sdiff.1 hSπ
      have hoff : ∀ k ∈ S, cs k = c k := by
        intro k hk
        apply hcs.1
        intro hkB
        rw [hB, Finset.mem_sup] at hkB
        obtain ⟨S', hS', hkS'⟩ := hkB
        have := π.eq_of_mem_parts (h𝒮 hS') hSπ hkS' hk
        exact hS𝒮 (this ▸ hS')
      have := demand_pair M hM hγ hφ π hc hSπ hSπ hi hj hi1 hj1
      have hd := hdpos _ (V_lt M hM hγ (π.nonempty_of_mem_parts hSπ) c)
      rw [mul_assoc, mul_assoc] at this
      rw [hoff i hi, hoff j hj]
      exact mul_left_cancel₀ hd.ne' this
  have hwi : 0 < M.P i / M.p i := div_pos (hM.1 i) (hM.2.2.1 i)
  have hwj : 0 < M.P j / M.p j := div_pos (hM.1 j) (hM.2.2.1 j)
  have key : Real.exp (-γ * (ct i - cs i)) = Real.exp (-γ * (ct j - cs j)) := by
    have e1 : Real.exp (-γ * (ct i - cs i)) = Real.exp (-γ * ct i) / Real.exp (-γ * cs i) := by
      rw [← Real.exp_sub]; ring_nf
    have e2 : Real.exp (-γ * (ct j - cs j)) = Real.exp (-γ * ct j) / Real.exp (-γ * cs j) := by
      rw [← Real.exp_sub]; ring_nf
    rw [e1, e2, div_eq_div_iff (Real.exp_pos _).ne' (Real.exp_pos _).ne']
    have := congrArg₂ (· * ·) hA' hC.symm
    have hne : (M.P i / M.p i) * (M.P j / M.p j) ≠ 0 := (mul_pos hwi hwj).ne'
    apply mul_right_cancel₀ hne
    linear_combination this
  have := Real.exp_injective key
  have hγ' : γ ≠ 0 := hγ.ne'
  have : ct i - cs i = ct j - cs j := by
    have h2 : -γ * ((ct i - cs i) - (ct j - cs j)) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (neg_eq_zero.1 h) hγ'
    · linarith
  exact this
