-- Prove2me | solution 1 for GassSaaty.ParametricPivot.lambdaBar_satisfies_ineq3_prime
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:57:34.020525+00:00
-- url     : https://prove2.me/submissions/2605acd7-e3cb-402f-b6e8-c4a7bd1e3b47

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization
open Matrix

namespace GassSaaty.ParametricPivot

lemma gs_unit {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) : IsUnit (basisMatrix A B) := by
  have h : LinearIndependent ℝ (fun i => (basisMatrix A B)ᵀ i) := by
    have := hB
    unfold IsStdBasis at this
    convert this using 1
    funext i r
    rfl
  have := (Matrix.linearIndependent_rows_iff_isUnit).1 h
  exact (Matrix.isUnit_transpose _).1 this

lemma gs_mulVec_u {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (j : Fin n) :
    (basisMatrix A B).mulVec (pivotColumn A B j) = fun i => A i j := by
  unfold pivotColumn
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (gs_unit hB)), Matrix.one_mulVec]

lemma gs_det_E {m : ℕ} (ℓ : Fin m) (u : Fin m → ℝ) :
    (Matrix.updateCol (1 : Matrix (Fin m) (Fin m) ℝ) ℓ u).det = u ℓ := by
  have := Matrix.cramer_apply (1 : Matrix (Fin m) (Fin m) ℝ) u ℓ
  rw [← this, Matrix.cramer_one]; rfl


lemma gs_E_mulVec {m : ℕ} (ℓ : Fin m) (u v : Fin m → ℝ) (hℓ : u ℓ ≠ 0) (w : Fin m → ℝ)
    (hw : w = fun i => if i = ℓ then v ℓ / u ℓ else v i - u i * (v ℓ / u ℓ)) :
    (Matrix.updateCol (1 : Matrix (Fin m) (Fin m) ℝ) ℓ u).mulVec w = v := by
  subst hw
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Matrix.one_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]
  simp only [if_true]
  have : ∀ k ∈ Finset.univ.erase ℓ, (if k = ℓ then u i else if i = k then (1:ℝ) else 0) *
      (if k = ℓ then v ℓ / u ℓ else v k - u k * (v ℓ / u ℓ)) =
      (if i = k then v k - u k * (v ℓ / u ℓ) else 0) := by
    intro k hk
    have hk' : k ≠ ℓ := Finset.ne_of_mem_erase hk
    simp [hk']
  rw [Finset.sum_congr rfl this]
  by_cases hi : i = ℓ
  · subst hi
    simp [Finset.sum_ite_eq]
    field_simp
  · have : i ∈ Finset.univ.erase ℓ := by simp [hi]
    rw [Finset.sum_ite_eq _ i, if_pos this]
    field_simp
    ring

lemma gs_pivot {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B B' : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (s : Fin n) (ℓ : Fin m)
    (hℓ : pivotColumn A B s ℓ ≠ 0) (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    IsUnit (basisMatrix A B') ∧ ∀ j, pivotColumn A B' j = fun i =>
      if i = ℓ then pivotColumn A B j ℓ / pivotColumn A B s ℓ
      else pivotColumn A B j i - pivotColumn A B s i * (pivotColumn A B j ℓ / pivotColumn A B s ℓ) := by
  set u := pivotColumn A B s with hu
  have hBE : basisMatrix A B' = basisMatrix A B * Matrix.updateCol (1 : Matrix (Fin m) (Fin m) ℝ) ℓ u := by
    rw [Matrix.mul_updateCol, Matrix.mul_one, hu, gs_mulVec_u hB]
    ext r k
    simp only [Matrix.updateCol_apply, basisMatrix, Matrix.submatrix_apply, id]
    by_cases hk : k = ℓ
    · subst hk; simp [hB'ℓ]
    · simp [hk, hB'ne k hk]
  have hE : IsUnit (Matrix.updateCol (1 : Matrix (Fin m) (Fin m) ℝ) ℓ u) := by
    rw [Matrix.isUnit_iff_isUnit_det, gs_det_E]; exact isUnit_iff_ne_zero.2 hℓ
  have hU' : IsUnit (basisMatrix A B') := by
    rw [hBE]; exact (gs_unit hB).mul hE
  refine ⟨hU', fun j => ?_⟩
  have key := gs_E_mulVec ℓ u (pivotColumn A B j) hℓ _ rfl
  generalize hw : (fun i => if i = ℓ then pivotColumn A B j ℓ / u ℓ
      else pivotColumn A B j i - u i * (pivotColumn A B j ℓ / u ℓ)) = w at key ⊢
  have h2 : (basisMatrix A B').mulVec w = fun i => A i j := by
    rw [hBE, ← Matrix.mulVec_mulVec, key, gs_mulVec_u hB]
  have h3 : pivotColumn A B' j = (basisMatrix A B')⁻¹.mulVec (fun i => A i j) := rfl
  rw [h3, ← h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hU'), Matrix.one_mulVec]


lemma gs_rc_pivot {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B B' : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (s : Fin n) (ℓ : Fin m)
    (hℓ : pivotColumn A B s ℓ ≠ 0) (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i)
    (c : Fin n → ℝ) (j : Fin n) :
    reducedCost A c B' j = reducedCost A c B j
      - (pivotColumn A B j ℓ / pivotColumn A B s ℓ) * reducedCost A c B s := by
  have hp := (gs_pivot hB s ℓ hℓ hB'ℓ hB'ne).2 j
  have e1 : reducedCost A c B' j = c j - (fun i => c (B' i)) ⬝ᵥ pivotColumn A B' j := by
    unfold reducedCost; rfl
  rw [e1, hp]
  unfold reducedCost
  have hu : ∀ k : Fin n, (basisMatrix A B)⁻¹.mulVec (fun i' => A i' k) = pivotColumn A B k := fun k => rfl
  rw [hu, hu]
  simp only [dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ), ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]
  have h1 : ∑ i ∈ Finset.univ.erase ℓ, c (B' i) *
      (if i = ℓ then pivotColumn A B j ℓ / pivotColumn A B s ℓ
        else pivotColumn A B j i - pivotColumn A B s i * (pivotColumn A B j ℓ / pivotColumn A B s ℓ))
      = ∑ i ∈ Finset.univ.erase ℓ, c (B i) * pivotColumn A B j i
        - (pivotColumn A B j ℓ / pivotColumn A B s ℓ) *
          ∑ i ∈ Finset.univ.erase ℓ, c (B i) * pivotColumn A B s i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.ne_of_mem_erase hi
    rw [hB'ne i hi', if_neg hi']
    ring
  rw [h1]
  simp only [hB'ℓ, if_true]
  field_simp
  ring

lemma gs_rc_basic {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (c : Fin n → ℝ) (i : Fin m) : reducedCost A c B (B i) = 0 := by
  haveI : Invertible (basisMatrix A B) := Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).1 (gs_unit hB))
  exact reducedCost_basic A c B i

lemma gs_col_basic {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (i : Fin m) : pivotColumn A B (B i) = Pi.single i 1 := by
  have h := gs_mulVec_u hB (B i)
  have h2 : (basisMatrix A B).mulVec (Pi.single i 1) = fun r => A r (B i) := by
    funext r; simp [basisMatrix, Matrix.mulVec_single_one]
  have hu := gs_unit hB
  have hinj : Function.Injective (basisMatrix A B).mulVec :=
    Matrix.mulVec_injective_of_isUnit hu
  exact hinj (h.trans h2.symm)

lemma gs_rc_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (d d' : Fin n → ℝ)
    (t : ℝ) (j : Fin n) :
    reducedCost A (d + t • d') B j = reducedCost A d B j + t * reducedCost A d' B j := by
  simp only [reducedCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun i => d (B i) + t * d' (B i)) = (fun i => d (B i)) + t • (fun i => d' (B i)) := by
    funext i; simp
  rw [this, add_dotProduct, smul_dotProduct]
  simp; ring


lemma gs_alpha_pivot {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B B' : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (s : Fin n) (ℓ : Fin m)
    (hℓ : pivotColumn A B s ℓ ≠ 0) (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i)
    (d : Fin n → ℝ) (j : Fin n) :
    alpha A d B' j = alpha A d B j
      - (pivotColumn A B j ℓ / pivotColumn A B s ℓ) * alpha A d B s := by
  unfold alpha
  rw [gs_rc_pivot hB s ℓ hℓ hB'ℓ hB'ne]
  ring

lemma gs_beta_pivot {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B B' : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (s : Fin n) (ℓ : Fin m)
    (hℓ : pivotColumn A B s ℓ ≠ 0) (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i)
    (d : Fin n → ℝ) (j : Fin n) :
    beta A d B' j = beta A d B j
      - (pivotColumn A B j ℓ / pivotColumn A B s ℓ) * beta A d B s := by
  unfold beta
  rw [gs_rc_pivot hB s ℓ hℓ hB'ℓ hB'ne]
  ring

lemma gs_alpha_basic {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (d : Fin n → ℝ) (i : Fin m) : alpha A d B (B i) = 0 := by
  unfold alpha; rw [gs_rc_basic hB]; simp

lemma gs_beta_basic {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (d : Fin n → ℝ) (i : Fin m) : beta A d B (B i) = 0 := by
  unfold beta; rw [gs_rc_basic hB]; simp

lemma eq7_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (s : Fin n) (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    alpha A d B' (B ℓ) = -alpha A d B s / pivotColumn A B s ℓ ∧
      beta A d' B' (B ℓ) = -beta A d' B s / pivotColumn A B s ℓ := by
  have hne : pivotColumn A B s ℓ ≠ 0 := hℓ.ne'
  have h1 : pivotColumn A B (B ℓ) ℓ = 1 := by rw [gs_col_basic hB]; simp
  constructor
  · rw [gs_alpha_pivot hB s ℓ hne hB'ℓ hB'ne, h1, gs_alpha_basic hB]
    field_simp; ring
  · rw [gs_beta_pivot hB s ℓ hne hB'ℓ hB'ne, h1, gs_beta_basic hB]
    field_simp; ring

lemma lamBar_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ j, alpha A d B' j + (-alpha A d B s / beta A d' B s) * beta A d' B' j ≤ 0 := by
  intro j
  have hne : pivotColumn A B s ℓ ≠ 0 := hℓ.ne'
  rw [gs_alpha_pivot hB s ℓ hne hB'ℓ hB'ne, gs_beta_pivot hB s ℓ hne hB'ℓ hB'ne]
  set θ := pivotColumn A B j ℓ / pivotColumn A B s ℓ
  set lam := -alpha A d B s / beta A d' B s with hlam
  have hz : alpha A d B s + lam * beta A d' B s = 0 := by
    rw [hlam]; field_simp; ring
  have : alpha A d B j - θ * alpha A d B s + lam * (beta A d' B j - θ * beta A d' B s)
      = alpha A d B j + lam * beta A d' B j - θ * (alpha A d B s + lam * beta A d' B s) := by ring
  rw [this, hz, mul_zero, sub_zero]
  obtain ⟨t₀, ht₀⟩ := hcons
  by_cases hj : 0 < beta A d' B j
  · have := hsmin j hj
    rw [le_div_iff₀ hj] at this
    have h2 : -alpha A d B j / beta A d' B j * beta A d' B j = -alpha A d B j := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right (hsmin j hj) hj.le]
  · push_neg at hj
    have h0 : t₀ ≤ lam := by
      have := ht₀ s
      rw [hlam, le_div_iff₀ hβs]; linarith
    have h1 := ht₀ j
    nlinarith [mul_le_mul_of_nonpos_right h0 hj]

lemma below_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ t : ℝ, t < -alpha A d B s / beta A d' B s →
      ¬ ∀ j, alpha A d B' j + t * beta A d' B' j ≤ 0 := by
  intro t ht hall
  have h := hall (B ℓ)
  obtain ⟨e1, e2⟩ := eq7_core A d d' B B' hB s ℓ hℓ hB'ℓ hB'ne
  rw [e1] at h
  have e2' : beta A d' B' (B ℓ) = -beta A d' B s / pivotColumn A B s ℓ := e2
  rw [e2'] at h
  rw [lt_div_iff₀ hβs] at ht
  have : (-alpha A d B s / pivotColumn A B s ℓ + t * (-beta A d' B s / pivotColumn A B s ℓ))
      = -(alpha A d B s + t * beta A d' B s) / pivotColumn A B s ℓ := by ring
  rw [this] at h
  have h3 : 0 < -(alpha A d B s + t * beta A d' B s) / pivotColumn A B s ℓ :=
    div_pos (by linarith) hℓ
  linarith

theorem ineq3_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ) (B : Fin m ↪ Fin n)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0) (t : ℝ) :
    (∀ j, alpha A d B j + t * beta A d' B j ≤ 0) ↔
      (lamLower A d d' B ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ lamBar A d d' B) := by
  obtain ⟨t₀, ht₀⟩ := hcons
  unfold lamLower lamBar
  rw [Finset.sup_le_iff, Finset.le_inf_iff]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hj' : beta A d' B j < 0 := (Finset.mem_filter.1 hj).2
      have := h j
      rw [WithBot.coe_le_coe, div_le_iff_of_neg hj']
      linarith
    · have hj' : 0 < beta A d' B j := (Finset.mem_filter.1 hj).2
      have := h j
      rw [WithTop.coe_le_coe, le_div_iff₀ hj']
      linarith
  · rintro ⟨h1, h2⟩ j
    rcases lt_trichotomy (beta A d' B j) 0 with hj | hj | hj
    · have := h1 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
      rw [WithBot.coe_le_coe, div_le_iff_of_neg hj] at this
      linarith
    · have := ht₀ j
      rw [hj] at this ⊢
      simpa using this
    · have := h2 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
      rw [WithTop.coe_le_coe, le_div_iff₀ hj] at this
      linarith

end GassSaaty.ParametricPivot

open GassSaaty.ParametricPivot


theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ j, alpha A d B' j + (-alpha A d B s / beta A d' B s) * beta A d' B' j ≤ 0 := by
  exact lamBar_core A d d' B B' hB hcons s hβs hsmin ℓ hℓ hB'ℓ hB'ne
