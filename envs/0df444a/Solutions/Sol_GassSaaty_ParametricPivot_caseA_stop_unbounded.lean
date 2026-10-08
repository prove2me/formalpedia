-- Prove2me | solution 1 for GassSaaty.ParametricPivot.caseA_stop_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:06:25.403+00:00
-- url     : https://prove2.me/submissions/40c67065-0956-476c-8fcd-00ad5f8ef201

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


lemma gs_bfs {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {B : Fin m ↪ Fin n}
    {x : Fin n → ℝ} (hx : IsSimplexState A b B x) :
    IsBasicFeasibleSolution (stdFormSystem A b) x := by
  obtain ⟨hB, ⟨hAx, hx0⟩, hxn⟩ := hx
  have hU := gs_unit hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    rcases i with r | j
    · show A r ⬝ᵥ x = b r
      rw [← hAx]; rfl
    · simp [stdFormSystem] at hi
  · classical
    let nb : Finset (Fin n) := (Finset.univ.image B)ᶜ
    have hnb : ∀ j, j ∈ nb ↔ j ∉ Set.range B := by
      intro j; simp [nb]
    have hcard : nb.card = n - m := by
      simp [nb, Finset.card_compl, Finset.card_image_of_injective _ B.injective]
    refine ⟨(Finset.univ : Finset (Fin m)).disjSum nb, ?_, ?_, ?_⟩
    · rw [Finset.card_disjSum, hcard]; simp
      have : m ≤ n := by
        simpa using Fintype.card_le_of_embedding B
      omega
    · intro a ha
      rcases a with r | j
      · show A r ⬝ᵥ x = b r
        rw [← hAx]; rfl
      · have : j ∈ nb := by simpa using ha
        show Pi.single j 1 ⬝ᵥ x = 0
        simp [hxn j ((hnb j).1 this)]
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      let G : Fin m ⊕ Fin n → ℝ := fun a => if h : a ∈ (Finset.univ : Finset (Fin m)).disjSum nb then g ⟨a, h⟩ else 0
      have hG : ∀ a : ↥((Finset.univ : Finset (Fin m)).disjSum nb), G a.1 = g a := by
        intro a; simp [G, a.2]
      have hsum0 : ∑ a ∈ (Finset.univ : Finset (Fin m)).disjSum nb, G a • (stdFormSystem A b a).a = 0 := by
        rw [← Finset.sum_coe_sort ((Finset.univ : Finset (Fin m)).disjSum nb)]
        rw [← hg]
        apply Finset.sum_congr rfl
        intro a _
        rw [hG]
      rw [Finset.sum_disjSum] at hsum0
      simp only [stdFormSystem] at hsum0
      have h1 : (basisMatrix A B)ᵀ.mulVec (fun r => G (Sum.inl r)) = 0 := by
        funext k
        have := congr_fun hsum0 (B k)
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        have h2 : ∑ j ∈ nb, G (Sum.inr j) * (Pi.single j (1:ℝ) : Fin n → ℝ) (B k) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have : j ≠ B k := fun h => (hnb j).1 hj ⟨k, h.symm⟩
          simp [Pi.single_apply, this]
        rw [h2, add_zero] at this
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, basisMatrix, Matrix.submatrix_apply, id, Pi.zero_apply]
        rw [← this]
        apply Finset.sum_congr rfl
        intro r _; ring
      have hGl : ∀ r, G (Sum.inl r) = 0 := by
        have := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_transpose _).2 hU) (h1.trans (Matrix.mulVec_zero _).symm)
        intro r; exact congr_fun this r
      have hGr : ∀ j ∈ nb, G (Sum.inr j) = 0 := by
        intro j0 hj0
        have := congr_fun hsum0 j0
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hGl, zero_mul,
          Finset.sum_const_zero, zero_add] at this
        rw [Finset.sum_eq_single j0] at this
        · simpa using this
        · intro j _ hne; simp [Pi.single_apply, Ne.symm hne]
        · intro h; exact absurd hj0 h
      intro a
      rw [← hG a]
      rcases a with ⟨a | j, ha⟩
      · exact hGl a
      · have : j ∈ nb := by simpa using ha
        exact hGr j this
  · intro i
    rcases i with r | j
    · show A r ⬝ᵥ x = b r
      rw [← hAx]; rfl
    · show 0 ≤ Pi.single j 1 ⬝ᵥ x
      simpa using hx0 j


lemma gs_pos {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {B : Fin m ↪ Fin n}
    {x : Fin n → ℝ}
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (hx : IsSimplexState A b B x) (i : Fin m) : 0 < x (B i) := by
  classical
  have hbfs := gs_bfs hx
  obtain ⟨hB, ⟨hAx, hx0⟩, hxn⟩ := hx
  have hnn : 0 ≤ x (B i) := hx0 _
  by_contra hcon
  have hz : x (B i) = 0 := le_antisymm (not_lt.1 hcon) hnn
  apply hnd x hbfs
  refine ⟨hbfs.1, ?_⟩
  let nb : Finset (Fin n) := (Finset.univ.image B)ᶜ
  have hcard : nb.card = n - m := by
    simp [nb, Finset.card_compl, Finset.card_image_of_injective _ B.injective]
  have hsub : (↑(insert (B i) nb) : Set (Fin n)) ⊆ {j | x j = 0} := by
    intro j hj
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hj
    rcases hj with rfl | hj
    · exact hz
    · exact hxn j (by simpa [nb] using hj)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [nb]), hcard] at h1
  omega



lemma gs_dir_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (s : Fin n) (j : Fin n) :
    basicDirection A B s j = (if j = s then 1 else 0) -
      ∑ i : Fin m, if j = B i then pivotColumn A B s i else 0 := by
  unfold basicDirection
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.single_apply]
  rfl

lemma gs_dir_B {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) {s : Fin n}
    (hs : s ∉ Set.range B) (i : Fin m) :
    basicDirection A B s (B i) = - pivotColumn A B s i := by
  rw [gs_dir_sum]
  have : B i ≠ s := fun h => hs ⟨i, h⟩
  simp [this, B.injective.eq_iff]

lemma gs_dir_s {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) {s : Fin n}
    (hs : s ∉ Set.range B) : basicDirection A B s s = 1 := by
  rw [gs_dir_sum]
  have : ∀ i, s ≠ B i := fun i h => hs ⟨i, h.symm⟩
  simp [this]

lemma gs_dir_other {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) {s j : Fin n}
    (hj : j ∉ Set.range B) (hjs : j ≠ s) : basicDirection A B s j = 0 := by
  rw [gs_dir_sum]
  have : ∀ i, j ≠ B i := fun i h => hj ⟨i, h.symm⟩
  simp [this, hjs]

lemma gs_dir_A {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (hB : IsStdBasis A B) (s : Fin n) : A.mulVec (basicDirection A B s) = 0 := by
  have hu := gs_mulVec_u hB s
  have hd : basicDirection A B s = Pi.single s 1 -
      ∑ i : Fin m, Pi.single (B i) (pivotColumn A B s i) := rfl
  rw [hd]
  generalize pivotColumn A B s = u at hu ⊢
  funext r
  have hr := congr_fun hu r
  simp only [Matrix.mulVec, dotProduct, basisMatrix, Matrix.submatrix_apply, id] at hr
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Finset.sum_apply, Pi.single_apply, mul_sub,
    Finset.sum_sub_distrib, Pi.zero_apply]
  have e1 : ∑ x : Fin n, A r x * (if x = s then (1:ℝ) else 0) = A r s := by simp
  have e2 : ∑ x : Fin n, A r x * ∑ i : Fin m, (if x = B i then u i else 0)
      = ∑ i : Fin m, A r (B i) * u i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [e1, e2, hr]; ring

lemma gs_dir_cost {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (s : Fin n)
    (c : Fin n → ℝ) : c ⬝ᵥ basicDirection A B s = reducedCost A c B s := by
  unfold basicDirection reducedCost
  rw [dotProduct_sub, dotProduct_sum, dotProduct_single_one]
  simp only [dotProduct_single]
  rfl


lemma gs_exists_theta {m : ℕ} (f : Fin m → ℝ) (hf : ∀ i, 0 < f i) : ∃ θ : ℝ, 0 < θ ∧ ∀ i, θ ≤ f i := by
  refine ⟨1 / (1 + ∑ i, 1 / f i), ?_, fun i => ?_⟩
  · have : 0 ≤ ∑ i, 1 / f i := Finset.sum_nonneg (fun i _ => (one_div_pos.2 (hf i)).le)
    positivity
  · have h1 : 1 / f i ≤ ∑ i, 1 / f i :=
      Finset.single_le_sum (f := fun i => 1 / f i) (fun i _ => (one_div_pos.2 (hf i)).le) (Finset.mem_univ i)
    have h2 : 1 / f i ≤ 1 + ∑ i, 1 / f i := by linarith
    have := one_div_le_one_div_of_le (one_div_pos.2 (hf i)) h2
    simpa using this

lemma gs_ray_mem {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {B : Fin m ↪ Fin n}
    {x : Fin n → ℝ} (hx : IsSimplexState A b B x) {s : Fin n} (hs : s ∉ Set.range B)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i, θ * pivotColumn A B s i ≤ x (B i)) :
    x + θ • basicDirection A B s ∈ stdPolyhedron A b := by
  obtain ⟨hB, ⟨hAx, hx0⟩, hxn⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, gs_dir_A hB, hAx]; simp
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hj : j ∈ Set.range B
    · obtain ⟨i, rfl⟩ := hj
      rw [gs_dir_B A B hs i]
      have := hθ i
      linarith
    · by_cases hjs : j = s
      · subst hjs
        rw [gs_dir_s A B hs, hxn _ hj]; linarith
      · rw [gs_dir_other A B hj hjs, hxn _ hj]; simp

lemma gs_ray_cost {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (s : Fin n)
    (c x : Fin n → ℝ) (θ : ℝ) :
    c ⬝ᵥ (x + θ • basicDirection A B s) = c ⬝ᵥ x + θ * reducedCost A c B s := by
  rw [dotProduct_add, dotProduct_smul, gs_dir_cost]; rfl

lemma gs_rc_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (c : Fin n → ℝ) (j : Fin n) :
    reducedCost A c B j = c j - (((fun i => c (B i)) ᵥ* (basisMatrix A B)⁻¹) ᵥ* A) j := by
  unfold reducedCost
  rw [Matrix.dotProduct_mulVec]; rfl

lemma gs_cost_id {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (c y : Fin n → ℝ) :
    c ⬝ᵥ y = ((fun i => c (B i)) ᵥ* (basisMatrix A B)⁻¹) ⬝ᵥ (A.mulVec y)
      + (fun j => reducedCost A c B j) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec]
  have : (fun j => reducedCost A c B j) = c - (((fun i => c (B i)) ᵥ* (basisMatrix A B)⁻¹) ᵥ* A) := by
    funext j; rw [gs_rc_eq]; rfl
  rw [this, sub_dotProduct]; ring

lemma gs_rc_x {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {B : Fin m ↪ Fin n}
    {x : Fin n → ℝ} (hx : IsSimplexState A b B x) (c : Fin n → ℝ) :
    (fun j => reducedCost A c B j) ⬝ᵥ x = 0 := by
  obtain ⟨hB, ⟨hAx, hx0⟩, hxn⟩ := hx
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hj
    show reducedCost A c B (B i) * x (B i) = 0
    rw [gs_rc_basic hB]; simp
  · rw [hxn j hj]; simp

lemma gs_opt_of_rc {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {B : Fin m ↪ Fin n}
    {x : Fin n → ℝ} (hx : IsSimplexState A b B x) (c : Fin n → ℝ)
    (h : ∀ j, 0 ≤ reducedCost A c B j) : IsLpOptimal c (stdPolyhedron A b) x := by
  refine ⟨hx.2.1, fun y hy => ?_⟩
  have h1 := gs_cost_id A B c y
  have h2 := gs_cost_id A B c x
  rw [hy.1] at h1
  rw [hx.2.1.1] at h2
  rw [gs_rc_x hx c, add_zero] at h2
  have h3 : 0 ≤ (fun j => reducedCost A c B j) ⬝ᵥ y :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (h j) (hy.2 j))
  linarith

lemma gs_rc_of_opt {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {B : Fin m ↪ Fin n}
    {x : Fin n → ℝ}
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (hx : IsSimplexState A b B x) (c : Fin n → ℝ)
    (hopt : IsLpOptimal c (stdPolyhedron A b) x) (s : Fin n) : 0 ≤ reducedCost A c B s := by
  by_contra hneg
  push_neg at hneg
  have hB := hx.1
  have hs : s ∉ Set.range B := by
    rintro ⟨i, rfl⟩
    rw [gs_rc_basic hB] at hneg; exact lt_irrefl _ hneg
  have hpos := gs_pos hnd hx
  obtain ⟨θ, hθ, hθf⟩ := gs_exists_theta
    (fun i => x (B i) / (|pivotColumn A B s i| + 1)) (fun i => div_pos (hpos i) (by positivity))
  have hmem := gs_ray_mem hx hs hθ.le (fun i => by
    have h1 := hθf i
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : pivotColumn A B s i ≤ |pivotColumn A B s i| := le_abs_self _
    nlinarith)
  have := hopt.2 _ hmem
  rw [gs_ray_cost] at this
  nlinarith


lemma gs_alpha_beta_rc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n) (d d' : Fin n → ℝ)
    (t : ℝ) (j : Fin n) :
    alpha A d B j + t * beta A d' B j = - reducedCost A (d + t • d') B j := by
  unfold alpha beta
  rw [gs_rc_add]; ring

theorem optimal_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x) (t : ℝ) :
    IsLpOptimal (d + t • d') (stdPolyhedron A b) x ↔
      ∀ j, alpha A d B j + t * beta A d' B j ≤ 0 := by
  constructor
  · intro h j
    rw [gs_alpha_beta_rc]
    have := gs_rc_of_opt hnd hx _ h j
    linarith
  · intro h
    apply gs_opt_of_rc hx
    intro j
    have := h j
    rw [gs_alpha_beta_rc] at this
    linarith

theorem caseA_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hcol : ∀ i, pivotColumn A B s i ≤ 0) :
    ∀ t : ℝ, -alpha A d B s / beta A d' B s < t →
      lpValue (d + t • d') (stdPolyhedron A b) = ⊥ ∧
        ¬ ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y := by
  intro t ht
  have hB := hx.1
  have hs : s ∉ Set.range B := by
    rintro ⟨i, rfl⟩
    rw [gs_beta_basic hB] at hβs; exact lt_irrefl _ hβs
  rw [div_lt_iff₀ hβs] at ht
  have hrc : reducedCost A (d + t • d') B s < 0 := by
    have := gs_alpha_beta_rc A B d d' t s
    linarith
  set c := d + t • d' with hc
  set r := - reducedCost A c B s with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have key : ∀ M : ℝ, ∃ y ∈ stdPolyhedron A b, c ⬝ᵥ y < M := by
    intro M
    set θ := (|c ⬝ᵥ x - M| + 1) / r with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hmem := gs_ray_mem hx hs hθ0 (fun i => by
      have := hx.2.1.2 (B i)
      have h2 : θ * pivotColumn A B s i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ0 (hcol i)
      simp only [Pi.zero_apply] at this
      linarith)
    refine ⟨_, hmem, ?_⟩
    rw [gs_ray_cost]
    have : θ * reducedCost A c B s = -(|c ⬝ᵥ x - M| + 1) := by
      rw [hθ]; have : reducedCost A c B s = -r := by rw [hr]; ring
      rw [this]; field_simp
    rw [this]
    have := le_abs_self (c ⬝ᵥ x - M)
    linarith
  refine ⟨?_, ?_⟩
  · rw [lpValue, EReal.eq_bot_iff_forall_lt]
    intro M
    obtain ⟨y, hy, hlt⟩ := key M
    exact lt_of_le_of_lt (iInf₂_le y hy) (by exact_mod_cast hlt)
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨y', hy', hlt⟩ := key (c ⬝ᵥ y)
    exact absurd (hy2 y' hy') (not_le.2 hlt)

lemma gs_unit_rev {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Fin m ↪ Fin n}
    (h : IsUnit (basisMatrix A B)) : IsStdBasis A B := by
  have h1 : LinearIndependent ℝ (fun i => (basisMatrix A B)ᵀ i) :=
    (Matrix.linearIndependent_rows_iff_isUnit).2 ((Matrix.isUnit_transpose _).2 h)
  unfold IsStdBasis
  convert h1 using 1
  funext i r
  rfl

theorem goal_core {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B B' : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hratio : ∀ i, 0 < pivotColumn A B s i →
      x (B ℓ) / pivotColumn A B s ℓ ≤ x (B i) / pivotColumn A B s i)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    IsLeast
      {t : ℝ | IsLpOptimal (d + t • d') (stdPolyhedron A b)
        (x + (x (B ℓ) / pivotColumn A B s ℓ) • basicDirection A B s)}
      (-alpha A d B s / beta A d' B s) := by
  have hB := hx.1
  have hne : pivotColumn A B s ℓ ≠ 0 := hℓ.ne'
  have hs : s ∉ Set.range B := by
    rintro ⟨i, rfl⟩
    rw [gs_beta_basic hB] at hβs; exact lt_irrefl _ hβs
  set θ := x (B ℓ) / pivotColumn A B s ℓ with hθ
  have hxBℓ : x (B ℓ) ≥ 0 := hx.2.1.2 _
  have hθ0 : 0 ≤ θ := div_nonneg hxBℓ hℓ.le
  have hθu : θ * pivotColumn A B s ℓ = x (B ℓ) := by rw [hθ]; field_simp
  have hmem := gs_ray_mem hx hs hθ0 (fun i => by
    by_cases hi : 0 < pivotColumn A B s i
    · have := hratio i hi
      rw [le_div_iff₀ hi] at this
      linarith
    · push_neg at hi
      have h2 : θ * pivotColumn A B s i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ0 hi
      have := hx.2.1.2 (B i)
      simp only [Pi.zero_apply] at this
      linarith)
  have hstate : IsSimplexState A b B' (x + θ • basicDirection A B s) := by
    refine ⟨gs_unit_rev (gs_pivot hB s ℓ hne hB'ℓ hB'ne).1, hmem, ?_⟩
    intro j hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hjB : j ∈ Set.range B
    · obtain ⟨i, rfl⟩ := hjB
      by_cases hi : i = ℓ
      · subst hi
        rw [gs_dir_B A B hs]; linarith
      · exact absurd ⟨i, hB'ne i hi⟩ hj
    · have hjs : j ≠ s := fun h => hj ⟨ℓ, by rw [hB'ℓ, h]⟩
      rw [gs_dir_other A B hjB hjs, hx.2.2 j hjB]; simp
  have hiff := optimal_core A b d d' hnd B' _ hstate
  refine ⟨?_, ?_⟩
  · show IsLpOptimal _ _ _
    rw [hiff]
    exact lamBar_core A d d' B B' hB hcons s hβs hsmin ℓ hℓ hB'ℓ hB'ne
  · intro t ht
    by_contra hlt
    push_neg at hlt
    have h := (hiff t).1 ht
    exact below_core A d d' B B' hB s hβs ℓ hℓ hB'ℓ hB'ne t hlt h

end GassSaaty.ParametricPivot

open GassSaaty.ParametricPivot


theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (hcol : ∀ i, pivotColumn A B s i ≤ 0) :
    ∀ t : ℝ, -alpha A d B s / beta A d' B s < t →
      lpValue (d + t • d') (stdPolyhedron A b) = ⊥ ∧
        ¬ ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y := by
  exact caseA_core A b d d' B x hx s hβs hcol
