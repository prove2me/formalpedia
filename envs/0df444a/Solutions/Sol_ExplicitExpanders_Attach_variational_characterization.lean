-- Prove2me | solution 1 for ExplicitExpanders.Attach.variational_characterization
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:51:03.201745+00:00
-- url     : https://prove2.me/submissions/14cdfb1e-74fe-4db1-8384-339fc7b6be11

import Mathlib
set_option autoImplicit false
open Matrix

theorem solution {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (k : ℝ) (hrow : A *ᵥ 1 = k • 1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ (μ : ℝ) (f : ι → ℝ), f ≠ 0 → ∑ i, f i = 0 → A *ᵥ f = μ • f → |μ| ≤ lam) ↔
      (∀ f : ι → ℝ, ∑ i, f i = 0 → |f ⬝ᵥ (A *ᵥ f)| ≤ lam * (f ⬝ᵥ f)) := by
  classical
  constructor
  swap
  · intro h μ f hf hsum hAf
    have h1 := h f hsum
    rw [hAf, dotProduct_smul, smul_eq_mul, abs_mul] at h1
    have hpos : 0 < f ⬝ᵥ f := by
      rcases lt_or_eq_of_le (dotProduct_self_star_nonneg f) with h | h
      · simpa using h
      · exfalso; apply hf; simpa [dotProduct_self_eq_zero] using h.symm
    have h2 : |f ⬝ᵥ f| = f ⬝ᵥ f := abs_of_pos hpos
    rw [h2] at h1
    exact le_of_mul_le_mul_right (by linarith) hpos
  intro h f hf
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := ι)
    positivity
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set J : Matrix ι ι ℝ := Matrix.of fun _ _ => (1 : ℝ) with hJdef
  set A' : Matrix ι ι ℝ := A - (k / N) • J with hA'def
  have hJ1 : J *ᵥ (1 : ι → ℝ) = N • (1 : ι → ℝ) := by
    ext i; simp [hJdef, mulVec, dotProduct, hNdef]
  have hJf : ∀ g : ι → ℝ, ∑ i, g i = 0 → J *ᵥ g = 0 := by
    intro g hg; ext i; simp [hJdef, mulVec, dotProduct, hg]
  have hA'1 : A' *ᵥ (1 : ι → ℝ) = 0 := by
    rw [hA'def, sub_mulVec, smul_mulVec, hJ1, hrow]
    ext i; simp [hN]
  have hA'f : ∀ g : ι → ℝ, ∑ i, g i = 0 → A' *ᵥ g = A *ᵥ g := by
    intro g hg
    rw [hA'def, sub_mulVec, smul_mulVec, hJf g hg]; simp
  have hA'H : A'ᴴ = A' := by
    have hJs : Jᵀ = J := by ext i j; simp [hJdef]
    rw [conjTranspose_eq_transpose_of_trivial, hA'def, transpose_sub, transpose_smul, hJs]
    have : Aᵀ = A := hA
    rw [this]
  have hA'T : A'ᵀ = A' := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hA'H
  have key : ∀ σ : ℝ, σ * σ = 1 → (lam • (1 : Matrix ι ι ℝ) - σ • A').PosSemidef := by
    intro σ hσ
    set H : Matrix ι ι ℝ := lam • (1 : Matrix ι ι ℝ) - σ • A' with hHdef
    have hH : H.IsHermitian := by
      simp [IsHermitian, hHdef, conjTranspose_sub, conjTranspose_smul, hA'H, hA'T]
    rw [hH.posSemidef_iff_eigenvalues_nonneg]
    intro i
    show 0 ≤ hH.eigenvalues i
    set e : ι → ℝ := ⇑(hH.eigenvectorBasis i) with hedef
    have hmul : H *ᵥ e = hH.eigenvalues i • e := by
      simpa using hH.mulVec_eigenvectorBasis i
    have hne : e ≠ 0 := by
      intro h0
      apply (hH.eigenvectorBasis.orthonormal.ne_zero i)
      ext j
      simpa using congrFun h0 j
    have hAe : A' *ᵥ e = (σ * (lam - hH.eigenvalues i)) • e := by
      have h1 : H *ᵥ e = lam • e - σ • (A' *ᵥ e) := by
        rw [hHdef, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
      rw [h1] at hmul
      have h2 : σ • (A' *ᵥ e) = (lam - hH.eigenvalues i) • e := by
        rw [sub_smul]
        rw [sub_eq_iff_eq_add] at hmul
        rw [hmul]; abel
      calc A' *ᵥ e = (σ * σ) • (A' *ᵥ e) := by rw [hσ, one_smul]
        _ = σ • (σ • (A' *ᵥ e)) := by rw [mul_smul]
        _ = _ := by rw [h2, smul_smul]
    have hσabs : |σ| = 1 := by
      have := abs_mul_abs_self σ
      nlinarith [abs_nonneg σ]
    by_cases hs : ∑ j, e j = 0
    · have := h (σ * (lam - hH.eigenvalues i)) e hne hs (by rw [← hA'f e hs]; exact hAe)
      rw [abs_mul, hσabs, one_mul] at this
      linarith [(abs_le.mp this).2]
    · have h0 : (1 : ι → ℝ) ⬝ᵥ (A' *ᵥ e) = 0 := by
        rw [dotProduct_mulVec]
        have : (1 : ι → ℝ) ᵥ* A' = A' *ᵥ 1 := by
          conv_lhs => rw [← hA'T]
          exact vecMul_transpose A' 1
        rw [this, hA'1]; simp
      rw [hAe, dotProduct_smul] at h0
      have h3 : (1 : ι → ℝ) ⬝ᵥ e = ∑ j, e j := by simp [dotProduct]
      rw [h3, smul_eq_mul] at h0
      have h4 : σ * (lam - hH.eigenvalues i) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact h
        · exact absurd h hs
      have hσ0 : σ ≠ 0 := by intro h; rw [h] at hσabs; simp at hσabs
      have : lam - hH.eigenvalues i = 0 := by
        rcases mul_eq_zero.mp h4 with h | h
        · exact absurd h hσ0
        · exact h
      linarith
  have q1 := (key 1 (by norm_num)).dotProduct_mulVec_nonneg f
  have q2 := (key (-1) (by norm_num)).dotProduct_mulVec_nonneg f
  simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, hA'f f hf, star_trivial, dotProduct_sub, dotProduct_add, dotProduct_smul,
    smul_eq_mul, neg_smul, one_smul, neg_mul, one_mul, sub_neg_eq_add] at q1 q2
  rw [abs_le]
  constructor <;> linarith
