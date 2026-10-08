-- Prove2me | solution 1 for ExplicitExpanders.Delete.variational
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:30:32.088775+00:00
-- url     : https://prove2.me/submissions/c5d62f6a-39c7-4fb5-88d8-8368bccf06e1

import Mathlib

set_option autoImplicit false

namespace VarE2884983

open Matrix

/-- self-adjointness of a symmetric matrix w.r.t. the dot product -/
theorem dot_mulVec_symm {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm)
    (u f : V → ℝ) : u ⬝ᵥ (A *ᵥ f) = (A *ᵥ u) ⬝ᵥ f := by
  rw [dotProduct_mulVec]
  congr 1
  conv_lhs => rw [← hA.eq]
  rw [vecMul_transpose]

theorem dot_self_pos {V : Type*} [Fintype V] (f : V → ℝ) (hf : f ≠ 0) : 0 < f ⬝ᵥ f := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hf
  unfold dotProduct
  exact Finset.sum_pos' (fun i _ => mul_self_nonneg (f i)) ⟨v, Finset.mem_univ _, mul_self_pos.mpr hv⟩

theorem dot_self_nonneg' {V : Type*} [Fintype V] (f : V → ℝ) : 0 ≤ f ⬝ᵥ f := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (f i))

/-- Parseval for an orthonormal basis of EuclideanSpace, in dot-product form -/
theorem parseval {V : Type*} [Fintype V] (b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V))
    (f g : V → ℝ) : ∑ i, (f ⬝ᵥ ⇑(b i)) * (⇑(b i) ⬝ᵥ g) = f ⬝ᵥ g := by
  have h := b.sum_inner_mul_inner (WithLp.toLp 2 f) (WithLp.toLp 2 g)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  simpa [dotProduct_comm] using h

theorem main {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm) (d : ℝ)
    (hrow : A *ᵥ (fun _ => (1 : ℝ)) = d • (fun _ => (1 : ℝ))) (lam : ℝ)
    (h1 : ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam)
    (f : V → ℝ) (hf : ∑ v, f v = 0) : |f ⬝ᵥ (A *ᵥ f)| ≤ lam * (f ⬝ᵥ f) := by
  classical
  have hH : A.IsHermitian := by
    show Aᴴ = A
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hA
  set b := hH.eigenvectorBasis with hb
  set μ := hH.eigenvalues with hμ
  have heig : ∀ i, A *ᵥ ⇑(b i) = μ i • ⇑(b i) := fun i => hH.mulVec_eigenvectorBasis i
  set one : V → ℝ := fun _ => 1 with hone
  have hf1 : one ⬝ᵥ f = 0 := by simp [dotProduct, hone, hf]
  -- expansion
  have hexp : f ⬝ᵥ (A *ᵥ f) = ∑ i, μ i * ((⇑(b i) ⬝ᵥ f) * (⇑(b i) ⬝ᵥ f)) := by
    rw [← parseval b f (A *ᵥ f)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dot_mulVec_symm A hA, heig i, smul_dotProduct, smul_eq_mul, dotProduct_comm f]
    ring
  have hnorm : f ⬝ᵥ f = ∑ i, (⇑(b i) ⬝ᵥ f) * (⇑(b i) ⬝ᵥ f) := by
    rw [← parseval b f f]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dotProduct_comm f]
  -- per-eigenvalue bound
  have hkey : ∀ i, (⇑(b i) ⬝ᵥ f) ≠ 0 → |μ i| ≤ lam := by
    intro i hci
    set u : V → ℝ := ⇑(b i) with hu
    set s : ℝ := one ⬝ᵥ u with hs
    have hne : Nonempty V := by
      by_contra hV
      rw [not_nonempty_iff] at hV
      exact hci (by simp [dotProduct])
    have hn : (Fintype.card V : ℝ) ≠ 0 := by
      have := Fintype.card_pos (α := V)
      positivity
    have hms : μ i * s = d * s := by
      have e1 : one ⬝ᵥ (A *ᵥ u) = μ i * s := by
        rw [heig i, dotProduct_smul, smul_eq_mul]
      have e2 : one ⬝ᵥ (A *ᵥ u) = d * s := by
        rw [dot_mulVec_symm A hA, hrow, smul_dotProduct, smul_eq_mul]
      rw [← e1, e2]
    set g : V → ℝ := u - (s / Fintype.card V) • one with hg
    have hgf : g ⬝ᵥ f = u ⬝ᵥ f := by
      rw [hg, sub_dotProduct, smul_dotProduct, hf1]; simp
    have hg0 : g ≠ 0 := by
      intro h
      apply hci
      rw [← hgf, h, zero_dotProduct]
    have hgsum : ∑ v, g v = 0 := by
      have : ∑ v, g v = one ⬝ᵥ g := by simp [dotProduct, hone]
      rw [this, hg, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      have : one ⬝ᵥ one = (Fintype.card V : ℝ) := by simp [dotProduct, hone]
      rw [this, ← hs]
      field_simp
      ring
    have hAg : A *ᵥ g = μ i • g := by
      rw [hg, mulVec_sub, mulVec_smul, heig i, hrow, smul_sub, smul_smul, smul_smul]
      congr 2
      field_simp
      linarith [hms]
    exact h1 (μ i) g hg0 hgsum hAg
  rw [hexp, hnorm, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_of_nonneg (mul_self_nonneg (⇑(b i) ⬝ᵥ f))]
  by_cases hc : (⇑(b i) ⬝ᵥ f) = 0
  · simp [hc]
  · exact mul_le_mul_of_nonneg_right (hkey i hc) (mul_self_nonneg _)

end VarE2884983

open Matrix in
theorem solution {V : Type*} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm) (d : ℝ)
    (hrow : A *ᵥ (fun _ => (1 : ℝ)) = d • (fun _ => (1 : ℝ))) (lam : ℝ) :
    (∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → ∑ v, f v = 0 → A *ᵥ f = μ • f → |μ| ≤ lam) ↔
      (∀ f : V → ℝ, ∑ v, f v = 0 → |f ⬝ᵥ (A *ᵥ f)| ≤ lam * (f ⬝ᵥ f)) := by
  constructor
  · intro h1 f hf
    exact VarE2884983.main A hA d hrow lam h1 f hf
  · intro h2 μ f hf0 hfs hAf
    have h := h2 f hfs
    rw [hAf, dotProduct_smul, smul_eq_mul, abs_mul,
      abs_of_nonneg (VarE2884983.dot_self_nonneg' f)] at h
    exact le_of_mul_le_mul_right h (VarE2884983.dot_self_pos f hf0)
