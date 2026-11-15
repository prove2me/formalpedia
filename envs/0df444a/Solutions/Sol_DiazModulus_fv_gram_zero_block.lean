-- Prove2me | solution 1 for DiazModulus.fv_gram_zero_block
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:42:56.59919+00:00
-- url     : https://prove2.me/submissions/c53d6b18-e6ba-4c85-a159-25ac39ad3618

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rank_bound

open Complex ComplexConjugate

/-! # Roy's Corollary 1 for a Gram matrix

Take `Q̄`-bases `x₀, …, x_{d−1}` of `X` and `y₀, …, y_{ℓ−1}` of `Y`. The Gram matrix `G = (xᵢ · yⱼ)` has
entries in `ℒ̃`, so Roy's Corollary 1 gives invertible algebraic matrices `P`, `Q` and integers
`1 ≤ d′ ≤ d`, `ℓ′ ≤ ℓ` with `(PGQ)ᵢⱼ = 0` for `i < d′` and `j ≥ ℓ′`, and `d·ℓ′ ≤ rank G·(d′ + ℓ′)`.
Put `x̃ᵢ = Σₐ Pᵢₐ xₐ` and `ỹⱼ = Σ_b Q_{bj} y_b`; since `P`, `Q` are invertible with algebraic entries,
these are again `Q̄`-free families in `X` and `Y`, and bilinearity gives `x̃ᵢ · ỹⱼ = (PGQ)ᵢⱼ`.
`X₁` is spanned by the `x̃ᵢ` with `i < d′` (dimension `d′`), `Y₁` by the `ỹⱼ` with `j ≥ ℓ′`
(dimension `ℓ − ℓ′`), and `X₁ · Y₁ = 0` by bilinearity. Finally `G` is the product of the matrix of
rows `xᵢ` with the transpose of the matrix of rows `yⱼ`, so its rank is at most the dimension of the
ℂ-span of the `xᵢ`, which lies in the ℂ-span of `X`. -/

namespace RC3_GZ
open DiazModulus

/-- An invertible algebraic change of basis keeps a family `Q̄`-free. -/
theorem li_comb {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → (Fin n → ℂ))
    (hv : LinearIndependent (↥Qbar) v) (p : Matrix ι ι (↥Qbar)) (hp : p.det ≠ 0) :
    LinearIndependent (↥Qbar) (fun i => ∑ a, p i a • v a) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  have h0 : ∑ a, (∑ i, c i * p i a) • v a = 0 := by
    rw [← hc]
    simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hvm : Matrix.vecMul c p = 0 := funext fun a => by
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]; exact hv _ h0 a
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hp hvm)

/-- Orthogonality of two sets passes to their `Q̄`-spans. -/
theorem dot_zero_span {n : ℕ} {S T : Set (Fin n → ℂ)} (h : ∀ s ∈ S, ∀ t ∈ T, s ⬝ᵥ t = 0) :
    ∀ x ∈ Submodule.span (↥Qbar) S, ∀ y ∈ Submodule.span (↥Qbar) T, x ⬝ᵥ y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem s hs =>
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact h s hs t ht
    | zero => exact dotProduct_zero _
    | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, add_zero]
    | smul c a _ ha => rw [dotProduct_smul, ha, smul_zero]
  | zero => intro y _; exact zero_dotProduct _
  | add a b _ _ ha hb => intro y hy; rw [add_dotProduct, ha y hy, hb y hy, add_zero]
  | smul c a _ ha => intro y hy; rw [smul_dotProduct, ha y hy, smul_zero]

/-- The determinant of an algebraic matrix, read in `Q̄`. -/
theorem det_ne_zero_of {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : ∀ i j, P i j ∈ Qbar)
    (hu : IsUnit P.det) : (Matrix.of fun i j => (⟨P i j, hP i j⟩ : ↥Qbar)).det ≠ 0 := by
  intro h
  have hm : P = (Matrix.of fun i j => (⟨P i j, hP i j⟩ : ↥Qbar)).map Qbar.subtype := by ext; rfl
  have := RingHom.map_det Qbar.subtype (Matrix.of fun i j => (⟨P i j, hP i j⟩ : ↥Qbar))
  rw [h, map_zero, RingHom.mapMatrix_apply, ← hm] at this
  exact hu.ne_zero this.symm

end RC3_GZ

open DiazModulus RC3_GZ in
theorem solution {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X] [FiniteDimensional (↥Qbar) ↥Y]
    (hX : 0 < Module.finrank (↥Qbar) ↥X)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x ⬝ᵥ y ∈ LogAlgTilde) :
    ∃ X₁ Y₁ : Submodule (↥Qbar) (Fin n → ℂ), X₁ ≤ X ∧ Y₁ ≤ Y ∧
      0 < Module.finrank (↥Qbar) ↥X₁ ∧ (∀ x ∈ X₁, ∀ y ∈ Y₁, x ⬝ᵥ y = 0) ∧
      Module.finrank (↥Qbar) ↥X * (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥Y₁) ≤
        Module.finrank ℂ ↥(Submodule.span ℂ (X : Set (Fin n → ℂ))) *
          (Module.finrank (↥Qbar) ↥X₁ + (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥Y₁)) := by
  set d := Module.finrank (↥Qbar) ↥X with hd
  set l := Module.finrank (↥Qbar) ↥Y with hl
  let bx := Module.finBasis (↥Qbar) ↥X
  let byy := Module.finBasis (↥Qbar) ↥Y
  let x : Fin d → (Fin n → ℂ) := fun a => (bx a : Fin n → ℂ)
  let y : Fin l → (Fin n → ℂ) := fun b => (byy b : Fin n → ℂ)
  have hxli : LinearIndependent (↥Qbar) x := bx.linearIndependent.map' X.subtype X.ker_subtype
  have hyli : LinearIndependent (↥Qbar) y := byy.linearIndependent.map' Y.subtype Y.ker_subtype
  let G : Matrix (Fin d) (Fin l) ℂ := Matrix.of fun i j => x i ⬝ᵥ y j
  have hG : ∀ i j, G i j ∈ LogAlgTilde := fun i j => hXY _ (bx i).2 _ (byy j).2
  obtain ⟨d', l', P, Q, hd'0, hd'd, hl'l, hPu, hQu, hP, hQ, hz, hroy⟩ :=
    DiazModulus.roy_rank_bound G hG hX
  let p : Matrix (Fin d) (Fin d) (↥Qbar) := Matrix.of fun i a => ⟨P i a, hP i a⟩
  let q : Matrix (Fin l) (Fin l) (↥Qbar) := Matrix.of fun b j => ⟨Q b j, hQ b j⟩
  let xt : Fin d → (Fin n → ℂ) := fun i => ∑ a, p i a • x a
  let yt : Fin l → (Fin n → ℂ) := fun j => ∑ b, q.transpose j b • y b
  have hxt_mem : ∀ i, xt i ∈ X := fun i => X.sum_mem fun a _ => X.smul_mem _ (bx a).2
  have hyt_mem : ∀ j, yt j ∈ Y := fun j => Y.sum_mem fun b _ => Y.smul_mem _ (byy b).2
  have hxtli : LinearIndependent (↥Qbar) xt := li_comb x hxli p (det_ne_zero_of P hP hPu)
  have hytli : LinearIndependent (↥Qbar) yt := li_comb y hyli q.transpose
    (by rw [Matrix.det_transpose]; exact det_ne_zero_of Q hQ hQu)
  -- the Gram identity
  have hgram : ∀ i j, xt i ⬝ᵥ yt j = (P * G * Q) i j := by
    intro i j
    simp only [xt, yt, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
      Subfield.smul_def, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, p, q,
      Matrix.transpose_apply,
      Matrix.of_apply, G]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  -- the two families
  let ιy : Fin (l - l') → Fin l := fun j => ⟨l' + j.val, by omega⟩
  have hιy : Function.Injective ιy := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [ιy] at this; omega)
  let fx : Fin d' → (Fin n → ℂ) := fun i => xt (Fin.castLE hd'd i)
  let fy : Fin (l - l') → (Fin n → ℂ) := fun j => yt (ιy j)
  have hfx : LinearIndependent (↥Qbar) fx := hxtli.comp _ (Fin.castLE_injective hd'd)
  have hfy : LinearIndependent (↥Qbar) fy := hytli.comp _ hιy
  refine ⟨Submodule.span (↥Qbar) (Set.range fx), Submodule.span (↥Qbar) (Set.range fy),
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => hxt_mem _),
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hyt_mem _), ?_, ?_, ?_⟩
  · rw [finrank_span_eq_card hfx, Fintype.card_fin]; exact hd'0
  · refine dot_zero_span ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    simp only [fx, fy]
    rw [hgram]
    exact hz _ _ (by simp) (by simp [ιy])
  · rw [finrank_span_eq_card hfx, finrank_span_eq_card hfy, Fintype.card_fin, Fintype.card_fin]
    have hll : l - (l - l') = l' := by omega
    rw [hll]
    -- rank of the Gram matrix
    let A : Matrix (Fin d) (Fin n) ℂ := Matrix.of fun i k => x i k
    let B : Matrix (Fin l) (Fin n) ℂ := Matrix.of fun j k => y j k
    have hGAB : G = A * B.transpose := by
      ext i j; simp [G, A, B, Matrix.mul_apply, dotProduct]
    have hrk : G.rank ≤ Module.finrank ℂ ↥(Submodule.span ℂ (X : Set (Fin n → ℂ))) := by
      rw [hGAB]
      refine (Matrix.rank_mul_le_left _ _).trans ?_
      rw [Matrix.rank_eq_finrank_span_row]
      refine Submodule.finrank_mono (Submodule.span_mono ?_)
      rintro _ ⟨i, rfl⟩
      exact (bx i).2
    calc d * l' ≤ G.rank * (d' + l') := hroy
      _ ≤ _ := Nat.mul_le_mul_right _ hrk
