-- Prove2me | solution 1 for Conway99Formal.TwoSidedSchur.full_gram_bound_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:25:17.729274+00:00
-- url     : https://prove2.me/submissions/dfb4250b-30fd-49b2-9a6d-4084f6330bb5

import Definitions.Def_Conway99_TwoSidedSchurPureBlocks_20261003

set_option autoImplicit false

namespace Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

def pairing (L : Matrix g e ℝ) (x : g → ℝ) (y : e → ℝ) : ℝ :=
  ∑ i, x i * action L y i

/-- The two complementary PSD block inequalities, evaluated on `(x,t*y)`.
The same `L`, `a`, and `q` occur in both blocks. -/
structure ComplementaryPSD (L : Matrix g e ℝ) where
  a : (g → ℝ) → ℝ
  q : (e → ℝ) → ℝ
  first : ∀ (x : g → ℝ) (y : e → ℝ) (t : ℝ),
    0 ≤ a x + t ^ 2 * q y - 2 * t * pairing L x y
  second : ∀ (x : g → ℝ) (y : e → ℝ) (t : ℝ),
    0 ≤ 28 * normSq x - a x + t ^ 2 * (28 * normSq y - q y) +
      2 * t * pairing L x y

/-- The exact full-Gram contraction: `LᵀL ≤ 196I` in quadratic-form order. -/
theorem full_gram_bound (L : Matrix g e ℝ) (h : ComplementaryPSD L)
    (y : e → ℝ) : normSq (action L y) ≤ 196 * normSq y := by
  let x := action L y
  have hc := h.first x y 14
  have hp := h.second x y (-14)
  have hs : pairing L x y = normSq x := rfl
  rw [hs] at hc hp
  nlinarith

section LiteralBlocks

variable {h : Type*} [Fintype h] [DecidableEq g] [DecidableEq h]

/-- The good principal block `A=40I-K_GG`. -/
def goodA (K : Matrix (g ⊕ h) (g ⊕ h) ℝ) : Matrix g g ℝ :=
  (40 : ℝ) • 1 - K.submatrix Sum.inl Sum.inl

/-- The other good principal block `A_plus=K_GG-12I`. -/
def goodAplus (K : Matrix (g ⊕ h) (g ⊕ h) ℝ) : Matrix g g ℝ :=
  K.submatrix Sum.inl Sum.inl - (12 : ℝ) • 1

theorem good_block_sum (K : Matrix (g ⊕ h) (g ⊕ h) ℝ) :
    goodA K + goodAplus K = (28 : ℝ) • 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [goodA, goodAplus, Matrix.one_apply, hij] <;> ring

/-- The exceptional principal block of the first complementary matrix. -/
def exceptionalBlock (K W R : Matrix h h ℝ) : Matrix (h ⊕ h) (h ⊕ h) ℝ :=
  Matrix.fromBlocks ((40 : ℝ) • 1 - K) (-W) (-Wᵀ) R

private theorem quadratic_fromBlocks (A : Matrix g g ℝ)
    (L : Matrix g (h ⊕ h) ℝ) (Q : Matrix (h ⊕ h) (h ⊕ h) ℝ)
    (x : g → ℝ) (y : h ⊕ h → ℝ) (t : ℝ) :
    (Sum.elim x (t • y)) ⬝ᵥ
        ((Matrix.fromBlocks A (-L) (-Lᵀ) Q) *ᵥ (Sum.elim x (t • y))) =
      x ⬝ᵥ (A *ᵥ x) + t ^ 2 * (y ⬝ᵥ (Q *ᵥ y)) -
        2 * t * pairing L x y := by
  rw [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    dotProduct_add, Matrix.neg_mulVec, Matrix.mulVec_smul,
    dotProduct_neg, smul_dotProduct, dotProduct_smul]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [pairing, action, dotProduct, Matrix.mulVec]
  ring

private def rootRotate : g ⊕ (h ⊕ h) → (g ⊕ h) ⊕ h
  | .inl i => .inl (.inl i)
  | .inr (.inl j) => .inl (.inr j)
  | .inr (.inr j) => .inr j

private theorem first_reindexed (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ)
    (hK : ∀ i j, K i j = K j i) :
    (firstBlock K W R).submatrix rootRotate rootRotate =
      Matrix.fromBlocks (goodA K) (-goodCross K W) (-(goodCross K W)ᵀ)
        (exceptionalBlock (K.submatrix Sum.inr Sum.inr)
          (W.submatrix Sum.inr id) R) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [rootRotate, firstBlock, goodA, goodCross, exceptionalBlock,
      Matrix.fromBlocks, Matrix.fromCols, Matrix.one_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.transpose_apply] <;> try rw [hK] <;> ring

private theorem second_reindexed (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ)
    (hK : ∀ i j, K i j = K j i) :
    (secondBlock K W R).submatrix rootRotate rootRotate =
      Matrix.fromBlocks (goodAplus K) (goodCross K W) (goodCross K W)ᵀ
        ((28 : ℝ) • 1 - exceptionalBlock (K.submatrix Sum.inr Sum.inr)
          (W.submatrix Sum.inr id) R) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [rootRotate, secondBlock, goodAplus, goodCross, exceptionalBlock,
      Matrix.fromBlocks, Matrix.fromCols, Matrix.one_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.transpose_apply] <;> try rw [hK] <;> split_ifs <;> ring

private theorem complement_quadratic (A : Matrix g g ℝ) (x : g → ℝ) :
    x ⬝ᵥ (((28 : ℝ) • 1 - A) *ᵥ x) =
      28 * normSq x - x ⬝ᵥ (A *ᵥ x) := by
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, normSq, dotProduct]
  calc
    (∑ i, x i * (28 * x i - (A *ᵥ x) i)) =
        ∑ i, (28 * (x i * x i) - x i * (A *ᵥ x) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 28 * (∑ i, x i * x i) - ∑ i, x i * (A *ᵥ x) i := by
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum]

private noncomputable def complementary_of_reindexed
    (A : Matrix g g ℝ) (L : Matrix g (h ⊕ h) ℝ)
    (Q : Matrix (h ⊕ h) (h ⊕ h) ℝ)
    (hc : (Matrix.fromBlocks A (-L) (-Lᵀ) Q).PosSemidef)
    (hp : (Matrix.fromBlocks ((28 : ℝ) • 1 - A) L Lᵀ
      ((28 : ℝ) • 1 - Q)).PosSemidef) : ComplementaryPSD L := by
  refine ⟨(fun x => x ⬝ᵥ (A *ᵥ x)), (fun y => y ⬝ᵥ (Q *ᵥ y)), ?_, ?_⟩
  · intro x y t
    have hz : star (Sum.elim x (t • y)) = Sum.elim x (t • y) := by
      ext i
      simp
    have hpos := hc.dotProduct_mulVec_nonneg (Sum.elim x (t • y))
    rw [hz, quadratic_fromBlocks] at hpos
    exact hpos
  · intro x y t
    have hz : star (Sum.elim x (t • y)) = Sum.elim x (t • y) := by
      ext i
      simp
    have hpos := hp.dotProduct_mulVec_nonneg (Sum.elim x (t • y))
    rw [hz] at hpos
    have heq := quadratic_fromBlocks ((28 : ℝ) • 1 - A) (-L)
      ((28 : ℝ) • 1 - Q) x y t
    simp only [neg_neg, Matrix.transpose_neg] at heq
    rw [heq, complement_quadratic A x, complement_quadratic Q y] at hpos
    have hact : action (-L) y = -action L y := by
      funext i
      simp [action, Matrix.neg_apply, Finset.sum_neg_distrib]
    have hpair : pairing (-L) x y = -pairing L x y := by
      simp [pairing, hact, Finset.sum_neg_distrib]
    rw [hpair] at hpos
    nlinarith

/-- The common rooted `K,W,R` and both actual PSD blocks supply the
quadratic interface used by the full-Gram contraction. -/
noncomputable def complementaryPSD_of_blocks
    (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ)
    (hc : (firstBlock K W R).PosSemidef)
    (hp : (secondBlock K W R).PosSemidef) :
    ComplementaryPSD (goodCross K W) := by
  have hK (i j : g ⊕ h) : K i j = K j i := by
    have hs := hc.isHermitian.apply (Sum.inl i) (Sum.inl j)
    by_cases hij : i = j
    · subst j; rfl
    simp [firstBlock, Matrix.fromBlocks, Matrix.one_apply, hij,
      Ne.symm hij] at hs
    linarith
  have hc' := hc.submatrix (rootRotate : g ⊕ (h ⊕ h) → (g ⊕ h) ⊕ h)
  have hp' := hp.submatrix (rootRotate : g ⊕ (h ⊕ h) → (g ⊕ h) ⊕ h)
  rw [first_reindexed K W R hK] at hc'
  rw [second_reindexed K W R hK] at hp'
  have hA : goodAplus K = (28 : ℝ) • 1 - goodA K := by
    have hs := good_block_sum K
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hs)
  rw [hA] at hp'
  exact complementary_of_reindexed (goodA K) (goodCross K W)
    (exceptionalBlock (K.submatrix Sum.inr Sum.inr)
      (W.submatrix Sum.inr id) R) hc' hp'

theorem full_gram_bound_of_blocks_proof
    (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ)
    (hc : (firstBlock K W R).PosSemidef)
    (hp : (secondBlock K W R).PosSemidef)
    (y : h ⊕ h → ℝ) :
    normSq (action (goodCross K W) y) ≤ 196 * normSq y :=
  full_gram_bound (goodCross K W) (complementaryPSD_of_blocks K W R hc hp) y

#check Conway99Formal.TwoSidedSchur.full_gram_bound_of_blocks_proof
#print axioms Conway99Formal.TwoSidedSchur.full_gram_bound_of_blocks_proof

end LiteralBlocks

end Conway99Formal.TwoSidedSchur

theorem solution {g h : Type*} [Fintype g] [Fintype h] [DecidableEq g] [DecidableEq h] (K : Matrix (g ⊕ h) (g ⊕ h) ℝ) (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ) (hc : (Conway99Formal.TwoSidedSchur.firstBlock K W R).PosSemidef) (hp : (Conway99Formal.TwoSidedSchur.secondBlock K W R).PosSemidef) (y : h ⊕ h → ℝ) : Conway99Formal.TwoSidedSchur.normSq (Conway99Formal.TwoSidedSchur.action (Conway99Formal.TwoSidedSchur.goodCross K W) y) ≤ 196 * Conway99Formal.TwoSidedSchur.normSq y := by
  exact Conway99Formal.TwoSidedSchur.full_gram_bound_of_blocks_proof K W R hc hp y

#check _root_.solution
#print axioms _root_.solution
