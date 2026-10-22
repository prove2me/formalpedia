-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.bookend_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:39:35.154748+00:00
-- url     : https://prove2.me/submissions/4c727caa-6d78-4c89-86d6-009d50878265

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

set_option autoImplicit false
open Matrix GGHRSW.ColoredMatrix

section QQ

variable {p : ℕ}

theorem qqf_tele {R : Type*} [Monoid R] (n : ℕ) :
    ∀ (G : Fin (n + 1) → Rˣ) (X : Fin n → R),
      (List.ofFn fun i : Fin n => (↑(G i.castSucc) : R) * X i * ↑(G i.succ)⁻¹).prod =
        ↑(G 0) * (List.ofFn X).prod * ↑(G (Fin.last n))⁻¹ := by
  induction n with
  | zero =>
    intro G X
    simp
  | succ n ih =>
    intro G X
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have := ih (fun i => G i.succ) (fun i => X i.succ)
    simp only [← Fin.succ_castSucc]
    rw [this]
    simp only [Fin.succ_last, Fin.castSucc_zero, mul_assoc, Units.inv_mul_cancel_left]


theorem qqf_blockDiag_mul {r : ℕ} (d d' : Fin r → ZMod p) (B B' : Matrix (Fin 5) (Fin 5) (ZMod p)) :
    GGHRSW.ColoredMatrix.blockDiag d B * GGHRSW.ColoredMatrix.blockDiag d' B' = GGHRSW.ColoredMatrix.blockDiag (fun j => d j * d' j) (B * B') := by
  unfold GGHRSW.ColoredMatrix.blockDiag
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.diagonal_mul_diagonal]

theorem qqf_blockDiag_one {r : ℕ} :
    GGHRSW.ColoredMatrix.blockDiag (fun _ : Fin r => (1 : ZMod p)) (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) = 1 := by
  unfold GGHRSW.ColoredMatrix.blockDiag
  rw [Matrix.reindex_apply]
  simp [Matrix.diagonal_one, Matrix.fromBlocks_one]

theorem qqf_blockDiag_prod {r : ℕ} (n : ℕ) :
    ∀ (d : Fin n → Fin r → ZMod p) (B : Fin n → Matrix (Fin 5) (Fin 5) (ZMod p)),
      (List.ofFn fun i => GGHRSW.ColoredMatrix.blockDiag (d i) (B i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, d i j) (List.ofFn B).prod := by
  induction n with
  | zero =>
    intro d B
    simp [qqf_blockDiag_one]
  | succ n ih =>
    intro d B
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, qqf_blockDiag_mul]
    simp [Fin.prod_univ_succ]

theorem qqf_smul_prod {R : Type*} [CommSemiring R] {m : ℕ} (n : ℕ) :
    ∀ (c : Fin n → R) (M : Fin n → Matrix (Fin m) (Fin m) R),
      (List.ofFn fun i => c i • M i).prod = (∏ i, c i) • (List.ofFn M).prod := by
  induction n with
  | zero =>
    intro c M
    simp
  | succ n ih =>
    intro c M
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, smul_mul_smul_comm,
      Fin.prod_univ_succ]


theorem qqf_bd_ll {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (k k' : Fin r) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.castAdd 5 k) (Fin.castAdd 5 k') = diagonal d k k' := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

theorem qqf_bd_lr {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (k : Fin r) (k' : Fin 5) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.castAdd 5 k) (Fin.natAdd r k') = 0 := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

theorem qqf_bd_rl {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (k : Fin 5) (k' : Fin r) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.natAdd r k) (Fin.castAdd 5 k') = 0 := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

theorem qqf_bd_rr {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (k k' : Fin 5) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.natAdd r k) (Fin.natAdd r k') = B k k' := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

theorem qqf_sandwich {m : ℕ} (e : Fin (2 * m) → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (mid low : Fin m → ZMod p) (star star' : Fin 5 → ZMod p) :
    (bookendRow mid star * GGHRSW.ColoredMatrix.blockDiag e B * bookendCol low star') 0 0 =
      star ⬝ᵥ (B *ᵥ star') := by
  simp only [Matrix.mul_apply, Fin.sum_univ_add (a := 2 * m) (b := 5)]
  simp [qqf_bd_ll, qqf_bd_lr, qqf_bd_rl, qqf_bd_rr, bookendRow, bookendCol, Fin.sum_univ_succ]
  rw [Finset.sum_eq_zero, zero_add]
  · simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x _
    split_ifs with h
    · rw [Finset.sum_eq_zero, zero_mul]
      intro x1 _
      split_ifs with h1
      · rfl
      · rw [diagonal_apply]
        by_cases hx : x1 = x
        · exact absurd (hx ▸ h) h1
        · simp [hx]
    · rfl

end QQ

theorem solution (p : ℕ) [Fact p.Prime] (bp : BP) (ω : Sample p bp)
    (b : Fin bp.n → Bool) :
    (sTil ω * (List.ofFn fun i => DTil ω i (b i)).prod * tTil ω) 0 0 =
        (∏ i, alpha bp ω.γ i (b i)) *
          (ω.sStar ⬝ᵥ
            ((List.ofFn fun i => (bp.A i (b i)).permMatrix (ZMod p)).prod *ᵥ ω.tStar)) ∧
      (s'Til ω * (List.ofFn fun i => D'Til ω i (b i)).prod * t'Til ω) 0 0 =
        (∏ i, alpha' bp ω.γ i (b i)) * (ω.s'Star ⬝ᵥ ω.t'Star) := by
  constructor
  · have hT : sTil ω * (List.ofFn fun i => DTil ω i (b i)).prod * tTil ω =
        bookendRow ω.sMid ω.sStar * (List.ofFn fun i => Dmat ω i (b i)).prod *
          bookendCol ω.tLow ω.tStar := by
      unfold sTil tTil DTil
      rw [qqf_tele bp.n ω.R (fun i => Dmat ω i (b i))]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
      have hc : ∀ c : Matrix (Fin (NDim bp.n)) (Fin 1) (ZMod p),
          Units.val ((ω.R (Fin.last bp.n))⁻¹) *
            (Units.val (ω.R (Fin.last bp.n)) * c) = c := fun c => by
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      erw [hc]
    rw [hT]
    have hD : (List.ofFn fun i => Dmat ω i (b i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, ω.d i (b i) j)
          ((∏ i, alpha bp ω.γ i (b i)) •
            (List.ofFn fun i => (bp.A i (b i)).permMatrix (ZMod p)).prod) := by
      unfold Dmat
      rw [qqf_blockDiag_prod bp.n (fun i => ω.d i (b i))
        (fun i => alpha bp ω.γ i (b i) • (bp.A i (b i)).permMatrix (ZMod p)),
        qqf_smul_prod]
    rw [hD, qqf_sandwich, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  · have hT : s'Til ω * (List.ofFn fun i => D'Til ω i (b i)).prod * t'Til ω =
        bookendRow ω.s'Mid ω.s'Star * (List.ofFn fun i => D'mat ω i (b i)).prod *
          bookendCol ω.t'Low ω.t'Star := by
      unfold s'Til t'Til D'Til
      rw [qqf_tele bp.n ω.R' (fun i => D'mat ω i (b i))]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
      have hc : ∀ c : Matrix (Fin (NDim bp.n)) (Fin 1) (ZMod p),
          Units.val ((ω.R' (Fin.last bp.n))⁻¹) *
            (Units.val (ω.R' (Fin.last bp.n)) * c) = c := fun c => by
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      erw [hc]
    rw [hT]
    have hD : (List.ofFn fun i => D'mat ω i (b i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, ω.d' i (b i) j)
          ((∏ i, alpha' bp ω.γ i (b i)) •
            (List.ofFn fun _ : Fin bp.n => (1 : Matrix (Fin 5) (Fin 5) (ZMod p))).prod) := by
      unfold D'mat
      rw [qqf_blockDiag_prod bp.n (fun i => ω.d' i (b i))
        (fun i => alpha' bp ω.γ i (b i) • (1 : Matrix (Fin 5) (Fin 5) (ZMod p))),
        qqf_smul_prod]
    rw [hD, qqf_sandwich, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp
