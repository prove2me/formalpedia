-- Prove2me | solution 1 for BenignDegen.lemma_C_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:38:58.412809+00:00
-- url     : https://prove2.me/submissions/95849abf-0741-4472-8502-f6609377a960

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace Aux_BenignDegen_C6
open BenignDegen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma symm_of_psd (a : Matrix ι ι ℝ) (ha : a.PosSemidef) (i j : ι) : a i j = a j i := by
  have := ha.1.apply j i
  rw [star_trivial] at this
  exact this

lemma dot_symm (a : Matrix ι ι ℝ) (ha : a.PosSemidef) (x y : ι → ℝ) :
    x ⬝ᵥ (a *ᵥ y) = y ⬝ᵥ (a *ᵥ x) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [symm_of_psd a ha j i]; ring

lemma quad_nonneg (a : Matrix ι ι ℝ) (ha : a.PosSemidef) (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (a *ᵥ x) := by
  have := (posSemidef_iff_dotProduct_mulVec.1 ha).2 x
  simpa using this

lemma cs_form (a : Matrix ι ι ℝ) (ha : a.PosSemidef) (x y : ι → ℝ) :
    (x ⬝ᵥ (a *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (a *ᵥ x)) * (y ⬝ᵥ (a *ᵥ y)) := by
  have hq : ∀ t : ℝ, 0 ≤ x ⬝ᵥ (a *ᵥ x) + 2 * t * (x ⬝ᵥ (a *ᵥ y)) + t ^ 2 * (y ⬝ᵥ (a *ᵥ y)) := by
    intro t
    have h := quad_nonneg a ha (x + t • y)
    have e : (x + t • y) ⬝ᵥ (a *ᵥ (x + t • y)) = x ⬝ᵥ (a *ᵥ x) + 2 * t * (x ⬝ᵥ (a *ᵥ y))
        + t ^ 2 * (y ⬝ᵥ (a *ᵥ y)) := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      rw [dot_symm a ha y x]; ring
    linarith
  set p := x ⬝ᵥ (a *ᵥ x)
  set r := x ⬝ᵥ (a *ᵥ y)
  set s := y ⬝ᵥ (a *ᵥ y)
  have hs0 : 0 ≤ s := quad_nonneg a ha y
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- s = 0 forces r = 0
    have hr : r = 0 := by
      by_contra hr
      have h := hq (-(p + 1) / (2 * r))
      rw [← hs] at h
      have e : p + 2 * (-(p + 1) / (2 * r)) * r + (-(p + 1) / (2 * r)) ^ 2 * 0 = -1 := by
        field_simp <;> ring
      linarith
    rw [hr, ← hs]; simp
  · have := hq (-r / s)
    have e : p + 2 * (-r / s) * r + (-r / s) ^ 2 * s = p - r ^ 2 / s := by
      field_simp; ring
    rw [e] at this
    have : r ^ 2 / s ≤ p := by linarith
    rw [div_le_iff₀ hs] at this
    linarith

lemma op_bound (A : SymMat ι) (w : ι → ℝ) :
    w ⬝ᵥ (A.toMat *ᵥ w) ≤ opNorm A * (w ⬝ᵥ w) := by
  set W : EuclideanSpace ℝ ι := WithLp.toLp 2 w
  have h1 : w ⬝ᵥ (A.toMat *ᵥ w) = inner ℝ W (act A W) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [act, W, dotProduct_comm]
  have h2 : inner ℝ W (act A W) ≤ ‖W‖ * ‖act A W‖ := real_inner_le_norm _ _
  have h3 : ‖act A W‖ ≤ opNorm A * ‖W‖ := by
    unfold opNorm
    exact (LinearMap.toContinuousLinearMap (act A)).le_opNorm W
  have h4 : ‖W‖ ^ 2 = w ⬝ᵥ w := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [W, dotProduct, sq]
  have h5 : 0 ≤ ‖W‖ := norm_nonneg _
  rw [h1]
  calc inner ℝ W (act A W) ≤ ‖W‖ * ‖act A W‖ := h2
    _ ≤ ‖W‖ * (opNorm A * ‖W‖) := mul_le_mul_of_nonneg_left h3 h5
    _ = opNorm A * (w ⬝ᵥ w) := by rw [← h4]; ring

lemma key (A : SymMat ι) (hA : A ∈ psdCone ι) (u : ι → ℝ) :
    (A.toMat *ᵥ u) ⬝ᵥ (A.toMat *ᵥ u) ≤ opNorm A * (u ⬝ᵥ (A.toMat *ᵥ u)) := by
  have ha : A.toMat.PosSemidef := hA
  set a := A.toMat
  set v := a *ᵥ u
  have hN : 0 ≤ opNorm A := norm_nonneg _
  have hcs := cs_form a ha u v
  have e1 : u ⬝ᵥ (a *ᵥ v) = v ⬝ᵥ v := by
    rw [dot_symm a ha u v]
  rw [e1] at hcs
  have hb := op_bound A v
  have hq := quad_nonneg a ha u
  have hvv : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  rcases eq_or_lt_of_le hvv with h0 | hpos
  · rw [← h0]; exact mul_nonneg hN hq
  · have : (v ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ (a *ᵥ u)) * (opNorm A * (v ⬝ᵥ v)) :=
      hcs.trans (mul_le_mul_of_nonneg_left hb hq)
    nlinarith

end Aux_BenignDegen_C6

open BenignDegen Aux_BenignDegen_C6 MatrixOrder in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (A B : SymMat ι)
    (hA : A ∈ psdCone ι) (hB : B ∈ psdCone ι) :
    frob (A.toMat * B.toMat) ^ 2 ≤ opNorm A * opNorm B * ⟪A, B⟫ := by
  have ha : A.toMat.PosSemidef := hA
  have hb : B.toMat.PosSemidef := hB
  set a := A.toMat with hadef
  set b := B.toMat with hbdef
  have hNA : 0 ≤ opNorm A := norm_nonneg _
  have hNB : 0 ≤ opNorm B := norm_nonneg _
  let col : ι → ι → ℝ := fun j i => b i j
  -- frobenius norm as a sum over columns
  have hfrob : frob (a * b) ^ 2 = ∑ j, (a *ᵥ col j) ⬝ᵥ (a *ᵥ col j) := by
    unfold frob
    rw [Real.sq_sqrt (by positivity)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    simp only [dotProduct, sq]
    apply Finset.sum_congr rfl; intro i _
    simp [Matrix.mul_apply, mulVec, dotProduct, col]
  have hstep1 : frob (a * b) ^ 2 ≤ opNorm A * ∑ j, col j ⬝ᵥ (a *ᵥ col j) := by
    rw [hfrob, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => key A hA (col j))
  -- ∑ col_j ⬝ a col_j = tr(a b b)
  have htr1 : ∑ j, col j ⬝ᵥ (a *ᵥ col j) = (a * (b * b)).trace := by
    simp only [trace, diag_apply, Matrix.mul_apply, dotProduct, mulVec, col, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    rw [symm_of_psd b hb i j]; ring
  -- D = ‖B‖ b - b b is PSD
  set D := opNorm B • b - b * b with hD
  have hDpsd : D.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    constructor
    · unfold IsHermitian
      rw [hD, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, hb.1.eq, star_trivial]
    · intro x
      have eD : D *ᵥ x = opNorm B • (b *ᵥ x) - b *ᵥ (b *ᵥ x) := by
        rw [hD, sub_mulVec, smul_mulVec, mulVec_mulVec]
      rw [star_trivial, eD, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      have h1 := key B hB x
      have e : x ⬝ᵥ (b *ᵥ (b *ᵥ x)) = (b *ᵥ x) ⬝ᵥ (b *ᵥ x) := by
        rw [dot_symm b hb x (b *ᵥ x)]
      rw [e]
      linarith
  -- tr(a D) ≥ 0 via a square root of a
  have htrD : 0 ≤ (a * D).trace := by
    have ha0 : 0 ≤ a := ha.nonneg
    have hX := CFC.sqrt_mul_sqrt_self a ha0
    have hXsa : IsSelfAdjoint (CFC.sqrt a) := (CFC.sqrt_nonneg a).isSelfAdjoint
    set X := CFC.sqrt a with hXdef
    have hXh : Xᴴ = X := hXsa
    rw [← hX, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    have := (hDpsd.conjTranspose_mul_mul_same X).trace_nonneg
    rw [hXh, Matrix.mul_assoc] at this
    exact this
  have hstep2 : (a * (b * b)).trace ≤ opNorm B * (a * b).trace := by
    have : (a * D).trace = opNorm B * (a * b).trace - (a * (b * b)).trace := by
      rw [hD, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul, smul_eq_mul]
    linarith
  have hinner : ⟪A, B⟫ = (a * b).trace := by
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fintype.sum_prod_type, trace, diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [star_trivial, hadef, hbdef, SymMat.toMat]
    have := symm_of_psd b hb j i
    simp only [hbdef, SymMat.toMat] at this
    rw [this]; ring
  rw [hinner]
  calc frob (a * b) ^ 2 ≤ opNorm A * ∑ j, col j ⬝ᵥ (a *ᵥ col j) := hstep1
    _ = opNorm A * (a * (b * b)).trace := by rw [htr1]
    _ ≤ opNorm A * (opNorm B * (a * b).trace) := mul_le_mul_of_nonneg_left hstep2 hNA
    _ = opNorm A * opNorm B * (a * b).trace := by ring
