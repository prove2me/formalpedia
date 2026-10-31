-- Prove2me | solution 1 for BSPConvex.CMM.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:48:17.73697+00:00
-- url     : https://prove2.me/submissions/6b15db13-698e-4391-8be6-f77b2ec5eacf

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model
import Theorems.Thm_BSPConvex_CMM_lemma_6
import Theorems.Thm_BSPConvex_CMM_g_identity

open Matrix
open scoped MatrixOrder

namespace BSPCMMAuxG
open BSPConvex.CMM

/-- `S(q)` is positive definite on the open simplex. -/
theorem S_posDef {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ intSimplex m) : (Smat x).PosDef := by
  obtain ⟨hx0, hx1⟩ := hx
  have hH : (Smat x).IsHermitian := by
    ext i j
    simp only [Smat, conjTranspose_apply, Matrix.sub_apply, diagonal_apply, vecMulVec_apply,
      star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      ring
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro v hv
  set S := ∑ j, x j * v j with hS
  have e1 : ∀ i, (Smat x *ᵥ v) i = x i * v i - x i * S := by
    intro i
    rw [Smat, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
    congr 1
    simp only [mulVec, dotProduct, vecMulVec_apply]
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e2 : ∀ i, v i * (x i * v i - x i * S) = x i * v i ^ 2 - (x i * v i) * S := by
    intro i; ring
  have key : star v ⬝ᵥ (Smat x *ᵥ v) = ∑ i, x i * v i ^ 2 - S ^ 2 := by
    rw [star_trivial]
    simp only [dotProduct, e1]
    rw [Finset.sum_congr rfl (fun i _ => e2 i), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hS,
      sq]
  rw [key]
  have hcs : S ^ 2 ≤ (∑ i, x i) * ∑ i, x i * v i ^ 2 := by
    rw [hS]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; exact (hx0 i).le
    · intro i _; exact mul_nonneg (hx0 i).le (sq_nonneg _)
    · intro i _; apply le_of_eq; ring
  have hq : 0 < ∑ i, x i * v i ^ 2 := by
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    calc (0 : ℝ) < x k * v k ^ 2 := mul_pos (hx0 k) (by positivity)
      _ ≤ ∑ i, x i * v i ^ 2 :=
        Finset.single_le_sum (f := fun i => x i * v i ^ 2)
          (fun i _ => mul_nonneg (hx0 i).le (sq_nonneg _)) (Finset.mem_univ k)
  have : (∑ i, x i) * ∑ i, x i * v i ^ 2 < ∑ i, x i * v i ^ 2 := by
    calc (∑ i, x i) * ∑ i, x i * v i ^ 2 < 1 * ∑ i, x i * v i ^ 2 :=
          mul_lt_mul_of_pos_right hx1 hq
      _ = ∑ i, x i * v i ^ 2 := one_mul _
  linarith

theorem sqrtSig_psd {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) :
    (CFC.sqrt Sig).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sig)

theorem sqrtSig_unit {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef) :
    IsUnit (CFC.sqrt Sig) :=
  (CFC.isUnit_sqrt_iff Sig hSig.posSemidef.nonneg).2 hSig.isUnit

theorem T_posDef {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) : (Tmat Sig q).PosDef := by
  have hs := sqrtSig_psd Sig
  have hH : (CFC.sqrt Sig)ᴴ = CFC.sqrt Sig := hs.isHermitian.eq
  have hpsd := (S_posDef q hq).posSemidef.conjTranspose_mul_mul_same (CFC.sqrt Sig)
  rw [hH] at hpsd
  change (CFC.sqrt Sig * Smat q * CFC.sqrt Sig).PosDef
  rw [hpsd.posDef_iff_isUnit]
  exact ((sqrtSig_unit Sig hSig).mul (S_posDef q hq).isUnit).mul (sqrtSig_unit Sig hSig)

theorem sqrtT_posDef {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) : (CFC.sqrt (Tmat Sig q)).PosDef := by
  have hT := T_posDef Sig hSig q hq
  have hpsd : (CFC.sqrt (Tmat Sig q)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)
  rw [hpsd.posDef_iff_isUnit]
  exact (CFC.isUnit_sqrt_iff _ hT.posSemidef.nonneg).2 hT.isUnit

/-- `tr(S(q) M) = qᵀ diag M − qᵀ M q` for any matrix `M`. -/
theorem trace_S_mul {m : ℕ} (q : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (Smat q * M) = q ⬝ᵥ Matrix.diag M - q ⬝ᵥ (M *ᵥ q) := by
  rw [Matrix.trace_mul_comm, Smat, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  · simp [Matrix.trace, Matrix.mul_diagonal, dotProduct, mul_comm]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
      mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring

theorem trace_SM {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (q : Fin m → ℝ) (hq : q ∈ intSimplex m) :
    Matrix.trace (Smat q * Mmat Sig q) = Matrix.trace (CFC.sqrt (Tmat Sig q)) := by
  set s := CFC.sqrt Sig
  set r := CFC.sqrt (Tmat Sig q)
  have hr : IsUnit r.det := (Matrix.isUnit_iff_isUnit_det r).1 (sqrtT_posDef Sig hSig q hq).isUnit
  have hrr : r * r = Tmat Sig q := CFC.sqrt_mul_sqrt_self _ (T_posDef Sig hSig q hq).posSemidef.nonneg
  have h1 : Smat q * Mmat Sig q = (Smat q * s * r⁻¹) * s := by
    simp only [Mmat, s, r, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : s * (Smat q * s * r⁻¹) = r * (r * r⁻¹) := by
    rw [← Matrix.mul_assoc r r, hrr]
    simp only [Tmat, s, Matrix.mul_assoc]
  rw [h2, Matrix.mul_nonsing_inv _ hr, Matrix.mul_one]


theorem simplex_convex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

theorem intSimplex_convex (m : ℕ) : Convex ℝ (intSimplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx.1 i)) (mul_nonneg hb (hy.1 i).le)
    · subst ha'
      have : b = 1 := by linarith
      subst this; simpa using hy.1 i
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_lt_mul_of_pos_left hx.2 ha', mul_le_mul_of_nonneg_left hy.2.le hb]
    · subst ha'
      have : b = 1 := by linarith
      subst this; simpa using hy.2

theorem intSimplex_subset {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ intSimplex m) : x ∈ simplex m :=
  ⟨fun i => (hx.1 i).le, hx.2.le⟩

theorem sym_dot {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ} (hX : Xᵀ = X) (a b : Fin m → ℝ) :
    a ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (X *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hX, dotProduct_comm]

/-- Variational characterisation of `vᵀ X⁻¹ v` for positive definite `X`. -/
theorem variational {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.PosDef) (u v : Fin m → ℝ) :
    2 * (u ⬝ᵥ v) - u ⬝ᵥ (X *ᵥ u) ≤ v ⬝ᵥ (X⁻¹ *ᵥ v) := by
  have hXt : Xᵀ = X := by
    have := hX.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX.isUnit
  have hXR : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hRt : (X⁻¹)ᵀ = X⁻¹ := by rw [Matrix.transpose_nonsing_inv, hXt]
  have h0 := hX.posSemidef.dotProduct_mulVec_nonneg (u - X⁻¹ *ᵥ v)
  rw [star_trivial] at h0
  have e1 : X *ᵥ (X⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, hXR, one_mulVec]
  rw [mulVec_sub, e1, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    sym_dot hXt (X⁻¹ *ᵥ v) u, dotProduct_comm (X⁻¹ *ᵥ v) v] at h0
  simp only [e1] at h0
  linarith

theorem variational_eq {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.PosDef) (v : Fin m → ℝ) :
    2 * ((X⁻¹ *ᵥ v) ⬝ᵥ v) - (X⁻¹ *ᵥ v) ⬝ᵥ (X *ᵥ (X⁻¹ *ᵥ v)) = v ⬝ᵥ (X⁻¹ *ᵥ v) := by
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX.isUnit
  have hXR : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have e1 : X *ᵥ (X⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, hXR, one_mulVec]
  rw [e1, dotProduct_comm (X⁻¹ *ᵥ v) v]
  ring

/-- `h(q) = qᵀ M(q) q = (Σ^{1/2} q)ᵀ (T(q)^{1/2})⁻¹ (Σ^{1/2} q)`. -/
theorem h_eq {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) :
    q ⬝ᵥ (Mmat Sig q *ᵥ q) =
      (CFC.sqrt Sig *ᵥ q) ⬝ᵥ ((CFC.sqrt (Tmat Sig q))⁻¹ *ᵥ (CFC.sqrt Sig *ᵥ q)) := by
  have hst : (CFC.sqrt Sig)ᵀ = CFC.sqrt Sig := by
    have := (sqrtSig_psd Sig).isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [Mmat, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hst]

theorem h_convex {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (x y : Fin m → ℝ) (hx : x ∈ intSimplex m) (hy : y ∈ intSimplex m)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (a • x + (1 - a) • y) ⬝ᵥ (Mmat Sig (a • x + (1 - a) • y) *ᵥ (a • x + (1 - a) • y)) ≤
      a * (x ⬝ᵥ (Mmat Sig x *ᵥ x)) + (1 - a) * (y ⬝ᵥ (Mmat Sig y *ᵥ y)) := by
  set z := a • x + (1 - a) • y with hz
  have hzI : z ∈ intSimplex m :=
    intSimplex_convex m hx hy ha.1 (by linarith [ha.2]) (by ring)
  set s := CFC.sqrt Sig
  set X := CFC.sqrt (Tmat Sig z)
  set X1 := CFC.sqrt (Tmat Sig x)
  set X2 := CFC.sqrt (Tmat Sig y)
  have hX : X.PosDef := sqrtT_posDef Sig hSig z hzI
  have hX1 : X1.PosDef := sqrtT_posDef Sig hSig x hx
  have hX2 : X2.PosDef := sqrtT_posDef Sig hSig y hy
  have hL := BSPConvex.CMM.lemma_6 Sig hSig.posSemidef x y (intSimplex_subset hx)
    (intSimplex_subset hy) a ha
  rw [h_eq, h_eq, h_eq]
  set w := s *ᵥ z
  set w1 := s *ᵥ x
  set w2 := s *ᵥ y
  have hw : w = a • w1 + (1 - a) • w2 := by
    simp only [w, w1, w2, hz, mulVec_add, mulVec_smul]
  set u := X⁻¹ *ᵥ w
  have e0 := variational_eq hX w
  have hle : u ⬝ᵥ ((a • X1 + (1 - a) • X2) *ᵥ u) ≤ u ⬝ᵥ (X *ᵥ u) := by
    have := hL.dotProduct_mulVec_nonneg u
    rw [star_trivial, sub_mulVec, dotProduct_sub] at this
    linarith
  have v1 := variational hX1 u w1
  have v2 := variational hX2 u w2
  have hexp : u ⬝ᵥ ((a • X1 + (1 - a) • X2) *ᵥ u) =
      a * (u ⬝ᵥ (X1 *ᵥ u)) + (1 - a) * (u ⬝ᵥ (X2 *ᵥ u)) := by
    rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have hexp2 : u ⬝ᵥ w = a * (u ⬝ᵥ w1) + (1 - a) * (u ⬝ᵥ w2) := by
    rw [hw, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have ha0 : 0 ≤ a := ha.1
  have ha1 : 0 ≤ 1 - a := by linarith [ha.2]
  have k1 := mul_le_mul_of_nonneg_left v1 ha0
  have k2 := mul_le_mul_of_nonneg_left v2 ha1
  linarith

theorem trace_concave {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (x y : Fin m → ℝ) (hx : x ∈ intSimplex m) (hy : y ∈ intSimplex m)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    a * Matrix.trace (CFC.sqrt (Tmat Sig x)) + (1 - a) * Matrix.trace (CFC.sqrt (Tmat Sig y)) ≤
      Matrix.trace (CFC.sqrt (Tmat Sig (a • x + (1 - a) • y))) := by
  have hL := BSPConvex.CMM.lemma_6 Sig hSig.posSemidef x y (intSimplex_subset hx)
    (intSimplex_subset hy) a ha
  have := hL.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul] at this
  linarith

end BSPCMMAuxG

open BSPConvex.CMM in
theorem solution {m : ℕ} (ω c : Fin m → ℝ) (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef) :
    ConcaveOn ℝ (intSimplex m) (profit ω c Sig) := by
  refine ⟨BSPCMMAuxG.intSimplex_convex m, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  have haI : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  set z := a • x + (1 - a) • y with hz
  have hzI : z ∈ intSimplex m :=
    BSPCMMAuxG.intSimplex_convex m hx hy ha hb (by ring)
  have hp : ∀ q, q ∈ intSimplex m → profit ω c Sig q =
      q ⬝ᵥ (ω - c) + (1 / 2 : ℝ) * Matrix.trace (CFC.sqrt (Tmat Sig q)) -
        (1 / 2 : ℝ) * (q ⬝ᵥ (Mmat Sig q *ᵥ q)) := by
    intro q hq
    have h := g_identity Sig hSig q hq
    have h' := h.1.symm.trans h.2
    simp only [profit]
    linarith
  rw [smul_eq_mul, smul_eq_mul, hp x hx, hp y hy, hp z hzI]
  have hlin : z ⬝ᵥ (ω - c) = a * (x ⬝ᵥ (ω - c)) + (1 - a) * (y ⬝ᵥ (ω - c)) := by
    rw [hz, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have ht := BSPCMMAuxG.trace_concave Sig hSig x y hx hy a haI
  have hh := BSPCMMAuxG.h_convex Sig hSig x y hx hy a haI
  rw [← hz] at ht hh
  nlinarith
