-- Prove2me | solution 1 for BSPConvex.CMM.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:44:45.010229+00:00
-- url     : https://prove2.me/submissions/9c2a2645-aa03-48cd-a623-a35d42d82f5d

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model
import Theorems.Thm_BSPConvex_CMM_S_T_loewner_concave
import Theorems.Thm_BSPConvex_CMM_S_posSemidef

open Matrix
open scoped MatrixOrder

namespace BSPCMMAux6

/-- Operator monotonicity of the square root for real matrices. -/
theorem sqrt_mono {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  have hB : 0 ≤ B := hA.trans hAB
  set a := CFC.sqrt A with ha_def
  set b := CFC.sqrt B with hb_def
  have ha : a.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)
  have hb : b.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B)
  have haa : a * a = A := CFC.sqrt_mul_sqrt_self A hA
  have hbb : b * b = B := CFC.sqrt_mul_sqrt_self B hB
  have hBA : (B - A).PosSemidef := hAB
  have hD : (b - a).IsHermitian := hb.1.sub ha.1
  rw [Matrix.le_iff, hD.posSemidef_iff_eigenvalues_nonneg]
  intro j
  set v : n → ℝ := ⇑(hD.eigenvectorBasis j) with hv_def
  set μ := hD.eigenvalues j with hμ
  have hv : (b - a) *ᵥ v = μ • v := hD.mulVec_eigenvectorBasis j
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := (hD.eigenvectorBasis).orthonormal.ne_zero j
    apply h1
    ext i
    have := congrFun h i
    simpa [hv_def] using this
  have hTs : (b - a)ᵀ = b - a := by
    have := hD.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hsplit : B - A = (b - a) * b + a * (b - a) := by
    rw [← haa, ← hbb]; noncomm_ring
  have key : v ⬝ᵥ ((B - A) *ᵥ v) = μ * (v ⬝ᵥ (b *ᵥ v) + v ⬝ᵥ (a *ᵥ v)) := by
    rw [hsplit, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, dotProduct_add,
      dotProduct_mulVec v (b - a), ← mulVec_transpose, hTs, hv, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  have h0 : 0 ≤ v ⬝ᵥ ((B - A) *ᵥ v) := by
    have := hBA.dotProduct_mulVec_nonneg v
    simpa using this
  have sa : 0 ≤ v ⬝ᵥ (a *ᵥ v) := by simpa using ha.dotProduct_mulVec_nonneg v
  have sb : 0 ≤ v ⬝ᵥ (b *ᵥ v) := by simpa using hb.dotProduct_mulVec_nonneg v
  show 0 ≤ μ
  by_contra hneg'
  have hneg : μ < 0 := lt_of_not_ge hneg'
  have hsum : v ⬝ᵥ (b *ᵥ v) + v ⬝ᵥ (a *ᵥ v) ≤ 0 := by
    by_contra hc'
    have hc := lt_of_not_ge hc'
    have : μ * (v ⬝ᵥ (b *ᵥ v) + v ⬝ᵥ (a *ᵥ v)) < 0 := mul_neg_of_neg_of_pos hneg hc
    linarith
  have ea : v ⬝ᵥ (a *ᵥ v) = 0 := by linarith
  have eb : v ⬝ᵥ (b *ᵥ v) = 0 := by linarith
  have ha0 : a *ᵥ v = 0 := (Matrix.PosSemidef.dotProduct_mulVec_zero_iff ha v).1 (by simpa using ea)
  have hb0 : b *ᵥ v = 0 := (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hb v).1 (by simpa using eb)
  have : μ • v = 0 := by rw [← hv, sub_mulVec, ha0, hb0, sub_zero]
  rcases smul_eq_zero.1 this with h | h
  · exact (lt_irrefl _ (h ▸ hneg))
  · exact hv0 h

/-- Operator concavity of the square root for real matrices, in the form used in Lemma 6. -/
theorem sqrt_concave {n : Type} [Fintype n] [DecidableEq n] {A B X : Matrix n n ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hX : lam • A + (1 - lam) • B ≤ X) :
    lam • CFC.sqrt A + (1 - lam) • CFC.sqrt B ≤ CFC.sqrt X := by
  set a := CFC.sqrt A
  set b := CFC.sqrt B
  have ha : 0 ≤ a := CFC.sqrt_nonneg A
  have hb : 0 ≤ b := CFC.sqrt_nonneg B
  have haa : a * a = A := CFC.sqrt_mul_sqrt_self A hA
  have hbb : b * b = B := CFC.sqrt_mul_sqrt_self B hB
  have hl0 : 0 ≤ lam := hlam.1
  have hl1 : 0 ≤ 1 - lam := by linarith [hlam.2]
  set C := lam • a + (1 - lam) • b with hC
  have hC0 : 0 ≤ C := add_nonneg (smul_nonneg hl0 ha) (smul_nonneg hl1 hb)
  have hdiff : lam • A + (1 - lam) • B - C ^ 2 = (lam * (1 - lam)) • ((a - b) * (a - b)) := by
    rw [← haa, ← hbb, hC, sq]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub,
      smul_add, smul_sub]
    module
  have hpsd : 0 ≤ (lam * (1 - lam)) • ((a - b) * (a - b)) := by
    have hH : (a - b).IsHermitian :=
      (Matrix.nonneg_iff_posSemidef.1 ha).1.sub (Matrix.nonneg_iff_posSemidef.1 hb).1
    have : ((a - b)ᴴ * (a - b)).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
    rw [hH.eq] at this
    exact Matrix.nonneg_iff_posSemidef.2 (this.smul (mul_nonneg hl0 hl1))
  have hC2 : C ^ 2 ≤ X := by
    have : C ^ 2 ≤ lam • A + (1 - lam) • B := by
      rw [← sub_nonneg, hdiff]; exact hpsd
    exact this.trans hX
  have hCsq : 0 ≤ C ^ 2 := by
    have hH : C.IsHermitian := (Matrix.nonneg_iff_posSemidef.1 hC0).1
    have : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
    rw [hH.eq, ← sq] at this
    exact Matrix.nonneg_iff_posSemidef.2 this
  have := sqrt_mono hCsq hC2
  rwa [CFC.sqrt_sq C hC0] at this

end BSPCMMAux6

open BSPConvex.CMM in
theorem BSPCMMAux6.T_nonneg {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef)
    (x : Fin m → ℝ) (hx : x ∈ simplex m) : 0 ≤ Tmat Sig x := by
  have hs : (CFC.sqrt Sig).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sig)
  have hH : (CFC.sqrt Sig)ᴴ = CFC.sqrt Sig := hs.isHermitian.eq
  have := (S_posSemidef x hx).conjTranspose_mul_mul_same (CFC.sqrt Sig)
  rw [hH] at this
  exact Matrix.nonneg_iff_posSemidef.2 this

open BSPConvex.CMM in
theorem solution {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosSemidef)
    (x y : Fin m → ℝ) (hx : x ∈ simplex m) (hy : y ∈ simplex m)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (CFC.sqrt (Tmat Sig (lam • x + (1 - lam) • y)) -
      (lam • CFC.sqrt (Tmat Sig x) + (1 - lam) • CFC.sqrt (Tmat Sig y))).PosSemidef := by
  have hT := (S_T_loewner_concave Sig hSig x y lam hlam).2.2
  exact BSPCMMAux6.sqrt_concave (BSPCMMAux6.T_nonneg Sig hSig x hx)
    (BSPCMMAux6.T_nonneg Sig hSig y hy) lam hlam hT
