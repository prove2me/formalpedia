-- Prove2me | solution 1 for Formalism.GM.lieMat_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:26.951437+00:00
-- url     : https://prove2.me/submissions/c75d2389-f44b-4939-8560-f752be001c3b

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff
import Theorems.Thm_Formalism_GM_DetBound_coeff_le_gaussR
import Theorems.Thm_Formalism_GM_DetBound_gaussR_sum_le
import Theorems.Thm_Formalism_GM_DetBound_gaussR_C
import Theorems.Thm_Formalism_GM_DetBound_gaussR_mul_le
import Theorems.Thm_Formalism_GM_DetBound_gaussR_det_le
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_max_coeff_zero
import Theorems.Thm_Formalism_GM_DetBound_norm_inv_entry_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial DetBound
namespace Formalism.GM
theorem _root_.solution (hM : MahlerK) : LieMat := by
  intro p _ K _ _ _ n del₀ h E c t₀ U V d hc hU hV hdU hdV hE hdel hA
  set L : K[X] := C ((p : K) ^ h) * X + C (t₀ : K) with hL
  set ρ : NNReal := Real.toNNReal ((p : ℝ) ^ (-E)) with hρdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, Real.toNNReal_le_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  set A := binMatK K del₀ c with hAdef
  set B : Matrix (Fin n) (Fin n) K[X] := A.map (fun P => P.comp L) with hB
  have hdetB : A.det.comp L = B.det := by
    have := RingHom.map_det (Polynomial.compRingHom L) A
    simpa [Polynomial.coe_compRingHom_apply, RingHom.mapMatrix_apply] using this
  have hC1 : ∀ a : K, ‖a‖ ≤ 1 → gaussR 1 (C a) ≤ 1 := by
    intro a ha; rw [gaussR_C, ← NNReal.coe_le_coe]; simpa using ha
  have hmul1 : ∀ P Q : K[X], gaussR 1 P ≤ 1 → gaussR 1 Q ≤ 1 → gaussR 1 (P * Q) ≤ 1 :=
    fun P Q hP hQ => (gaussR_mul_le _ _ _).trans (mul_le_one' hP hQ)
  have hBint : ∀ i j, gaussR 1 (B i j) ≤ 1 := by
    intro i j
    simp only [hB, Matrix.map_apply, hAdef, binMatK, Polynomial.sum_comp, mul_comp, C_comp]
    apply gaussR_sum_le
    intro k hk
    apply hmul1 _ _ (hC1 _ (hc i j k))
    rw [gaussR_le_iff]
    intro m
    rw [one_pow, mul_one, ← NNReal.coe_le_coe]
    have hk' : k ≤ p ^ h := by
      have := Finset.mem_range.mp hk; omega
    rw [coe_nnnorm, NNReal.coe_one]
    exact hM p K h k t₀ hk' m
  have hB0 : B.map (Polynomial.eval 0) = U * Matrix.diagonal d * V := by
    rw [← hA]; ext i j; simp [hB, Matrix.map_apply, Polynomial.eval_comp, hL]
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hdU]; norm_num))
  have hVu : IsUnit V.det := isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hdV]; norm_num))
  set B' : Matrix (Fin n) (Fin n) K[X] := (U⁻¹).map C * B * (V⁻¹).map C with hB'
  have hB'0 : B'.map (Polynomial.eval 0) = Matrix.diagonal d := by
    have hmul := fun (X Y : Matrix (Fin n) (Fin n) K[X]) =>
      (Matrix.map_mul (L := X) (M := Y) (f := Polynomial.evalRingHom (0 : K)))
    simp only [coe_evalRingHom] at hmul
    have hCm : ∀ W : Matrix (Fin n) (Fin n) K, (W.map C).map (Polynomial.eval 0) = W := by
      intro W; ext i j; simp
    rw [hB', hmul, hmul, hCm, hCm, hB0]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hVu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hUu]
  have hB'int : ∀ i j, gaussR 1 (B' i j) ≤ 1 := by
    intro i j
    simp only [hB', Matrix.mul_apply, Matrix.map_apply]
    apply gaussR_sum_le; intro l _
    apply hmul1 _ _ _ (hC1 _ (norm_inv_entry_le V hV hdV l j))
    apply gaussR_sum_le; intro k _
    exact hmul1 _ _ (hC1 _ (norm_inv_entry_le U hU hdU i k)) (hBint k l)
  classical
  let b : Fin n → NNReal := fun i => if ‖d i‖ ≤ (p : ℝ) ^ (-E) then ρ else 1
  have hrow : ∀ i j, gaussR ρ (B' i j) ≤ b i := by
    intro i j
    refine (gaussR_le_max_coeff_zero hρ1 _ (hB'int i j)).trans ?_
    have h0 : (B' i j).coeff 0 = Matrix.diagonal d i j := by
      rw [coeff_zero_eq_eval_zero, ← hB'0, Matrix.map_apply]
    rw [h0]
    simp only [b]
    split_ifs with hd
    · refine max_le ?_ le_rfl
      rw [Matrix.diagonal_apply]
      split_ifs with hij
      · rw [hρdef, Real.le_toNNReal_iff_coe_le (Real.rpow_nonneg (by linarith) _)]
        simpa using hd
      · simp
    · refine max_le ?_ hρ1
      have := coeff_le_gaussR 1 (B' i j) 0
      rw [h0, pow_zero, mul_one] at this
      exact this.trans (hB'int i j)
  have hdetB' : gaussR ρ B'.det ≤ ρ ^ (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card := by
    refine (gaussR_det_le ρ B' b hrow).trans (le_of_eq ?_)
    simp only [b]
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  have hBB' : B = U.map C * B' * V.map C := by
    have hmulC := fun (X Y : Matrix (Fin n) (Fin n) K) =>
      (Matrix.map_mul (L := X) (M := Y) (f := (C : K →+* K[X])))
    rw [hB']
    simp only [Matrix.mul_assoc]
    rw [← hmulC V⁻¹ V, Matrix.nonsing_inv_mul _ hVu, ← Matrix.mul_assoc (U.map C), ← hmulC U U⁻¹,
      Matrix.mul_nonsing_inv _ hUu]
    rw [Matrix.map_one _ (map_zero C) (map_one C), Matrix.one_mul, Matrix.mul_one]
  have hdetBB : B.det = C U.det * B'.det * C V.det := by
    rw [hBB', Matrix.det_mul, Matrix.det_mul, RingHom.map_det C U, RingHom.map_det C V]
    rfl
  have hnU : ‖U.det‖₊ = 1 := by ext; simpa using hdU
  have hnV : ‖V.det‖₊ = 1 := by ext; simpa using hdV
  have hfin : gaussR ρ (A.det.comp L) ≤ ρ ^ (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card := by
    rw [hdetB, hdetBB]
    calc gaussR ρ (C U.det * B'.det * C V.det)
        ≤ gaussR ρ (C U.det * B'.det) * gaussR ρ (C V.det) := gaussR_mul_le _ _ _
      _ ≤ gaussR ρ (C U.det) * gaussR ρ B'.det * gaussR ρ (C V.det) := by
          gcongr; exact gaussR_mul_le _ _ _
      _ = gaussR ρ B'.det := by rw [gaussR_C, gaussR_C, hnU, hnV, one_mul, mul_one]
      _ ≤ _ := hdetB'
  have hfin' := NNReal.coe_le_coe.mpr hfin
  refine hfin'.trans (le_of_eq ?_)
  rw [NNReal.coe_pow, hρdef, Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), neg_mul]
end Formalism.GM
