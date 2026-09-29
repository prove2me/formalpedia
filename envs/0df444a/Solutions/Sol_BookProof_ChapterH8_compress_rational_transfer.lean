-- Prove2me | solution 1 for BookProof.ChapterH8.compress_rational_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:42:01.292853+00:00
-- url     : https://prove2.me/submissions/81ee3938-ab45-49e9-8ec6-53118b009949

import Definitions.Def_ChapterH4
open BookProof.ChapterH4 ContinuousLinearMap
set_option autoImplicit false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E)
    (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (v : E) (hv : V ((adjoint V) v) = v) :
    (Polynomial.aeval X p) (qXinv v) =
      V ((Polynomial.aeval (compress V X) p) (qBinv ((adjoint V) v))) := by
  have hb (Y : E →L[ℂ] E) (hY : ∀ x : F, ∃ y : F, Y (V x) = V y) (x : F) :
      Y (V x) = V (compress V Y x) := by
    obtain ⟨y, hy⟩ := hY x
    have hyy := congrArg (fun A : F →L[ℂ] F => A y) hVV
    simp only [compress, comp_apply, id_apply] at hyy ⊢
    rw [hy, hyy]
  have hInv (u : F) : qXinv (V u) = V (qBinv u) := by
    have hB := congrArg (fun A : F →L[ℂ] F => A u) hqBr
    have hQ := congrArg (fun A : E →L[ℂ] E => A (V (qBinv u))) hqXl
    simp only [comp_apply, id_apply] at hB hQ
    calc
      qXinv (V u) = qXinv (V (compress V qX (qBinv u))) := congrArg (fun w => qXinv (V w)) hB.symm
      _ = qXinv (qX (V (qBinv u))) := congrArg qXinv (hb qX hinvq (qBinv u)).symm
      _ = V (qBinv u) := hQ
  have hpow (n : ℕ) (u : F) : (X ^ n) (V u) = V (((compress V X) ^ n) u) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply]
      rw [ih, hb X hinvX]
  have hpoly (r : Polynomial ℂ) (u : F) :
      (Polynomial.aeval X r) (V u) = V ((Polynomial.aeval (compress V X) r) u) := by
    induction r using Polynomial.induction_on' with
    | add r s hr hs =>
      simp only [map_add, ContinuousLinearMap.add_apply, hr, hs]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, ContinuousLinearMap.smul_apply, hpow, map_smul]
  have hvinv : qXinv v = V (qBinv ((adjoint V) v)) :=
    (congrArg qXinv hv.symm).trans (hInv ((adjoint V) v))
  rw [hvinv, hpoly]
#print axioms solution
