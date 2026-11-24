-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.fs_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:47.996428+00:00
-- url     : https://prove2.me/submissions/59ac6009-29e1-4ef4-aaf3-6bfcc60c1603

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (C M6 L kR fR lam lC : ℝ) (hf1 : 1 ≤ fR) (hk8 : 8 ≤ kR) (hl0 : 0 ≤ lam)
    (hmE : M6 ≤ 2 * (M6 * L)) (hE16 : 16 * (M6 * L) ≤ kR * lam) (hCE : 16 * C * (M6 * L) ≤ kR * lam)
    (hlogC : 16 * lC ≤ lam) :
    M6 + (C * M6 * fR * L + C * M6 * fR * L) +
      ((kR - 2) * fR * (lC - lam) + (kR - 2) * fR * (lC - lam)) ≤ -(kR * fR * lam) := by
  have hf0 : 0 ≤ fR := by linarith
  have hk0 : 0 ≤ kR := by linarith
  have hfl : 0 ≤ fR * lam := mul_nonneg hf0 hl0
  have b0 : kR * lam ≤ kR * fR * lam := by
    have h1 := mul_nonneg (mul_nonneg hk0 hl0) (sub_nonneg.2 hf1)
    have e : kR * fR * lam - kR * lam = kR * lam * (fR - 1) := by ring
    linarith
  have b2 : 2 * (C * M6 * fR * L) ≤ kR * fR * lam / 8 := by
    have h := mul_le_mul_of_nonneg_left hCE hf0
    have e1 : 2 * (C * M6 * fR * L) = fR * (16 * C * (M6 * L)) / 8 := by ring
    have e2 : fR * (kR * lam) = kR * fR * lam := by ring
    linarith
  have b3 : 2 * ((kR - 2) * fR * lC) ≤ kR * fR * lam / 8 := by
    have h1 : (kR - 2) * fR * (16 * lC) ≤ (kR - 2) * fR * lam :=
      mul_le_mul_of_nonneg_left hlogC (mul_nonneg (by linarith) hf0)
    have e1 : 2 * ((kR - 2) * fR * lC) = (kR - 2) * fR * (16 * lC) / 8 := by ring
    have e2 : (kR - 2) * fR * lam = kR * fR * lam - 2 * (fR * lam) := by ring
    linarith
  have b4 : 8 * (fR * lam) ≤ kR * fR * lam := by
    have h := mul_le_mul_of_nonneg_right hk8 hfl
    have e : kR * (fR * lam) = kR * fR * lam := by ring
    linarith
  have e : M6 + (C * M6 * fR * L + C * M6 * fR * L) +
      ((kR - 2) * fR * (lC - lam) + (kR - 2) * fR * (lC - lam)) =
      M6 + 2 * (C * M6 * fR * L) + 2 * ((kR - 2) * fR * lC) - 2 * (kR * fR * lam) + 4 * (fR * lam) := by ring
  rw [e]
  linarith
end Formalism.HermitianLatticeCounting.P
