-- Prove2me | solution 1 for BookProof.HermiteCore.deriv_poly_mul_gaussH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:27.676721+00:00
-- url     : https://prove2.me/submissions/d19257f9-3513-464a-ae05-3444c05ded50

-- Generated from ChapterHermiteFunctions.lean — solution of BookProof.HermiteCore.deriv_poly_mul_gaussH
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
import Theorems.Thm_BookProof_HermiteCore_hasDerivAt_poly_mul_gaussH
open BookProof.HermiteCore









open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p : Polynomial ℝ) :
    deriv (fun y : ℝ => p.eval y * gaussH y)
      = fun x : ℝ => (derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x := funext fun x => (hasDerivAt_poly_mul_gaussH p x).deriv
