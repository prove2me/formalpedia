-- Prove2me | solution 1 for BookProof.HermiteExpWall.memLp_scalaron_psi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:04:55.064422+00:00
-- url     : https://prove2.me/submissions/b5edecaa-183a-49b5-a2a1-c3849907a187

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.memLp_scalaron_psi
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_mul
import Theorems.Thm_BookProof_QgHermiteCore_continuous_gaussPoly
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_integrable_potential_gaussPoly_mul
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.QgHermiteCore
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.Starobinsky

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (N : ℕ) :
    MemLp (fun x => starobinskyV M alpha x * psi N x) 2 volume := by

  have hVc : Continuous (starobinskyV M alpha) := continuous_starobinskyV M alpha
  have hVb : ExpBounded (starobinskyV M alpha) := expBounded_starobinskyV M alpha hM
  refine (memLp_two_iff_integrable_sq_norm
    ((hVc.mul (continuous_gaussPoly _)).aestronglyMeasurable)).mpr ?_
  have h := integrable_potential_gaussPoly_mul
    (W := fun x => starobinskyV M alpha x * starobinskyV M alpha x)
    (hVc.mul hVc) (hVb.mul hVb) ((Polynomial.X : Polynomial ℝ) ^ N)
    ((Polynomial.X : Polynomial ℝ) ^ N)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, sq_abs, Pi.mul_apply]
  ring
