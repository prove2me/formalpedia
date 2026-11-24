-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.quadratic_form_theta_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:27.695172+00:00
-- url     : https://prove2.me/submissions/37739032-86a4-4507-a069-2cf86a3072e6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_theta_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (w : ℂ) : q1 L d (cmTheta 1 d * w) = (1 + (d : ℝ)) / 4 * q1 L d w := by
  have h1 : herm L (cmTheta 1 d * w) (cmTheta 1 d * w) =
      ((Complex.normSq (cmTheta 1 d) : ℝ) : ℂ) * herm L w w := by
    simp only [herm, map_mul]
    rw [← Complex.mul_conj]
    ring
  simp only [q1]
  rw [h1, Complex.re_ofReal_mul, theta_normSq]
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
