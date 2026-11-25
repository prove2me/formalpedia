-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:04.497028+00:00
-- url     : https://prove2.me/submissions/88d81eb5-28de-48d1-94e0-f8f306a0cb78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_cmQuadraticForm_eq_alternatingForm

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
theorem _root_.solution (w : ℂ) : alphaQ (Real.sqrt d / 2) (stdH L Unit) (io w) = aa L d w := by
  unfold alphaQ aa
  rw [cmQuadraticForm_eq_alternatingForm]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
