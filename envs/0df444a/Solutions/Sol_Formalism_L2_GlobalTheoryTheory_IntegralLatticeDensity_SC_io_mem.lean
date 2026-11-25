-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.io_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:29.471373+00:00
-- url     : https://prove2.me/submissions/0264f018-fb2f-4d5b-b42b-da8c1c284f44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar

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
theorem _root_.solution {w : ℂ} (h : w ∈ L.lattice) : io w ∈ stdLat L Unit := by
  unfold stdLat
  first
    | exact fun _ _ => h
    | (rw [← SetLike.mem_coe, AddSubgroup.coe_pi]; exact Set.mem_univ_pi.mpr fun _ => h)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
