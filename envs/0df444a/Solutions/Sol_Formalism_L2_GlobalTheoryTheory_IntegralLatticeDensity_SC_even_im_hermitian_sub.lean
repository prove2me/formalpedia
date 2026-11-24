-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.even_im_hermitian_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:14.768802+00:00
-- url     : https://prove2.me/submissions/d67ab5bb-5124-4e51-810c-54f17e62d66d

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
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (a b c e m k : ℤ) (h1 : ¬(2 ∣ a ∧ 2 ∣ b)) (h2 : ¬(2 ∣ c ∧ 2 ∣ e))
    (h3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e)) :
    (2 ∣ m ∧ 2 ∣ k) ∨ (2 ∣ m - a ∧ 2 ∣ k - b) ∨ (2 ∣ m - c ∧ 2 ∣ k - e) ∨ (2 ∣ m - (a + c) ∧ 2 ∣ k - (b + e)) := by
  omega
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
