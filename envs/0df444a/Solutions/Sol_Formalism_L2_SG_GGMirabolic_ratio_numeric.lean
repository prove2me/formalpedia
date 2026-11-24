-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.ratio_numeric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:53.123452+00:00
-- url     : https://prove2.me/submissions/0ba0fe41-5f73-4838-9b9e-3aadd8f2b0fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_t_GGNumeric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic
theorem _root_.solution (k : ℕ) (q : ℝ) (hq : 3 ≤ q) :
    ∏ i ∈ Finset.Ico 1 k, (1 - (q ^ i)⁻¹)⁻¹ ≤ 1 + 3 / q := by
  have h := Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_GGNumeric (k - 1) q hq
  have he : Finset.Ico 1 k = Finset.Icc 1 (k - 1) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [he]; exact h
end Formalism.L2.SG.GGMirabolic
