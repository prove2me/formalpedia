-- Prove2me | solution 1 for Formalism.L2.Th1.G.eigen_split_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:53:58.493937+00:00
-- url     : https://prove2.me/submissions/b5a60dbf-d844-4c11-81df-04d4767f0e05

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
namespace Formalism.L2.Th1.G
theorem _root_.solution : EigenSplit := by
  intro K _ _ ι T X _ ty pr BB th chi chi' hth hBB hc hsep
  refine ⟨fun i j => if ty j = pr (ty i) then 0 else BB i j / th, fun i j => ?_, fun i j => ?_⟩
  · dsimp only
    split_ifs with h
    · simp
    · obtain ⟨x, hx⟩ := hsep (ty i) (ty j) h
      have h1 := hc x i j
      rw [norm_mul, hx, one_mul] at h1
      rw [norm_div]
      exact div_le_one_of_le₀ h1 (norm_nonneg _)
  · dsimp only
    split_ifs with h
    · simp
    · field_simp
      ring
end Formalism.L2.Th1.G
