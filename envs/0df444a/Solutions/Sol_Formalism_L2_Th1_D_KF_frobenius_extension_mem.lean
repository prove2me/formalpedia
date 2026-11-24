-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.frobenius_extension_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:21.507364+00:00
-- url     : https://prove2.me/submissions/aa555788-2432-455b-8969-c2af7f1a0010

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_continuous
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_on_inclusion

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open KF
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution (x : ringB l) : sig1 σ0 hiso x ∈ ringB l := by
  refine (incAB_dense l).induction_on x ?_ ?_
  · exact IsClosed.preimage (frobenius_extension_continuous σ0 hiso) (Subring.isClosed_topologicalClosure (ringA l))
  · intro a
    rw [frobenius_extension_on_inclusion]
    exact ringA_le_ringB l (σ0 a).2
end Formalism.L2.Th1.D.KF
