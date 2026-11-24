-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:58:12.386195+00:00
-- url     : https://prove2.me/submissions/36dcd59b-c7ff-40bf-877f-3dad97c2e983

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504
import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K ι κ : Type} [Field K] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {α : Type*} {d : ℕ} (s : Finset α) (F : α → MvPolynomial κ (MvPolynomial ι K))
    (h : ∀ a ∈ s, biHom d (F a)) : biHom d (∑ a ∈ s, F a) := by
  first | exact _root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 .. | (apply _root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 <;> assumption) | (intros; apply _root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 <;> assumption) | (intros; apply @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 <;> first | assumption | infer_instance) | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› ‹_› α d s F h | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› ‹_› α d s F | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› ‹_› α d s | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› ‹_› α d | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› ‹_› α | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι κ | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K ι | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504 K
end Formalism.InvariantFactorPaths.G7
