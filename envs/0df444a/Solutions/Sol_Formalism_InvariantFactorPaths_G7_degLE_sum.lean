-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:03.904629+00:00
-- url     : https://prove2.me/submissions/913b37c7-9a13-4190-8af1-733670c3a6a8

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412
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
variable {κ R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {α : Type*} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R)
    (h : ∀ a ∈ s, degLE W n (F a)) : degLE W n (∑ a ∈ s, F a) := by
  first | exact _root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 .. | (apply _root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 <;> assumption) | (intros; apply _root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 <;> assumption) | (intros; apply @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 <;> first | assumption | infer_instance) | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› α W n s F h | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› α W n s F | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› α W n s | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› α W n | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› α W | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› α | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ R | exact @_root_.P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412 κ
end Formalism.InvariantFactorPaths.G7
