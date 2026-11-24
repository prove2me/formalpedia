-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_det_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:32.004792+00:00
-- url     : https://prove2.me/submissions/0d722dac-feee-471c-9781-4dda97655cbc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_prod

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
theorem _root_.solution {l : ℕ} {W : Finset κ} (N : Matrix (Fin l) (Fin l) (MvPolynomial κ R))
    (n : Fin l → ℕ) (h : ∀ i c, degLE W (n c) (N i c)) : degLE W (∑ c, n c) N.det := by
  rw [Matrix.det_apply']
  refine degLE_sum _ _ fun σ _ => ?_
  have h1 : degLE W 0 (((Equiv.Perm.sign σ : ℤ) : MvPolynomial κ R)) := by
    rw [← map_intCast (MvPolynomial.C : R →+* MvPolynomial κ R)]
    exact degLE_C W _
  have := degLE_mul h1 (degLE_prod Finset.univ n (fun c => N (σ c) c) fun c _ => h (σ c) c)
  rwa [zero_add] at this
end Formalism.InvariantFactorPaths.G7
