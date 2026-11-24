-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_shiftPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:12.689997+00:00
-- url     : https://prove2.me/submissions/fa685782-e24a-409e-b8c8-19598c74bbf9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_weight_one_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_shiftGen

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
theorem _root_.solution (b : κ → ι → K) {d : ℕ} {Q : MvPolynomial ι K} (hQ : Q.IsHomogeneous d) :
    biHom d (shiftPoly b Q) := by
  rw [shiftPoly_expand]
  refine biHom_sum _ _ fun n hn => ?_
  have h1 : n.degree = d := by
    rw [← weight_one_eq]
    exact hQ (MvPolynomial.mem_support_iff.mp hn)
  have h2 := biHom_mul (biHom_C (κ := κ) (MvPolynomial.isHomogeneous_C ι (MvPolynomial.coeff n Q)))
    (biHom_prod n.support (fun i => n i * 1) (fun i => shiftGen b i ^ n i)
      fun i _ => biHom_pow (biHom_shiftGen b i) (n i))
  simp only [mul_one, zero_add] at h2
  rw [← h1, Finsupp.degree_apply]
  exact h2
end Formalism.InvariantFactorPaths.G7
