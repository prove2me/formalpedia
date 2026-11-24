-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.shiftPoly_lowPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:05.96606+00:00
-- url     : https://prove2.me/submissions/c22187ff-d044-4352-8908-96a2033b96be

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add


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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K Tp Lw : Type} [Field K]
variable {κ : Type} [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (b : κ → Lw → K) (Q : MvPolynomial Lw K) :
    shiftPoly (ext0 (Tp := Tp) b) (lowPoly Q) =
      MvPolynomial.map (MvPolynomial.rename (Sum.inr : Lw → Tp ⊕ Lw) :
        MvPolynomial Lw K →ₐ[K] MvPolynomial (Tp ⊕ Lw) K).toRingHom (shiftPoly b Q) := by
  unfold shiftPoly lowPoly
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf =>
    simp only [map_mul, hf]
    simp [ext0, map_sum]
end Formalism.InvariantFactorPaths.G7.ETerm
