-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.constantCoeff_aeval_linP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:28.668035+00:00
-- url     : https://prove2.me/submissions/35308196-4149-48b1-91d4-fca2d22e8f02

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (A : ι → ι' → K) (G : MvPolynomial ι' K) :
    MvPolynomial.constantCoeff (MvPolynomial.aeval (linP A) G) = MvPolynomial.constantCoeff G := by
  induction G using MvPolynomial.induction_on
  · simp
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p j hp
    simp only [map_mul, MvPolynomial.aeval_X, hp, MvPolynomial.constantCoeff_X, mul_zero]
    simp [linP]
end Formalism.DworkPowerSeriesWeights
