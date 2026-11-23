-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pderiv_linP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:45.689355+00:00
-- url     : https://prove2.me/submissions/b2651491-9504-46d9-82c7-e10f868fb7b7

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
theorem _root_.solution (A : ι → ι' → K) (i : ι) (j : ι') :
    MvPolynomial.pderiv i (linP A j) = MvPolynomial.C (A i j) := by
  classical
  simp [linP, MvPolynomial.pderiv_X, Pi.single_apply]
end Formalism.DworkPowerSeriesWeights
