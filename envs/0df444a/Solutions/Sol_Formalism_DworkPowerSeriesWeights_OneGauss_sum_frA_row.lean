-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.sum_frA_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:57.329653+00:00
-- url     : https://prove2.me/submissions/1e0a33e9-a44b-4edd-83ff-e2f6ac5e03e5

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution {K : Type} [Field K] {N0 N1 : ℕ} (Y : Fin N0 × Fin N0 → K) (i : Fin N0)
    (b : Fin N1) :
    (∑ j : Fin N0 × Fin N1, MvPolynomial.C (frA Y (i, b) j) * MvPolynomial.X j :
      MvPolynomial (Fin N0 × Fin N1) K) =
      ∑ a : Fin N0, MvPolynomial.C (Y (i, a)) * MvPolynomial.X (a, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]
  · simp [frA]
  · intro c _ hc
    simp [frA, Ne.symm hc]
  · simp
end Formalism.DworkPowerSeriesWeights.OneGauss
