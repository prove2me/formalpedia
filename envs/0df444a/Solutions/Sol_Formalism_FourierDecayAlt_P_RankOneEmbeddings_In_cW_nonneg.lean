-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.cW_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:17.714778+00:00
-- url     : https://prove2.me/submissions/71b4bb02-5635-4376-8240-31a4ead71a7e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas sgF_meas
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution (c : Fin r → ℂ) : 0 ≤ cWeight k r c := by
  unfold cWeight
  exact Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
