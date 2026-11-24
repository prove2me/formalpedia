-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.secF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:20.082299+00:00
-- url     : https://prove2.me/submissions/a4be2d4a-0747-4647-9c42-abf2f8d3cf8e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Om_open

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : IsSection k r z z' μsec) : MeasSec (secF k r z z' μsec) := by
  classical
  have hs := hsec
  unfold IsSection at hs
  unfold MeasSec
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have heq : (fun ζ => secF k r z z' μsec ζ i j) =
      (Om k r z z').piecewise (fun ζ => μsec ζ i j) (fun _ => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j) := by
    funext ζ
    unfold secF Set.piecewise
    split_ifs <;> rfl
  rw [heq]
  exact ContinuousOn.measurable_piecewise (hs.1 i j).continuousOn continuousOn_const (Om_open z z').measurableSet
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
