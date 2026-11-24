-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.measurable_inv_mulVec_embWb_of_measSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:46.404437+00:00
-- url     : https://prove2.me/submissions/ae60efeb-d3d9-40c4-b020-4c6978931a1c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_mvM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_embS_meas

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
theorem _root_.solution {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (z' : Vc k r) :
    Measurable fun p : ℂ × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹ *ᵥ (embWb k r (s p.1) *ᵥ z') := by
  have h1 : Measurable fun p : ℂ × Mt k r => embF k r (s p.1) := (embS_meas (r := r) hs).comp measurable_fst
  have h2 : Measurable fun p : ℂ × Mt k r => mvM (embF k r (s p.1), z') :=
    mvM_cont.measurable.comp (h1.prodMk measurable_const)
  exact mvM_cont.measurable.comp ((invM_meas.comp measurable_snd).prodMk h2)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
