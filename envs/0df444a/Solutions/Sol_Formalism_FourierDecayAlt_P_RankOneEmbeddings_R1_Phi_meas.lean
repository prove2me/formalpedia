-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.Phi_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:17:34.511874+00:00
-- url     : https://prove2.me/submissions/0150335b-c627-4ee7-bd92-35fa95351436

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
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
theorem _root_.solution {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) : Measurable (Phi (r := r) s) := by
  have h1 : Measurable fun x : ℂ × (Mt k r × Mt k r) => invM x.2.1 :=
    invM_meas.comp (measurable_fst.comp measurable_snd)
  have h2 : Measurable fun x : ℂ × (Mt k r × Mt k r) => embF k r (s x.1) :=
    (embS_meas (r := r) hs).comp measurable_fst
  have h3 : Measurable fun x : ℂ × (Mt k r × Mt k r) => x.2.2 := measurable_snd.comp measurable_snd
  exact mulM_cont.measurable.comp ((mulM_cont.measurable.comp (h1.prodMk h2)).prodMk h3)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
