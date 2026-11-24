-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.ae_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:24:20.983229+00:00
-- url     : https://prove2.me/submissions/ffcefc0f-1707-4223-8cf9-56e1dc87eeff

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_mem

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
theorem _root_.solution (z z' : Vc k r) {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW)
    (hW' : IsHaarOn (UWset k r z') μW') [SFinite μW] [SFinite μW'] :
    ∀ᵐ x : ℂ × (Mt k r × Mt k r) ∂((wd k r z z').prod (μW.prod μW')),
      (Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z' := by
  have hA : ∀ᵐ p ∂(μW.prod μW'), (Matrix.of p.1 : Mat k r) ∈ UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_mem hW)
  have hB : ∀ᵐ p ∂(μW.prod μW'), (Matrix.of p.2 : Mat k r) ∈ UWset k r z' :=
    Measure.quasiMeasurePreserving_snd.ae (ae_mem hW')
  exact Measure.quasiMeasurePreserving_snd.ae (hA.and hB)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
