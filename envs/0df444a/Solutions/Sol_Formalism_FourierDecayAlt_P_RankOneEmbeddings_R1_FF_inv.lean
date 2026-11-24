-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.FF_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:20.32663+00:00
-- url     : https://prove2.me/submissions/a84a90b2-6d06-4bb9-aeaa-cfc25010aa11

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_lmulM_cont

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
theorem _root_.solution {z' : Vc k r} {μW' : Measure (Mt k r)} (hW' : IsHaarOn (UWset k r z') μW')
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) (m : Mat k r) (h : Mat k r) (hh : h ∈ UWset k r z') :
    ∫⁻ h', f (mulM ((m * h : Mat k r), h')) ∂μW' = ∫⁻ h', f (mulM (m, h')) ∂μW' := by
  have hmeas : Measurable (lmulM h : Mt k r → Mt k r) := (lmulM_cont h).measurable
  have hF : Measurable fun h' : Mt k r => f (mulM (m, h')) :=
    hf.comp (mulM_cont.measurable.comp (measurable_const.prodMk measurable_id))
  calc ∫⁻ h', f (mulM ((m * h : Mat k r), h')) ∂μW' = ∫⁻ h', f (mulM (m, lmulM h h')) ∂μW' := by
        congr 1
        funext h'
        congr 1
        exact Matrix.mul_assoc m h (Matrix.of h')
    _ = ∫⁻ h', f (mulM (m, h')) ∂(μW'.map (lmulM h)) := (lintegral_map hF hmeas).symm
    _ = ∫⁻ h', f (mulM (m, h')) ∂μW' := by rw [hW'.left h hh]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
