-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.lint_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:36:13.684871+00:00
-- url     : https://prove2.me/submissions/0ed9f77e-f55a-492c-870c-fce52d04616e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_zW_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_Phi_meas

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
theorem _root_.solution {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hs : MeasSec s) (z z' : Vc k r)
    (μW μW' : Measure (Mt k r)) [SFinite μW] [SFinite μW'] (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ m, f m ∂(((wd k r z z').prod (μW.prod μW')).map (Phi s)) =
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p : Mt k r × Mt k r, f (Phi s (ζ, p)) ∂(μW.prod μW') := by
  have hF : Measurable fun x : ℂ × (Mt k r × Mt k r) => f (Phi s x) := hf.comp (Phi_meas hs)
  rw [lintegral_map hf (Phi_meas hs), lintegral_prod _ hF.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ ((zW_meas k _ _).ennreal_ofReal) hF.lintegral_prod_right']
  rfl
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
