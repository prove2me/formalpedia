-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:47:25.320478+00:00
-- url     : https://prove2.me/submissions/a5f1cb24-b231-4076-a27f-5809eb2fe227

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) {f : (Fin (2 * r' + k + 1) → ℂ) → (Fin (2 * r' + k + 1) → ℂ)}
    (hf : MeasurePreserving f volume volume) {c : (Fin (2 * r' + k + 1) → ℂ) → ℝ} (hc : Measurable c) :
    MeasurePreserving (fun p : HPar k r' => (f p.1, p.2 + c p.1)) volume volume := by
  exact hf.skew_product (g := fun y s => s + c y) (μc := volume) (μd := volume)
    (measurable_snd.add (hc.comp measurable_fst)) (ae_of_all _ fun y => map_add_right_eq_self volume (c y))
end Formalism.FourierDecayAlt.P.B2x5
