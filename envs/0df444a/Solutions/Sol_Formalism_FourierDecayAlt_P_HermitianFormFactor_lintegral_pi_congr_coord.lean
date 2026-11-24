-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_pi_congr_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:19:43.678476+00:00
-- url     : https://prove2.me/submissions/b5e17901-a75f-4e22-b403-c129108f18dd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] [Inhabited E] (i : ι) (f f' : (ι → E) → ℝ≥0∞)
    (hf : Measurable f) (hf' : Measurable f')
    (h : ∀ x, ∫⁻ z, f (Function.update x i z) = ∫⁻ z, f' (Function.update x i z)) :
    ∫⁻ x, f x = ∫⁻ x, f' x := by
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => default), lintegral_eq_lmarginal_univ (fun _ => default),
    lmarginal_erase' _ hf (Finset.mem_univ i), lmarginal_erase' _ hf' (Finset.mem_univ i)]
  congr 2
  funext x
  exact h x
end Formalism.FourierDecayAlt.P.HermitianFormFactor
