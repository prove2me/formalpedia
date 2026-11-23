-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.summable_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:14.250532+00:00
-- url     : https://prove2.me/submissions/953ea2df-3af2-4eee-92f1-3cbe10f5b58c

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
variable {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
theorem _root_.solution (a : ι → V) (ha : Summable (fun i => ‖a i‖)) :
    Summable (fun p : ι × ι => (inner ℂ (a p.1) (a p.2) : ℂ)) := by
  have hprod : Summable (fun p : ι × ι => ‖a p.1‖ * ‖a p.2‖) :=
    Summable.mul_of_nonneg (f := fun i => ‖a i‖) (g := fun i => ‖a i‖) ha ha
      (fun i => norm_nonneg (a i)) (fun i => norm_nonneg (a i))
  have hb : Summable (fun p : ι × ι => ‖(inner ℂ (a p.1) (a p.2) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_inner_le_norm (𝕜 := ℂ) (a p.1) (a p.2)) hprod
  exact hb.of_norm
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
