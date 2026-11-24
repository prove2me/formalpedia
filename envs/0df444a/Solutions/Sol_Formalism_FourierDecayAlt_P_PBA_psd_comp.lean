-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.psd_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:33:46.840799+00:00
-- url     : https://prove2.me/submissions/894cbae0-38c0-4a48-8b33-41dba1940210

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {Z X : Type} (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H) (Y : Finset X) (g : X → Z)
    (hg : ∀ h ∈ Y, g h ∈ P) : TB.PSDOn Y (fun x y => H (g x) (g y)) := by
  unfold TB.PSDOn at hH ⊢
  exact hH.submatrix (fun x : Y => (⟨g x, hg x x.2⟩ : P))
end Formalism.FourierDecayAlt.P.PBA
