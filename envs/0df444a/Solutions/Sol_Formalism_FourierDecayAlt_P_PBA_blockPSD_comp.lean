-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.blockPSD_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:10.191303+00:00
-- url     : https://prove2.me/submissions/edf24900-c39f-4815-bc96-2f7212a30252

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_comp

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
theorem _root_.solution {α X : Type} (Y₀ : Finset α) (a w b : α → α → ℂ) (h : KB.BlockPSD Y₀ Y₀ a w b)
    (Y : Finset X) (l : X → α) (hl : ∀ x ∈ Y, l x ∈ Y₀) :
    KB.BlockPSD Y Y (fun x y => a (l x) (l y)) (fun x y => w (l x) (l y)) (fun x y => b (l x) (l y)) := by
  unfold KB.BlockPSD at h
  have h1 := psd_comp _ _ h (Y.disjSum Y) (Sum.map l l) (by
    rintro (x|x) hx
    · simpa using hl x (by simpa using hx)
    · simpa using hl x (by simpa using hx))
  unfold KB.BlockPSD
  unfold TB.PSDOn at h1 ⊢
  convert h1 using 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases i with x | x <;> rcases j with y | y <;> rfl
end Formalism.FourierDecayAlt.P.PBA
