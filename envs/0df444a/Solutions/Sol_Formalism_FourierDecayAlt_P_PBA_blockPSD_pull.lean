-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.blockPSD_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:11.207772+00:00
-- url     : https://prove2.me/submissions/63ded2ae-91bb-46eb-b071-16206ac0800b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_iff_qf


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
theorem _root_.solution {Z X : Type} (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H) (Y : Finset X)
    (f g : X → Z) (hf : ∀ h ∈ Y, f h ∈ P) (hg : ∀ h ∈ Y, g h ∈ P) :
    KB.BlockPSD Y Y (fun h h' => H (f h) (f h')) (fun h h' => H (f h) (g h')) (fun h h' => H (g h) (g h')) := by
  have h1 := psd_comp P H hH (Y.disjSum Y) (Sum.elim f g) (by
    rintro (x|x) hx
    · simpa using hf x (by simpa using hx)
    · simpa using hg x (by simpa using hx))
  have hherm := ((PBA.psd_iff_qf P H).1 hH).1
  unfold KB.BlockPSD
  unfold TB.PSDOn at h1 ⊢
  convert h1 using 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases i with x | x <;> rcases j with y | y
  · rfl
  · rfl
  · exact (hherm (f y) (hf y (by simpa using hj)) (g x) (hg x (by simpa using hi))).symm
  · rfl
end Formalism.FourierDecayAlt.P.PBA
