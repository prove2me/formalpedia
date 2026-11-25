-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.blockPSD_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:34:17.784796+00:00
-- url     : https://prove2.me/submissions/e5432804-d8a5-460a-876d-3d81b735900b

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) (f : α → H) (g : β → H) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ⟪f p, f q⟫_ℂ) (fun p q => ⟪f p, g q⟫_ℂ) (fun p q => ⟪g p, g q⟫_ℂ) := by
  unfold KB.BlockPSD TB.PSDOn
  have := Matrix.posSemidef_gram ℂ (fun x : (Y₁.disjSum Y₂) => Sum.elim f g x.1)
  convert this using 1
  all_goals try rfl
  ext ⟨x, hx⟩ ⟨y, hy⟩
  rcases x with p | p <;> rcases y with q | q <;> simp [Matrix.gram_apply]
end Formalism.FourierDecayAlt.P.PBK
