-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.IsConjM.dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:33:01.951226+00:00
-- url     : https://prove2.me/submissions/58aa48b7-dc96-41be-81b7-b4beca670fcc

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.N.K.Norm
namespace IsConjM
theorem _root_.solution [Group Γ] {M M' : Γ → Matrix n n K} (h : IsConjM M M') :
    IsConjM (fun g => (M g⁻¹).transpose) (fun g => (M' g⁻¹).transpose) := by
  obtain ⟨Q, P, h2, h1, h3⟩ := h.symm
  refine ⟨Q.transpose, P.transpose, ?_, ?_, fun g => ?_⟩
  · rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h3]
end IsConjM
end Formalism.MainNotions.N.K.Norm
