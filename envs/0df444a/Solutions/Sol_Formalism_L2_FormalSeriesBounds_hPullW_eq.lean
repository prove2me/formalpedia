-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.hPullW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:08.133751+00:00
-- url     : https://prove2.me/submissions/387a171a-fc47-4a5b-a71b-0b5c8287584a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (H : MvPowerSeries (WV I) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) :
    hPullW H (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = subst (linS (rowM g e v')) H := by
  unfold hPullW
  congr 1
  funext w
  unfold linS rowM
  rw [Fintype.sum_sum_type]
  rfl
end Formalism.L2.FormalSeriesBounds
