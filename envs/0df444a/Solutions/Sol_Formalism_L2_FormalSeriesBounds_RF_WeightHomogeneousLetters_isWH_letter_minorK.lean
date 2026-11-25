-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.isWH_letter_minorK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:27:23.295261+00:00
-- url     : https://prove2.me/submissions/56ace374-b566-4945-ae9b-cabd129e45d8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_wRowG_letter
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_minorK_row
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_rename


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
open WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)
include std
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
theorem _root_.solution {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRowG X idx (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) :=
  isWH_rename _ (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x)
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
