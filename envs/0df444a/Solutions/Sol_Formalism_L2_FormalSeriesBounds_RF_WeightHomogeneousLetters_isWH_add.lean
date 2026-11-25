-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.isWH_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:44.984936+00:00
-- url     : https://prove2.me/submissions/26b77a8b-391d-43a1-a1bf-537c4e4b136a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
variable {R : Type} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
theorem _root_.solution {σ : Type} {w1 w2 : σ → ℕ} {p : MvPolynomial σ R} {D1 D2 : ℕ}
    (h1 : IsWeightedHomogeneous w1 p D1) (h2 : IsWeightedHomogeneous w2 p D2) :
    IsWeightedHomogeneous (fun x => w1 x + w2 x) p (D1 + D2) := by
  intro m hm
  have e1 := h1 hm
  have e2 := h2 hm
  simp only [Finsupp.weight_apply, Finsupp.sum] at e1 e2 ⊢
  rw [← e1, ← e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => smul_add _ _ _
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
