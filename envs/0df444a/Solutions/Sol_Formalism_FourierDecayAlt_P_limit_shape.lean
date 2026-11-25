-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.limit_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:48:25.443507+00:00
-- url     : https://prove2.me/submissions/f344f5c6-b355-4a8e-ba42-45bcf95d09ec

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wM_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wM_zero_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_strictUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.LimitShape := by
  intro m z σ ρ' X B hX hx i j hji
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i => ?_) i hji
  · intro h
    have hj : j = 0 := le_antisymm h (Fin.zero_le _)
    subst hj
    have := wM_zero_cast X B (Fin.cons z ρ') σ 0
    simp only [Fin.castSucc_zero, Fin.cons_zero] at this
    rw [this]; simp
  · intro h
    rw [wM_succ]
    rcases h.eq_or_lt with h | h
    · subst h
      have := hx i
      unfold xOf at this
      rw [this]; simp
    · rw [blk_strictUpper X B hX _ _ (Fin.le_castSucc_iff.mpr h), Matrix.one_apply_ne h.ne']
      simp
end Formalism.FourierDecayAlt.P
