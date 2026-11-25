-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.EqOn.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:57.975816+00:00
-- url     : https://prove2.me/submissions/38e2ab34-1ed3-4046-85b9-d3c2d6679406

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_refl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace EqOn
theorem _root_.solution {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (k : ℕ) : EqOn A (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h
end EqOn
end Formalism.L2.FormalSeriesBounds
