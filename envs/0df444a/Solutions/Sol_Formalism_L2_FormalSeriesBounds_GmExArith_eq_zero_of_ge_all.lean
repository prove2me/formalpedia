-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.eq_zero_of_ge_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:08.304796+00:00
-- url     : https://prove2.me/submissions/43ff3382-59e7-483f-b30e-153780278db9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {x : C} (h : ∀ n : ℕ, V.Ge n x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have h1 := h n
  unfold VF.Ge at h1
  rw [← hr] at h1
  exact absurd (WithTop.coe_le_coe.1 h1) (not_le.2 hn)
end Formalism.L2.FormalSeriesBounds.GmExArith
