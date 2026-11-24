-- Prove2me | solution 1 for Formalism.G0.TailSumsP.clause2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.679676+00:00
-- url     : https://prove2.me/submissions/9c1abc47-4933-4f3c-843d-c0542e119d4b

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_shrink
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_vec_succ
import Theorems.Thm_Formalism_G0_TailSumsP_latestDegrees_succ_some
import Theorems.Thm_Formalism_G0_TailSumsP_latestDegrees_succ_none
import Theorems.Thm_Formalism_G0_TailSumsP_cnt_self
import Theorems.Thm_Formalism_G0_TailSumsP_cnt_succ_some
import Theorems.Thm_Formalism_G0_TailSumsP_cnt_succ_none

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP
namespace Formalism.G0.TailSumsP
theorem _root_.solution {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) (i u X : ℕ)
    (hX : tailK (what₂ i) u + X ≤ ((latestDegrees steps i).drop u).sum) :
    ∀ j, i ≤ j → j ≤ steps.length →
      tailK (what₂ j) (u + cnt steps i j) + X ≤
        ((latestDegrees steps j).drop (u + cnt steps i j)).sum := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; rw [cnt_self, Nat.add_zero]; exact hX
  | succ j hij ih =>
    intro hj
    have hj' : j < steps.length := by omega
    have hstep := hp.2 j hj'
    cases hs : steps[j] with
    | none =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_none steps j hj' hs, cnt_succ_none steps i j hij hj' hs]
      have := tailK_shrink hstep (u + cnt steps i j)
      have := ih (by omega)
      omega
    | some B =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_some steps j hj' hs, cnt_succ_some steps i j hij hj' hs,
        ← Nat.add_assoc, List.drop_succ_cons]
      have := tailK_vec_succ hstep (u + cnt steps i j)
      have := ih (by omega)
      omega
end Formalism.G0.TailSumsP
