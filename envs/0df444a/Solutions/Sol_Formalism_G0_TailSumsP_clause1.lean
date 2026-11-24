-- Prove2me | solution 1 for Formalism.G0.TailSumsP.clause1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:29.960193+00:00
-- url     : https://prove2.me/submissions/651da839-d776-4b01-aef5-0cea4604610a

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_zero_fun
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_shrink
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_vec_succ
import Theorems.Thm_Formalism_G0_TailSumsP_tailK_vec_zero
import Theorems.Thm_Formalism_G0_TailSumsP_latestDegrees_succ_some
import Theorems.Thm_Formalism_G0_TailSumsP_latestDegrees_succ_none

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
    (hp : IsPath steps what₂) :
    ∀ i ≤ steps.length, ∀ u, tailK (what₂ i) u ≤ ((latestDegrees steps i).drop u).sum := by
  intro i
  induction i with
  | zero => intro _ u; rw [hp.1, tailK_zero_fun]; exact Nat.zero_le _
  | succ i ih =>
    intro hi u
    have hi' : i < steps.length := by omega
    have hstep := hp.2 i hi'
    cases hs : steps[i] with
    | none =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_none steps i hi' hs]
      exact le_trans (tailK_shrink hstep u) (ih (by omega) u)
    | some B =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_some steps i hi' hs]
      cases u with
      | zero =>
        simp only [List.drop_zero, List.sum_cons]
        have h1 := ih (by omega) 0
        simp only [List.drop_zero] at h1
        have h2 := tailK_vec_zero hstep
        omega
      | succ u =>
        simp only [List.drop_succ_cons]
        exact le_trans (tailK_vec_succ hstep u) (ih (by omega) u)
end Formalism.G0.TailSumsP
