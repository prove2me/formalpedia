-- Prove2me | solution 1 for CookPvsNP.tm_output_length_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:02:24.151447+00:00
-- url     : https://prove2.me/submissions/72044d12-6493-45aa-b870-6adc677a0c62

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_tm_run_tape_len

open CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem solution (n : ℕ) (w : List Γ) :
    (M.output (M.run n (M.init w))).length ≤ n + w.length + 1 := by
  have hdrop : ∀ c : Cfg Γ M.Q, ((c.head :: c.right).reverse.dropWhile Option.isNone).length
      ≤ 1 + c.right.length := by
    intro c
    have h := List.length_dropWhile_le Option.isNone (c.head :: c.right).reverse
    have h' : (c.head :: c.right).reverse.length = c.right.length + 1 := by
      simp only [List.length_reverse, List.length_cons]
    omega
  have hout : ∀ c : Cfg Γ M.Q, (M.output c).length ≤ 1 + c.right.length := by
    intro c
    have h2 := hdrop c
    simpa [TM.output, add_comm] using h2
  have hinit : (M.init w).left.length + (M.init w).right.length ≤ w.length := by
    simp [TM.init]
  have hrun := tm_run_tape_len (M := M) n (M.init w)
  have hc := hout (M.run n (M.init w))
  omega
