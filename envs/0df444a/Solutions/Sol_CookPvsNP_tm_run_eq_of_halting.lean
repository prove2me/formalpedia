-- Prove2me | solution 1 for CookPvsNP.tm_run_eq_of_halting
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T17:18:19.007986+00:00
-- url     : https://prove2.me/submissions/c08fa0a7-cc5c-4232-82a9-dd70c54493aa

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

theorem solution {Γ : Type} (M : CookPvsNP.TM Γ) (c : CookPvsNP.Cfg Γ M.Q)
    (h : M.IsHalting c) (n : ℕ) : M.run n c = c := by
  unfold CookPvsNP.TM.run
  apply Function.iterate_fixed
  simp [CookPvsNP.TM.step, h]
