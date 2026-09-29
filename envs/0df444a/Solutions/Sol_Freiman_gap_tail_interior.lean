-- Prove2me | solution 1 for Freiman.gap_tail_interior
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:42:08.976265+00:00
-- url     : https://prove2.me/submissions/5672b18a-e756-41eb-bff1-e09a011fe159

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_cf_convergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Freiman

theorem solution (b : ℕ → ℕ+) (h : ∀ n, (b n : ℕ) ≤ 4) :
    (1 / 5 : ℝ) < cfValue b ∧ cfValue b < 5 / 6 := by
  have lower (c : ℕ → ℕ+) (hc : ∀ n, (c n : ℕ) ≤ 4) :
      (1 / 5 : ℝ) < cfValue c := by
    have ht := cf_convergence (fun n => c (n + 1))
    have hd0 : (0 : ℝ) < (c 0 : ℕ) := by exact_mod_cast (c 0).pos
    have hd4 : ((c 0 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hc 0
    rw [(cf_convergence c).2.2.2.2]
    apply (lt_div_iff₀ (by linarith [ht.2.2.1])).2
    linarith [ht.2.2.2.1]
  refine ⟨lower b h, ?_⟩
  have hl := lower (fun n => b (n + 1)) (fun n => h (n + 1))
  have hd : (1 : ℝ) ≤ (b 0 : ℕ) := by exact_mod_cast (b 0).pos
  rw [(cf_convergence b).2.2.2.2]
  apply (div_lt_iff₀ (by linarith)).2
  linarith
