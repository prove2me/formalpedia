-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.log_le_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:31.523866+00:00
-- url     : https://prove2.me/submissions/d2eb5103-df77-4e98-9419-868c44f2b75d

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine

section
-- module Solutions.EditMulticoloring.RamParams
/-!
# Part P (q379): logarithms and powers

Register convention: inputs in arbitrary registers below `S`; outputs at `S`, `S + 1`, …;
scratch above the outputs.  Each program's frame lemma lists the registers it may write.

* `floorLogW b N T S`: `S := Nat.log (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`
  (needs `Nat.log … ≤ regs T`, loop count `regs T`); writes `S .. S+3`.
* `ceilLogW b N T S`: `S := ceilLog (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`; `S .. S+3`.
* `powW a e S`: `S := regs a ^ regs e`; writes only `S`.
* `radW q t lR S`: `S := radiusBound q (2 t) (regs lR)`; writes `S .. S+2`.
* `rhoW q t nR hR qhR S`: `S := shortLength q t (regs hR)`; writes `S .. S+8`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Logs
variable (inp : ℕ → ℕ) (B : ℕ)

theorem log_le_of_pos_oai {b n : ℕ} (hb : 2 ≤ b) : Nat.log b n ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 := Nat.pow_log_le_self b h.ne'
    have h2 : Nat.log b n < b ^ Nat.log b n := Nat.lt_pow_self (by omega)
    omega

/-! ### The short length `ρ = shortLength q t h` -/

end Logs

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.log_le_of_pos_oai := @EditMulticoloring.Dev.Ram.log_le_of_pos_oai
