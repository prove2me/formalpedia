-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_eq_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:27.002244+00:00
-- url     : https://prove2.me/submissions/cc9d9a83-b861-47a7-b6a9-cc2837bc3048

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_parityPrefix_congr


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {m n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ m]) :
    oddCount n m = oddCount n' m := by
  have hp := parityPrefix_congr h
  unfold oddCount
  apply Finset.sum_congr rfl
  intro i hi
  have hii : i < m := Finset.mem_range.mp hi
  have hbit := congrFun hp ⟨i, hii⟩
  exact congrArg Fin.val hbit
end FirstPassageLinearTransport
