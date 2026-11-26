-- Prove2me | solution 1 for FirstPassageLinearTransport.parityPrefix_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:21.053333+00:00
-- url     : https://prove2.me/submissions/d2325c7e-7a6e-4155-b177-88a8eaa56068

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_orbit_modEq

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {M n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ M]) :
    (fun i : Fin M => parityBit n i) =
      (fun i : Fin M => parityBit n' i) := by
  funext i
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt i.isLt
  have hstep : orbit i n ≡ orbit i n' [MOD 2 ^ (j + 1)] := by
    apply orbit_modEq
    rwa [show (i : ℕ) + (j + 1) = M by omega]
  have hdvd : (2 : ℕ) ∣ 2 ^ (j + 1) :=
    dvd_pow_self 2 (Nat.succ_ne_zero j)
  apply Fin.ext
  exact hstep.of_dvd hdvd
end FirstPassageLinearTransport
