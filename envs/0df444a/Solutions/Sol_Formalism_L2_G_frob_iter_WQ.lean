-- Prove2me | solution 1 for Formalism.L2.G.frob_iter_WQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:33.488342+00:00
-- url     : https://prove2.me/submissions/78147863-7209-4adb-b2ef-cf10d5ac6a9f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution (x : WQ p n) : (WittVector.frobenius^[n]) x = x := by
  have hit : ∀ (m : ℕ) (y : WQ p n) (k : ℕ),
      ((WittVector.frobenius^[m]) y).coeff k = y.coeff k ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro y k; simp
    | succ m ih =>
      intro y k
      rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]
  ext k
  rw [hit]
  haveI : Fintype (F1 p n) := Fintype.ofFinite _
  have hcard : Fintype.card (F1 p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p n (NeZero.ne n)
  rw [← hcard, FiniteField.pow_card]
end Formalism.L2.G
