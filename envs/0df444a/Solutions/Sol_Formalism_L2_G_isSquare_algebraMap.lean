-- Prove2me | solution 1 for Formalism.L2.G.isSquare_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:34.346549+00:00
-- url     : https://prove2.me/submissions/81e2df6a-a8c6-45f3-babd-80a785e67902

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
theorem _root_.solution (hp2 : p ≠ 2) (a : F1 p n) : IsSquare (algebraMap (F1 p n) (F2 p n) a) := by
  by_cases ha : a = 0
  · rw [ha, map_zero]; exact ⟨0, by simp⟩
  haveI : Fintype (F1 p n) := Fintype.ofFinite _
  haveI : Fintype (F2 p n) := Fintype.ofFinite _
  have hq : Fintype.card (F1 p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p n (NeZero.ne n)
  have hq2 : Fintype.card (F2 p n) = (p ^ n) ^ 2 := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := F1 p n),
      FiniteField.finrank_extension, GaloisField.card p n (NeZero.ne n)]
  have hchar : ringChar (F2 p n) ≠ 2 := by
    rw [ringChar.eq (F2 p n) p]; exact hp2
  have ha' : algebraMap (F1 p n) (F2 p n) a ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact ha
  rw [FiniteField.isSquare_iff hchar ha', hq2]
  obtain ⟨r, hr⟩ : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  have hexp : (p ^ n) ^ 2 / 2 = (p ^ n - 1) * (r + 1) := by
    rw [hr, show (2 * r + 1) ^ 2 = 2 * (2 * r * (r + 1)) + 1 by ring,
      Nat.mul_add_div (by norm_num : 0 < 2), Nat.add_sub_cancel]
    norm_num
  rw [hexp, pow_mul, ← map_pow, ← hq, FiniteField.pow_card_sub_one_eq_one a ha, map_one, one_pow]
end Formalism.L2.G
