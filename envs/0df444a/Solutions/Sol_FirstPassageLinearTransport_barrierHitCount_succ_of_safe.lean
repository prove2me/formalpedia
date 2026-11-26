-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_succ_of_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:35.86039+00:00
-- url     : https://prove2.me/submissions/040b1a71-0f24-4ebe-a72d-36adfb48adde

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : ¬a < |(y : ℝ)|) :
    barrierHitCount a (r + 1) y =
      barrierHitCount a r (y - 1) + barrierHitCount a r (y + 1) := by
  classical
  have hc :
      Fintype.card
          {v : Fin (r + 1) → Bool // hitsBarrierFrom a (r + 1) y v} =
        Fintype.card
          (Σ b : Bool,
            {w : Fin r → Bool //
              hitsBarrierFrom a r (y + boolWalkStep b) w}) :=
    Fintype.card_congr (safeHitSuccEquiv (r := r) hy)
  rw [Fintype.card_sigma, Fintype.sum_bool] at hc
  have hcard (s : ℕ) (z : ℤ) :
      Fintype.card {v : Fin s → Bool // hitsBarrierFrom a s z v} =
        barrierHitCount a s z := by
    rw [barrierHitCount, Fintype.card_subtype]
  rw [hcard, hcard, hcard] at hc
  simpa [sub_eq_add_neg, add_comm] using hc
end FirstPassageLinearTransport
