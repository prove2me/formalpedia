-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:48.050712+00:00
-- url     : https://prove2.me/submissions/b3000b6b-084a-49df-b513-7a80c066a7a9

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i j : Fin n) (y : ℤ) (hy : y ∈ Iset lam (B0 lam nu) i) :
    |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ lam 0 - lam (Fin.last n) + n + 1 := by
  simp only [Iset, Finset.mem_Icc] at hy
  have hmi : min (len lam i) (B0 lam nu) ≤ lam i.castSucc - lam i.succ := min_le_left _ _
  have a1 : lam (Fin.last n) ≤ lam j.succ := h.1 (Fin.le_last _)
  have a2 : lam j.castSucc ≤ lam 0 := h.1 (Fin.zero_le _)
  have a3 : lam (Fin.last n) ≤ lam i.succ := h.1 (Fin.le_last _)
  have a4 : lam i.castSucc ≤ lam 0 := h.1 (Fin.zero_le _)
  have hj := h.2 j
  have il : ((i : ℕ) : ℤ) < n := by exact_mod_cast i.isLt
  have jl : ((j : ℕ) : ℤ) < n := by exact_mod_cast j.isLt
  rw [abs_le]
  constructor <;> omega
end Formalism.LogVandermondeBounds.flipTwoThree
