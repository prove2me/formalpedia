-- Prove2me | solution 1 for Formalism.HC.Der.Rd.sum_totient_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:29.553354+00:00
-- url     : https://prove2.me/submissions/25d37456-691c-44fa-9b3d-15e5b5b0219f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
namespace Formalism.HC.Der.Rd
theorem _root_.solution {l : ℕ} (hl : l.Prime) (s : ℕ) : ∑ k ∈ range (s + 1), (l ^ k).totient = l ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ hl, pow_succ]
    have h1 : 1 ≤ l := hl.one_lt.le
    calc l ^ s + l ^ s * (l - 1) = l ^ s * (1 + (l - 1)) := by ring
      _ = l ^ s * l := by congr 1; omega
end Formalism.HC.Der.Rd
