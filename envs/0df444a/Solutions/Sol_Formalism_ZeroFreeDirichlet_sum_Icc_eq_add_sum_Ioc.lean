-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.sum_Icc_eq_add_sum_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:12.081857+00:00
-- url     : https://prove2.me/submissions/05c2c3d0-4cae-4baa-95af-ef4843b0b8af

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
end Formalism.ZeroFreeDirichlet
