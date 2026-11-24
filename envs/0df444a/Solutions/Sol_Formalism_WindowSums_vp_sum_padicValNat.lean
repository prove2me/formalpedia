-- Prove2me | solution 1 for Formalism.WindowSums.vp_sum_padicValNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:09.394897+00:00
-- url     : https://prove2.me/submissions/17a975c9-946e-465a-aa61-5b32dd0e09f5

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace Formalism.WindowSums
theorem _root_.solution (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, padicValNat ℓ i = padicValNat ℓ M.factorial := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      padicValNat.mul (by omega : n + 1 ≠ 0) (Nat.factorial_ne_zero n)]
    omega
end Formalism.WindowSums
