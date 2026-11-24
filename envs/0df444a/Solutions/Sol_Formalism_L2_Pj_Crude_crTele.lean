-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crTele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:45.832272+00:00
-- url     : https://prove2.me/submissions/b1a829d3-4799-4d9b-878b-6728d0ab6d0c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (f : ℕ → ℕ) (R : ℕ) (hf : ∀ j, j < R → f (j + 1) ≤ f j) (hR : f R = 0) :
    ∀ d i, i + d = R → ∑ j ∈ Finset.range R, (if i ≤ j then f j - f (j + 1) else 0) = f i := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp only [Nat.add_zero] at hi
    subst hi
    rw [hR]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega)]
  | succ d ih =>
    intro i hi
    have h1 := ih (i + 1) (by omega)
    have hsplit : ∀ j, (if i ≤ j then f j - f (j + 1) else 0) =
        (if i + 1 ≤ j then f j - f (j + 1) else 0) + (if j = i then f j - f (j + 1) else 0) := by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · by_cases h' : i ≤ j
        · rw [if_pos h', if_pos (by omega), if_neg h, add_zero]
        · rw [if_neg h', if_neg (by omega), if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, h1, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by omega))]
    have := hf i (by omega)
    omega
end Formalism.L2.Pj.Crude
