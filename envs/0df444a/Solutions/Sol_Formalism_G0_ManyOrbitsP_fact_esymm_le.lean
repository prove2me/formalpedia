-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.fact_esymm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:22.816281+00:00
-- url     : https://prove2.me/submissions/5f28ed57-1966-41dd-a1c1-dff074e77371

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Theorems.Thm_Formalism_G0_ManyOrbitsP_add_pow_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    (n.factorial : ℝ) * s.esymm n ≤ s.sum ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
      simp
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ t.sum := Multiset.sum_nonneg ht
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      have e : (a ::ₘ t).esymm (n + 1) = t.esymm (n + 1) + a * t.esymm n := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      have h1 := ih ht (n + 1)
      have h2 := ih ht n
      have h3 := add_pow_ge t.sum a hS ha n
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * a)
      rw [e, Multiset.sum_cons, add_comm a t.sum]
      rw [Nat.factorial_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e5 : ((n : ℝ) + 1) * (n.factorial : ℝ) * (t.esymm (n + 1) + a * t.esymm n) =
          ((n : ℝ) + 1) * (n.factorial : ℝ) * t.esymm (n + 1) + ((n : ℝ) + 1) * a * ((n.factorial : ℝ) * t.esymm n) := by
        ring
      linarith [h1, h3, h4, e5]
end Formalism.G0.ManyOrbitsP
