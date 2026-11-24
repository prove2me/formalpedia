-- Prove2me | solution 1 for FairSelling.PhaseTPS.pstep_assign_any
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:17.583866+00:00
-- url     : https://prove2.me/submissions/3c0a342d-31b3-442c-918f-47ca35f4f9bd

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhase
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Theorems.Thm_FairSelling_PhaseTPS_pstep_assign

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k : Fin n}
    {S S₀own S₀ext : Finset G}
    (hSpool : S ⊆ s.pool) (hOpool : S₀own ⊆ s.pool) (hEpool : S₀ext ⊆ s.pool)
    (hSO : Disjoint S S₀own) (hSE : Disjoint S S₀ext) (hOE : Disjoint S₀own S₀ext)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hfin : q + r ≤ s.bank + (s.cash k + s.resv k - ∑ g ∈ s.own k, p g)
              + (∑ g ∈ S₀own, p g) + ∑ g ∈ S₀ext, p g)
    (hself : ∑ g ∈ S₀own, p g ≤ q + r)
    (hpure : (∀ g ∈ S₀ext, PureGood v p (insert k s.served) g) ∨
      (S = ∅ ∧ S₀own = ∅ ∧ r = 0 ∧ ∃ g0, S₀ext = {g0} ∧ q ≤ p g0))
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k → (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : ∀ j, j ∉ insert k s.served →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀own, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  by_cases hkpure : ∀ g ∈ s.ext k, PureGood v p s.served g
  · exact pstep_assign v p eps hn hp heps hs hSpool hOpool hEpool hSO hSE hOE hq hr hfin
      hself hpure hclaim hkeep hsafenew hcostnew hkpure
  · exact hcarrier hn hp heps hs hSpool hOpool hEpool hSO hSE hOE hq hr hfin
      hself hpure hclaim hkpure hkeep hsafenew hcostnew
end FairSelling.PhaseTPS
