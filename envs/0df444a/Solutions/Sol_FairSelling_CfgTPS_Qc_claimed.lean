-- Prove2me | solution 1 for FairSelling.CfgTPS.Qc_claimed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:52.183386+00:00
-- url     : https://prove2.me/submissions/60f38789-5eef-49da-a8f9-5360d57641f2

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
omit [Fintype G] [DecidableEq G]
namespace FairSelling.CfgTPS
theorem _root_.solution (S : Finset G) : ∃ k, req k ≤ vbarSum (w k) p S + Qc w p req k0 S := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' (⟨k0, Finset.mem_univ k0⟩ :
    (Finset.univ : Finset (Fin n)).Nonempty) (fun m => req m - vbarSum (w m) p S)
  refine ⟨k, ?_⟩
  have : gapMin w p req k0 S = req k - vbarSum (w k) p S := hk
  have h2 : gapMin w p req k0 S ≤ Qc w p req k0 S := le_max_right _ _
  rw [this] at h2
  linarith
end FairSelling.CfgTPS
