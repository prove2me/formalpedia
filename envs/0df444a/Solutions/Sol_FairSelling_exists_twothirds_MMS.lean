-- Prove2me | solution 1 for FairSelling.exists_twothirds_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:04.509269+00:00
-- url     : https://prove2.me/submissions/ffa32cef-e567-48db-9f42-88417b052677

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
import Theorems.Thm_FairSelling_exists_twothirds_MMS_of_equiMMS
import Theorems.Thm_FairSelling_exists_readjustment


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨v', hv'0, hv'le, hv'MMS, hv'E⟩ := exists_readjustment v p hn hv hp
  obtain ⟨o, hovalid, ho⟩ := exists_twothirds_MMS_of_equiMMS v' p hn hv'0 hp hv'E
  refine ⟨o, hovalid, fun i => ?_⟩
  have h1 : util (v' i) o i ≤ util (v i) o i := by
    unfold util
    have : ∑ g ∈ o.kept i, v' i g ≤ ∑ g ∈ o.kept i, v i g :=
      Finset.sum_le_sum (fun g _ => hv'le i g)
    linarith
  have h2 := ho i
  rw [hv'MMS i] at h2
  linarith
end FairSelling
