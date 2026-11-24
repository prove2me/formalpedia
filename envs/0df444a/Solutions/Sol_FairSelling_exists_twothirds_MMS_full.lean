-- Prove2me | solution 1 for FairSelling.exists_twothirds_MMS_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:06.835806+00:00
-- url     : https://prove2.me/submissions/8c2e18c0-1025-4352-9e11-2764baf0df39

import Mathlib
import Definitions.Def_RequestProject_TwoThirds
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_TwoThirdsFull
import Theorems.Thm_FairSelling_exists_full_of_valid
import Theorems.Thm_FairSelling_exists_twothirds_MMS


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Full p Finset.univ ∧
      ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by
  obtain ⟨o, hvalid, ho⟩ := exists_twothirds_MMS v p hn hv hp
  obtain ⟨o', hfull, _, hle⟩ := exists_full_of_valid v p hn hv o hvalid
  exact ⟨o', hfull, fun i => (ho i).trans (hle i)⟩
end FairSelling
