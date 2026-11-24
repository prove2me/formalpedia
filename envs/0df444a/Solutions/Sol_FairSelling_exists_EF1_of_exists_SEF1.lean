-- Prove2me | solution 1 for FairSelling.exists_EF1_of_exists_SEF1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:49:24.462624+00:00
-- url     : https://prove2.me/submissions/3a3f598b-9ad0-4a37-b5e9-d6d00e7cb311

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Theorems.Thm_FairSelling_EF1alloc_of_SEF1_full

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution
    (hSEF1 : ∀ w : Fin n → G → ℝ, (∀ i g, 0 ≤ w i g) →
      ∃ o : Outcome G n, o.Full (fun _ => 0) ∅ ∧ SEF1 w (fun _ => 0) o)
    (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset G, IsPartitionOf A Finset.univ ∧ EF1alloc v A := by
  obtain ⟨o, hfull, hsef1⟩ := hSEF1 v hv
  exact ⟨o.kept, EF1alloc_of_SEF1_full v hv _ (fun _ => rfl) o hfull hsef1⟩
end FairSelling
