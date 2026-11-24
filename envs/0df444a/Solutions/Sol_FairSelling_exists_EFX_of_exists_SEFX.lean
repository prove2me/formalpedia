-- Prove2me | solution 1 for FairSelling.exists_EFX_of_exists_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:49:02.477796+00:00
-- url     : https://prove2.me/submissions/6603ea0c-bccd-4f0e-b295-2983b388ec8c

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Theorems.Thm_FairSelling_EFXalloc_of_SEFX_full

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution
    (hSEFX : ∀ w : Fin n → G → ℝ, (∀ i g, 0 ≤ w i g) →
      ∃ o : Outcome G n, o.Full (fun _ => 0) ∅ ∧ SEFX w (fun _ => 0) o)
    (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset G, IsPartitionOf A Finset.univ ∧ EFXalloc v A := by
  obtain ⟨o, hfull, hsefx⟩ := hSEFX v hv
  exact ⟨o.kept, EFXalloc_of_SEFX_full v hv _ (fun _ => rfl) o hfull hsefx⟩
end FairSelling
