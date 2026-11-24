-- Prove2me | solution 1 for FairSelling.exists_SEFX_of_exists_EFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:49:33.744409+00:00
-- url     : https://prove2.me/submissions/6724218a-71d8-4a8c-a14b-4cc67aa909b2

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Theorems.Thm_FairSelling_SEFXs_sellAll
import Theorems.Thm_FairSelling_SEFX_of_SEFXs


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (sellable : Finset G) (A : Fin n → Finset G)
variable {v p sellable A}
namespace FairSelling
theorem _root_.solution (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hp0 : ∀ g ∉ sellable, p g = 0)
    (hEFX : ∃ A : Fin n → Finset G, IsPartitionOf A (Finset.univ \ sellable) ∧ EFXalloc v A) :
    ∃ o : Outcome G n, o.Valid p ∧ o.AllocatesAll ∧ SEFX v p o := by
  obtain ⟨A, hA, hEFX⟩ := hEFX
  obtain ⟨h1, h2, h3⟩ := SEFXs_sellAll hv hp hp0 hA hEFX
  exact ⟨_, h1, h2, SEFX_of_SEFXs h1 h3⟩
end FairSelling
