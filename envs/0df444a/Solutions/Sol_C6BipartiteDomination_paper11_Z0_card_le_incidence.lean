-- Prove2me | solution 1 for C6BipartiteDomination.paper11_Z0_card_le_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:31.637798+00:00
-- url     : https://prove2.me/submissions/60d96bad-0f62-4d8c-94be-5adeacb4829d

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper10_z0_has_S_neighbor
import Theorems.Thm_C6BipartiteDomination_sum_degreeTo_symm


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hNoIso : HasNoIsolatedVertices G) :
    (Z0Part G D).card ≤ incidenceTotal G D := by
  classical
  have hlocal : ∀ z ∈ Z0Part G D, 1 ≤ degreeTo G (SPart G D) z := by
    intro z hz
    obtain ⟨q, hqS, hqAdj⟩ := paper10_z0_has_S_neighbor G hNoIso hz
    have hmem : q ∈ (SPart G D).filter (fun v => G.Adj z v) :=
      Finset.mem_filter.mpr ⟨hqS, hqAdj⟩
    have hpos : 0 < ((SPart G D).filter (fun v => G.Adj z v)).card :=
      Finset.card_pos.mpr ⟨q, hmem⟩
    unfold degreeTo
    simpa [G.adj_comm] using hpos
  have hsum := Finset.sum_le_sum hlocal
  have hinc := sum_degreeTo_symm G (Z0Part G D) (SPart G D)
  have hinc' :
      (∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z) = incidenceTotal G D := by
    rw [hinc]
    simp [incidenceTotal, kCharge]
  calc
    (Z0Part G D).card = ∑ z ∈ Z0Part G D, (1 : ℕ) := by simp
    _ ≤ ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := hsum
    _ = incidenceTotal G D := hinc'
end C6BipartiteDomination
