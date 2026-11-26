-- Prove2me | solution 1 for C6BipartiteDomination.paper10_z0_has_S_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:57.030415+00:00
-- url     : https://prove2.me/submissions/94ede43d-1a0f-4116-814e-bd06b0c314ec

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_PPart
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hNoIso : HasNoIsolatedVertices G) {z : V}
    (hz : z ∈ Z0Part G D) :
    ∃ q ∈ SPart G D, G.Adj z q := by
  classical
  obtain ⟨q, hqAdj⟩ := hNoIso z
  have hzInfo := (mem_Z0Part G D z).mp hz
  have hzPart := (mem_ZPart G D z).mp hzInfo.1
  have hqNotD : q ∉ D := by
    intro hqD
    exact hzPart.2 q hqD hqAdj
  have hqNotW0 : q ∉ W0Part G D := by
    intro hqW0
    exact hzInfo.2 q hqW0 hqAdj
  have hqWB : q ∈ WBPart G D := (mem_WBPart G D q).mpr ⟨hqNotD, hqNotW0⟩
  have hqNotP : q ∉ PPart G D := by
    intro hqP
    obtain ⟨b, hbB, hqPriv⟩ := (mem_PPart G D q).mp hqP
    have hzEqB : z = b :=
      ((mem_privateExternalNeighbors G D b q).mp hqPriv).2 z hzPart.1 |>.mp hqAdj
    subst b
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G (D := D)) hz hbB).elim
  exact ⟨q, (mem_SPart G D q).mpr ⟨hqWB, hqNotP⟩, hqAdj⟩
end C6BipartiteDomination
