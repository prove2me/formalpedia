-- Prove2me | solution 1 for ChromaticReconstruction.swap_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:44:32.692591+00:00
-- url     : https://prove2.me/submissions/3cc70ad9-89d3-45f6-b245-75e3d8e31c7e

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_rfv_le
import Theorems.Thm_ChromaticReconstruction_map_rf_vx
import Theorems.Thm_ChromaticReconstruction_sB_spec
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_lf_mem_edgeSet
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution (hn : 2 * c + 3 ≤ n) (hp : p = c ∨ p = c + 1)
    (hF : F ⊆ (PL n p).edgeFinset) (hb : HasBrk n c F) :
    F.image (Sym2.map (rf n c (sB n c F))) ⊆ (PL n (2 * c + 1 - p)).edgeFinset := by
  obtain ⟨hs1, hs2, hbrk, -⟩ := sB_spec hb
  set s := sB n c F
  intro e he
  obtain ⟨e, heF, rfl⟩ := mem_image.1 he
  have hpn : p < n := by omega
  have heE := (mem_edgeSet_PL hpn e).1 (SimpleGraph.mem_edgeFinset.1 (hF heF))
  rw [SimpleGraph.mem_edgeFinset]
  rcases heE with ⟨i, hi, rfl⟩ | rfl
  · have hi1 : i ≠ c + s := fun h => hbrk.2 (h ▸ heF)
    have hi2 : ¬ (s ≤ c ∧ i = c - s) := by
      rintro ⟨h1, h2⟩
      rcases hbrk.1 with h | h
      · omega
      · exact h (h2 ▸ heF)
    rw [pe, map_rf_vx (by omega) (by omega), SimpleGraph.mem_edgeSet,
      PL_adj_vx (rfv_le (by omega) (by omega)) (rfv_le (by omega) (by omega))]
    unfold rfv
    split_ifs <;> omega
  · rw [lf, map_rf_vx (by omega) le_rfl]
    have e1 : rfv c s p = 2 * c + 1 - p := by unfold rfv; split_ifs <;> omega
    have e2 : rfv c s n = n := by unfold rfv; split_ifs <;> omega
    rw [e1, e2]
    exact lf_mem_edgeSet (by omega)
end ChromaticReconstruction
