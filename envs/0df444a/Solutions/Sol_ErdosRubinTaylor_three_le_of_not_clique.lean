-- Prove2me | solution 1 for ErdosRubinTaylor.three_le_of_not_clique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:44.181557+00:00
-- url     : https://prove2.me/submissions/3ff01771-09ed-48ba-b633-0bc4f07ce7d1

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
public import Theorems.Thm_ErdosRubinTaylor_SConn_rtg


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
namespace ErdosRubinTaylor
theorem _root_.solution [Finite V] {T : Set V} (hT : SConn G T) (hK : ¬ IsCliqueOn G T) :
    3 ≤ T.ncard := by
  simp only [IsCliqueOn, not_forall] at hK
  obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := hK
  rcases (hT.rtg hx hy).cases_head with h | ⟨c, hc, -⟩
  · exact absurd h hxy
  · have hcx : c ≠ x := (G.ne_of_adj hc.2.2).symm
    have hcy : c ≠ y := fun h => hnadj (h ▸ hc.2.2)
    have hsub : ({x, y, c} : Set V) ⊆ T := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hc.2.1
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hcy.symm] at this
    · exact this
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxy, hcx.symm⟩
end ErdosRubinTaylor
