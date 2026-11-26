-- Prove2me | solution 1 for ErdosRubinTaylor.adj_of_sconn_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:58.324561+00:00
-- url     : https://prove2.me/submissions/de7b1d2a-791b-414e-a84c-937690f6c464

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
theorem _root_.solution {D : Set V} {x : V} (h : SConn G (insert x D)) (hne : D.Nonempty)
    (hxD : x ∉ D) : ∃ d ∈ D, G.Adj x d := by
  obtain ⟨d, hd⟩ := hne
  rcases (h.rtg (Set.mem_insert x D) (Set.mem_insert_of_mem x hd)).cases_head with
    h' | ⟨c, hc, -⟩
  · exact absurd (h' ▸ hd) hxD
  · rcases hc.2.1 with rfl | hcD
    · exact absurd hc.2.2 (G.loopless.irrefl _)
    · exact ⟨c, hcD, hc.2.2⟩
end ErdosRubinTaylor
