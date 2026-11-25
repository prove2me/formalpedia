-- Prove2me | solution 1 for CliqueMinors.DiracCtx.contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:14.731105+00:00
-- url     : https://prove2.me/submissions/e67631ef-117c-4029-8898-363ceac0fa9d

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_lift_contract
public import Theorems.Thm_CliqueMinors_contractG_adj
public import Theorems.Thm_CliqueMinors_contract_degree
public import Theorems.Thm_CliqueMinors_contract_support


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
open CliqueMinors.DiracCtx
variable {G : SimpleGraph V} {S : Finset V}
namespace CliqueMinors.DiracCtx
theorem _root_.solution (H : DiracCtx G S) {x y : V} (hxy : G.Adj x y)
    (hmerge : 3 ≤ (((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y).card)
    (hcommon : ∀ z, G.Adj x z → G.Adj y z → 4 ≤ G.degree z) : False := by
  apply H.notK4
  refine isMinor_lift_contract (G' := contractG G x y) hxy (fun u v h => (contractG_adj.1 h).2)
    (by omega) ?_
  have hyS : y ∈ S := H.supp _ _ hxy.symm
  refine H.smaller _ (S.erase y) (Finset.card_erase_lt_of_mem hyS)
    ⟨x, Finset.mem_erase.2 ⟨hxy.ne, H.supp _ _ hxy⟩⟩ (contract_support hxy H.supp)
    (contract_degree 3 hxy H.deg hmerge hcommon)
end CliqueMinors.DiracCtx
