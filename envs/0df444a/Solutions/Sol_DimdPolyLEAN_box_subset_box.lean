-- Prove2me | solution 1 for DimdPolyLEAN.box_subset_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:10.831228+00:00
-- url     : https://prove2.me/submissions/a8ccccc5-b406-4b38-8283-666dfa1aeb2b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} {J K : MultiIndex d} (hJK : J ≤ K) :
    box J ⊆ box K := by
  intro alpha halpha
  rw [box, Fintype.mem_piFinset] at halpha ⊢
  intro q
  have hq := halpha q
  rw [Finset.mem_range] at hq ⊢
  exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hq) (hJK q))
end DimdPolyLEAN
