-- Prove2me | solution 1 for DimdPolyLEAN.finite_subset_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:11.627829+00:00
-- url     : https://prove2.me/submissions/40b570f7-0cd0-46f2-af39-12d6fe3908e3

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
    {d : Nat} (E : Finset (Idx d)) :
    ∃ J : MultiIndex d, E ⊆ box J := by
  refine ⟨fun q => Finset.sup E (fun alpha : Idx d => alpha q), ?_⟩
  intro alpha halpha
  rw [box, Fintype.mem_piFinset]
  intro q
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Finset.le_sup (s := E) (f := fun beta : Idx d => beta q) halpha
end DimdPolyLEAN
