-- Prove2me | solution 1 for BSLambda.LLL.card_filter_card_inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:58.73698+00:00
-- url     : https://prove2.me/submissions/45b7a510-7944-4319-b5a3-ee8ba4ceeae9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_supp
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_mem_arcSet
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_mem_discSet
public import Theorems.Thm_BSLambda_LLL_mem_fibre
public import Theorems.Thm_BSLambda_LLL_mem_missArcs
public import Theorems.Thm_BSLambda_LLL_mem_missSet
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_mem_ownerGates
public import Theorems.Thm_BSLambda_LLL_mem_zeroSet
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_middles
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.Construction.card_block
attribute [local simp] BSLambda.Construction.gateCoord_fst
attribute [local simp] BSLambda.Construction.ind_eq_false_iff
attribute [local simp] BSLambda.Construction.ind_eq_true_iff
attribute [local simp] BSLambda.Construction.mem_block
attribute [local simp] BSLambda.LLL.Flag1.mem_nonOwners
attribute [local simp] BSLambda.LLL.Flag1.mem_supp
attribute [local simp] BSLambda.LLL.avoid_empty
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.mem_arcSet
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.mem_discSet
attribute [local simp] BSLambda.LLL.mem_fibre
attribute [local simp] BSLambda.LLL.mem_missArcs
attribute [local simp] BSLambda.LLL.mem_missSet
attribute [local simp] BSLambda.LLL.mem_nbr
attribute [local simp] BSLambda.LLL.mem_ownerGates
attribute [local simp] BSLambda.LLL.mem_zeroSet
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.mem_cube
attribute [local simp] BSLambda.PartialAssign.mem_fixedSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_middles
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (V : Finset ι) {s m : ℕ} (hsm : s ≤ m) :
    (Finset.univ.filter fun S : Finset ι => S.card = m ∧ (V ∩ S).card = s).card
      = V.card.choose s * (Fintype.card ι - V.card).choose (m - s) := by
  classical
  -- a pair `(A, B)` with `A ⊆ V` and `B ⊆ Vᶜ` is disjoint and recovered from its union
  have hsplit : ∀ A B : Finset ι, A ⊆ V → B ⊆ Vᶜ →
      Disjoint A B ∧ V ∩ (A ∪ B) = A ∧ (A ∪ B) \ V = B := by
    intro A B h1 h2
    have h2' : ∀ x ∈ B, x ∉ V := fun x hx ↦ Finset.mem_compl.mp (h2 hx)
    refine ⟨Finset.disjoint_left.mpr fun x hx1 hx2 ↦ h2' x hx2 (h1 hx1), ?_, ?_⟩
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun hx ↦ hx.2.resolve_right fun hc ↦ h2' x hc hx.1, fun hx ↦ ⟨h1 hx, Or.inl hx⟩⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun hx ↦ hx.1.resolve_left fun hc ↦ hx.2 (h1 hc), fun hx ↦ ⟨Or.inr hx, h2' x hx⟩⟩
  have key : (Finset.univ.filter fun S : Finset ι ↦ S.card = m ∧ (V ∩ S).card = s).card
      = (V.powersetCard s ×ˢ Vᶜ.powersetCard (m - s)).card := by
    refine Finset.card_nbij' (fun S ↦ (V ∩ S, S \ V)) (fun q ↦ q.1 ∪ q.2) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.coe_filter_univ, Set.mem_ofPred_eq] at hS
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard]
      have h1 : (S ∩ V).card + (S \ V).card = S.card := Finset.card_inter_add_card_sdiff S V
      rw [Finset.inter_comm] at h1
      exact ⟨⟨Finset.inter_subset_left, hS.2⟩,
        fun x hx ↦ Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2, by omega⟩
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hq
      obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hq
      obtain ⟨hdisj, hinter, -⟩ := hsplit q.1 q.2 ha1 hb1
      simp only [Finset.coe_filter_univ, Set.mem_ofPred_eq]
      refine ⟨?_, by rw [hinter, ha2]⟩
      rw [Finset.card_union_of_disjoint hdisj, ha2, hb2]
      omega
    · intro S _
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hq
      obtain ⟨-, hinter, hsdiff⟩ := hsplit q.1 q.2 hq.1.1 hq.2.1
      exact Prod.ext hinter hsdiff
  rw [key, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_compl]
end BSLambda.LLL
