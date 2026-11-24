-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_two_nonowner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:22.412231+00:00
-- url     : https://prove2.me/submissions/946e7de6-cca6-4d46-b69c-4871d8add96c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_mem_ownerGates
public import Theorems.Thm_BSLambda_LLL_mem_arcSet
public import Theorems.Thm_BSLambda_LLL_mem_missSet
public import Theorems.Thm_BSLambda_LLL_missSet_subset_missSet
public import Theorems.Thm_BSLambda_LLL_mem_zeroSet
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_supp
public import Theorems.Thm_BSLambda_LLL_mem_missArcs
public import Theorems.Thm_BSLambda_LLL_mem_discSet
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_IsTournament_arc_of_not_arc
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_mem_fibre
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_ne
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
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
attribute [local simp] BSLambda.LLL.avoid_empty
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.mem_fibre
attribute [local simp] BSLambda.LLL.mem_nbr
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


attribute [local simp] BSLambda.LLL.mem_ownerGates
attribute [local simp] BSLambda.LLL.mem_arcSet
attribute [local simp] BSLambda.LLL.mem_missSet
attribute [local gcongr] BSLambda.LLL.missSet_subset_missSet
attribute [local simp] BSLambda.LLL.mem_zeroSet
attribute [local simp] BSLambda.LLL.Flag1.mem_nonOwners
attribute [local simp] BSLambda.LLL.Flag1.mem_supp
attribute [local simp] BSLambda.LLL.mem_missArcs
attribute [local simp] BSLambda.LLL.mem_discSet
section
@[expose] public section
namespace BSLambda
namespace LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
section ArcSet
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
variable (hT : IsTournament Arc)
include hT
end ArcSet
section MissSet
omit [Fintype ι] [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ γ' : ι → ι → Fin r} {Z : ι → Finset (Fin r)}
  {T T' S : Finset ι} {i j : ι}
end MissSet
namespace Flag1
section Membership
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}
namespace Active
variable (hF : F.Active Arc)
include hF
end Active
end Membership
end Flag1
section MissArcs
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
end MissArcs
private theorem subset_pair_of_card_erase_le_one {α : Type*} [DecidableEq α] [Nonempty α]
    {s : Finset α} {a : α} (h : (s.erase a).card ≤ 1) : ∃ z, s ⊆ {a, z} := by
  obtain ⟨z, hz⟩ := Finset.card_le_one_iff_subset_singleton.mp h
  refine ⟨z, fun x hx ↦ ?_⟩
  rcases eq_or_ne x a with rfl | hxa
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hz (Finset.mem_erase.mpr ⟨hxa, hx⟩))
end LLL
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} {h : ι} (hh : h ∈ S)
    {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j) {j : ι} (hj : j ∈ S.erase h)
    (hbud : (Z j).card + (missSet Arc γ Z S j).card ≤ 2) :
    (∃ z : Fin r, Z j ⊆ {γ h j, z}) ∧
      (missSet Arc γ Z (S.erase h) j).card + (if Z j ⊆ {γ h j} then 0 else 1) ≤ 1 := by
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩⟩
  have hjh : j ≠ h := Finset.ne_of_mem_erase hj
  have hle : (missSet Arc γ Z (S.erase h) j).card ≤ (missSet Arc γ Z S j).card :=
    Finset.card_le_card (missSet_subset_missSet (Finset.erase_subset _ _))
  cases hA : Arc h j with
  | true =>
    -- the owner gate already occupies one of the two units of budget
    have hmem : γ h j ∈ Z j := hgate j (Finset.mem_of_mem_erase hj) (by rw [hA])
    have hz1 : 1 ≤ (Z j).card := Finset.card_pos.mpr ⟨_, hmem⟩
    have hce : ((Z j).erase (γ h j)).card = (Z j).card - 1 := Finset.card_erase_of_mem hmem
    refine ⟨subset_pair_of_card_erase_le_one (by omega), ?_⟩
    by_cases hsub : Z j ⊆ {γ h j}
    · rw [if_pos hsub]
      omega
    · rw [if_neg hsub]
      obtain ⟨z, hzZ, hzne⟩ := Finset.not_subset.1 hsub
      have h2 : 2 ≤ (Z j).card := Finset.one_lt_card.2
        ⟨_, hmem, z, hzZ, fun hc ↦ hzne (Finset.mem_singleton.2 hc.symm)⟩
      omega
  | false =>
    -- the automatic miss `j → h` already occupies one of the two units of budget
    have hhM : h ∈ missSet Arc γ Z S j :=
      mem_missSet.2 ⟨hh, hT.arc_of_not_arc hjh hA, by simp [hZh]⟩
    have hM'card : (missSet Arc γ Z (S.erase h) j).card + 1 ≤ (missSet Arc γ Z S j).card := by
      have hsub : missSet Arc γ Z (S.erase h) j ⊆ (missSet Arc γ Z S j).erase h :=
        Finset.subset_erase.2 ⟨missSet_subset_missSet (Finset.erase_subset _ _),
          fun hc ↦ Finset.notMem_erase h S (mem_missSet.1 hc).1⟩
      have hcard := Finset.card_le_card hsub
      have hpos : 1 ≤ (missSet Arc γ Z S j).card := Finset.card_pos.2 ⟨h, hhM⟩
      rw [Finset.card_erase_of_mem hhM] at hcard
      omega
    refine ⟨subset_pair_of_card_erase_le_one (Finset.card_erase_le.trans (by omega)), ?_⟩
    by_cases hsub : Z j ⊆ {γ h j}
    · rw [if_pos hsub]
      omega
    · rw [if_neg hsub]
      obtain ⟨z, hzZ, -⟩ := Finset.not_subset.1 hsub
      have h1 : 1 ≤ (Z j).card := Finset.card_pos.2 ⟨z, hzZ⟩
      omega
end BSLambda.LLL
