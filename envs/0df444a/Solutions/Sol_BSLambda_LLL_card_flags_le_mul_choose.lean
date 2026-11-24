-- Prove2me | solution 1 for BSLambda.LLL.card_flags_le_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:32.876444+00:00
-- url     : https://prove2.me/submissions/de60aa99-6c0b-4096-95f8-3e6ff5956868

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_headOut_none
public import Theorems.Thm_BSLambda_LLL_headOut_some
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_bot_subset_headOut
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


attribute [local simp] BSLambda.LLL.headOut_none
attribute [local simp] BSLambda.LLL.headOut_some

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution {P : Flag1 ι → Prop} [DecidablePred P]
    {H : Finset (ι × Option ι)} {W : Finset ι} {c N : ℕ}
    (hact : ∀ G, P G → G.Active Arc) (hhead : ∀ G, P G → (G.owner, G.top) ∈ H)
    (hW : ∀ G, P G → W ⊆ G.bot) (hbot : ∀ G, P G → G.bot.card = c)
    (hN : ∀ G, P G → (headOut Arc (G.owner, G.top) \ W).card ≤ N) :
    (Finset.univ.filter P).card ≤ H.card * Nat.choose N (c - W.card) := by
  refine (Finset.card_le_card_of_injOn
      (fun G ↦ (⟨(G.owner, G.top), G.bot \ W⟩ : (_ : ι × Option ι) × Finset ι))
      (t := ((Finset.univ.filter P).image fun G ↦ (G.owner, G.top)).sigma
        fun q ↦ (headOut Arc q \ W).powersetCard (c - W.card)) ?_ ?_).trans ?_
  · intro G hG
    rw [Finset.mem_coe] at hG
    have hP : P G := (Finset.mem_filter.mp hG).2
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard]
    refine ⟨Finset.mem_image_of_mem _ hG,
      Finset.sdiff_subset_sdiff (hact G hP).bot_subset_headOut (Finset.Subset.refl W), ?_⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hW G hP), hbot G hP]
  · intro G₁ h₁ G₂ h₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have hq := congrArg Sigma.fst heq
    have hb : G₁.bot \ W = G₂.bot \ W := congrArg Sigma.snd heq
    refine Flag1.ext (congrArg Prod.fst hq) (congrArg Prod.snd hq) ?_
    rw [← Finset.sdiff_union_of_subset (hW G₁ h₁.2), hb,
      Finset.sdiff_union_of_subset (hW G₂ h₂.2)]
  · have hb : ∀ q ∈ (Finset.univ.filter P).image (fun G ↦ (G.owner, G.top)),
        ((headOut Arc q \ W).powersetCard (c - W.card)).card ≤ Nat.choose N (c - W.card) := by
      intro q hq
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose _ (hN G (Finset.mem_filter.mp hG).2)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hb
    have himg : ((Finset.univ.filter P).image fun G ↦ (G.owner, G.top)).card ≤ H.card :=
      Finset.card_le_card (Finset.image_subset_iff.mpr fun G hG ↦
        hhead G (Finset.mem_filter.mp hG).2)
    rw [Finset.card_sigma]
    exact le_trans (by simpa using hsum) (Nat.mul_le_mul_right _ himg)
end BSLambda.LLL
