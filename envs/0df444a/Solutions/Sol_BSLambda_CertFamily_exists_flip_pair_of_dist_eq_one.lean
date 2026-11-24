-- Prove2me | solution 1 for BSLambda.CertFamily.exists_flip_pair_of_dist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:05.392083+00:00
-- url     : https://prove2.me/submissions/2545812c-2a44-4a24-87e7-1bf1669df548

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_ne_of_dist_eq_one
public import Theorems.Thm_BSLambda_CertFamily_exists_flip_pair_of_gram_ne_zero
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_Sat_eq_of_fixed
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_card_violSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet_iff_exists_ne
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.flipSet_apply_of_mem



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧ p ∈ (F.P (F.owner x)).fixedSet ∧
        p ∉ (F.P (F.owner y)).fixedSet := by
  obtain ⟨p, q, hpq, hconf, hyf, hp⟩ :=
    F.exists_flip_pair_of_gram_ne_zero (F.ne_of_dist_eq_one hd) hne
  refine ⟨p, q, hpq, hconf, hyf, hp.resolve_right fun h ↦ ?_⟩
  obtain ⟨b, hb⟩ := PartialAssign.mem_fixedSet_iff_exists.1 h.1
  have hxp : x.1 p ≠ b := by
    have hyp : y.1 p = b := (F.owner_sat y).eq_of_fixed hb
    rw [hyf, flipSet_apply_of_mem (Finset.mem_insert_self p {q})] at hyp
    rw [← hyp]
    exact (Bool.not_ne_self _).symm
  -- Both `p` and `q` would then be violated literals of `C_j` at `x`, contradicting `hd`.
  have hsub : ({p, q} : Finset V) ⊆ (F.P (F.owner y)).violSet x.1 :=
    Finset.insert_subset (PartialAssign.mem_violSet_iff_exists_ne.2 ⟨b, hb, hxp⟩)
      (Finset.singleton_subset_iff.2 (hconf.mem_violSet (F.owner_sat x)))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hpq, ← PartialAssign.dist_eq_card_violSet, hd] at hcard
  omega
end BSLambda.CertFamily
