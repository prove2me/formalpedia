-- Prove2me | solution 1 for BSLambda.CertFamily.dist_eq_one_or_dist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:06.164797+00:00
-- url     : https://prove2.me/submissions/74e79a5f-02e3-4733-99f4-e505799ea302

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_exists_flip_pair_of_gram_ne_zero
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_card_violSet
public import Theorems.Thm_BSLambda_PartialAssign_violSet_eq_singleton_of_conflict
public import Theorems.Thm_BSLambda_flipSet_flipSet
attribute [local simp] BSLambda.flipSet_flipSet



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) :
    (F.P (F.owner y)).dist x.1 = 1 ∨ (F.P (F.owner x)).dist y.1 = 1 := by
  obtain ⟨p, q, -, hconf, hyf, hp⟩ := F.exists_flip_pair_of_gram_ne_zero hxy hne
  -- Flipping is an involution, so `x` is equally the `{p, q}`-flip of `y`.
  have hxf : x.1 = flipSet y.1 {p, q} := by rw [hyf, flipSet_flipSet]
  rcases hp with hpx | hpy
  · refine Or.inl ?_
    rw [PartialAssign.dist_eq_card_violSet, PartialAssign.violSet_eq_singleton_of_conflict
      (F.owner_sat x) (hyf ▸ F.owner_sat y) hconf hpx.2, Finset.card_singleton]
  · refine Or.inr ?_
    rw [PartialAssign.dist_eq_card_violSet, PartialAssign.violSet_eq_singleton_of_conflict
      (F.owner_sat y) (hxf ▸ F.owner_sat x) hconf.symm hpy.2, Finset.card_singleton]
end BSLambda.CertFamily
