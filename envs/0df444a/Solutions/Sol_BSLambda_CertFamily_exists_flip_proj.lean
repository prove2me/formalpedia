-- Prove2me | solution 1 for BSLambda.CertFamily.exists_flip_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:04.885797+00:00
-- url     : https://prove2.me/submissions/38d86e38-2b10-4eb1-bf5f-44c38ed061b2

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_exists_flip_pair_of_dist_eq_one
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_eq_flipSet_proj_of_dist_eq_one
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_singleton_flipSet_singleton
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.flipSet_flipSet



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
    ∃ p ∈ (F.P (F.owner x)).fixedSet, y.1 = flipSet ((F.P (F.owner y)).proj x.1) {p} := by
  obtain ⟨p, q, hpq, hconf, hyf, hpi, -⟩ := F.exists_flip_pair_of_dist_eq_one hne hd
  obtain ⟨v, hv, hx_eq⟩ := PartialAssign.eq_flipSet_proj_of_dist_eq_one hd
  -- `x` satisfies `C_i` and `q` is a conflict, so `q` violates `C_j`; the violation set
  -- is the singleton `{v}`, hence `v = q`.
  have hqv : q = v := by
    have hmem := hconf.mem_violSet (F.owner_sat x)
    rwa [hv, Finset.mem_singleton] at hmem
  subst hqv
  -- Now `y = x^{p,q} = ((π x)^q)^{p,q} = (π x)^p`.
  rw [hx_eq] at hyf
  refine ⟨p, hpi, hyf.trans ?_⟩
  rw [Finset.pair_comm, ← flipSet_singleton_flipSet_singleton _ hpq.symm, flipSet_flipSet]
end BSLambda.CertFamily
