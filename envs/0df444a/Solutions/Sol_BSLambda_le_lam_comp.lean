-- Prove2me | solution 1 for BSLambda.le_lam_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:44.101804+00:00
-- url     : https://prove2.me/submissions/5bbf2e99-8d11-4774-8fbf-31ee2888b02b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_exists_apply_eq_and_ne_zero
public import Theorems.Thm_BSLambda_adj_comp_mulVec_prod
public import Theorems.Thm_BSLambda_prod_eigenvector_ne_zero
public import Theorems.Thm_BSLambda_exists_top_eigenvector
public import Theorems.Thm_BSLambda_lam_nonneg
public import Theorems.Thm_BSLambda_le_lam_of_eigenvector


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool) :
    lam f * lam g ≤ lam (comp f g) := by
  rcases eq_or_lt_of_le (lam_nonneg g) with hg | hg
  · rw [← hg, mul_zero]
    exact lam_nonneg _
  obtain ⟨u, hu0, hu⟩ := exists_top_eigenvector g
  obtain ⟨v, hv0, hv⟩ := exists_top_eigenvector f
  exact le_lam_of_eigenvector (comp f g)
    (prod_eigenvector_ne_zero g (exists_apply_eq_and_ne_zero g hg.ne' hu0 hu) hv0)
    (adj_comp_mulVec_prod f g hu hv)
end BSLambda
