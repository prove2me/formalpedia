-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.BR.semiGenusZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:42.927778+00:00
-- url     : https://prove2.me/submissions/a4fd183e-886f-49ec-b93f-1356d5bd0f89

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_AlgebraMapNeZero
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_loc_iff_of_isom
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_algebraMap_ne_zero__8e24046a48f0
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_smul_eq_alg
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_gl_of_isom
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_apply
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_nondeg
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_symm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_selfDualMod_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locR_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR
theorem _root_.solution (hZ : SemiGenusZLoc) : SemiGenusZ := by
  intro E _ _ _ n J hK hJh hdet r s z L M hLfg hMfg hLsp hMsp hLd hMd hsz hU hSL hSM hzL hzM hPL hPM p hp
  have hpP := hp.isPrime

  have hU' : ∀ w ∈ Submodule.span E (Set.range s),
      w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup ↔ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup := by
    intro w hw
    change w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M
    constructor
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).1 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).2 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
  have hsplit : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ w ∈ N, ∃ w₁ ∈ N, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      ∀ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup, ∃ w₁ ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup,
        w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, hJ J (s a) (w - w₁) = 0 := by
    intro N hN w hw
    obtain ⟨t, ht, htw⟩ := hw
    obtain ⟨u, huN, hus, hu0⟩ := hN _ htw
    have ht0 := algebraMap_ne_zero' hpP ht
    refine ⟨(algebraMap (𝓞 E) E t)⁻¹ • u, ⟨t, ht, ?_⟩, Submodule.smul_mem _ _ hus, fun a => ?_⟩
    · rw [smul_eq_alg, smul_smul, mul_inv_cancel₀ ht0, one_smul]; exact huN
    · have e : w - (algebraMap (𝓞 E) E t)⁻¹ • u = (algebraMap (𝓞 E) E t)⁻¹ • (t • w - u) := by
        rw [smul_eq_alg, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e, map_smul, smul_eq_mul, hJ_apply, hu0 a, mul_zero]
  have hprim : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ c : E, c • z ∈ N → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ c : E, c • z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup → c ∈ locRing p := by
    intro N hN c hc
    obtain ⟨t, ht, htc⟩ := hc
    rw [smul_eq_alg, smul_smul] at htc
    obtain ⟨r, hr⟩ := hN _ htc
    have ht0 := algebraMap_ne_zero' hpP ht
    rw [mem_locRing, mem_locR_iff hpP]
    refine ⟨r, t, ht, ?_⟩
    rw [hr]; field_simp
  have hzloc : ∀ N : Submodule (𝓞 E) (Fin n → E), z ∈ N → z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup :=
    fun N hz => ⟨1, one_mem _, by rw [one_smul]; exact hz⟩
  obtain ⟨g, hg, hgs, hgz, hm⟩ := hZ E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp s z
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
    hsz hU' (hsplit L hSL) (hsplit M hSM) (hzloc L hzL) (hzloc M hzM) (hprim L hPL) (hprim M hPM)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  refine ⟨γ, hγ, fun a => by rw [hγg, hgs a], by rw [hγg, hgz], loc_iff_of_isom g hm γ hγg⟩
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
