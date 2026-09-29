-- Prove2me | solution 1 for CuspForm.isNewAt_or_goodEigensystemOccursAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2dc5efb7-050c-5ceb-be0f-0444c9d6caa8

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Theorems.Thm_ModularForm_alSlash_add_heckeU_alSlash_alSlash
import Theorems.Thm_ModularForm_alSlash_heckeT_comm
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import Theorems.Thm_ModularFormClass_heckeT_heckeU_comm
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_CuspForm_sq_eq_one_of_atkinLehnerLin_eq_smul
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isNewAt_or_goodEigensystemOccursAt

theorem solution {N q : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N * q)) 2) (hf : f.IsNormalizedEigenform)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    f.IsNewAt q ∨ f.GoodEigensystemOccursAt N := by
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0

  have hN0 : N ≠ 0 := fun h => hqN (h ▸ dvd_zero q)
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero hN0 hq.ne_zero⟩

  have hqM : q ∣ N * q := dvd_mul_left q N
  have hsq : ¬ q ^ 2 ∣ N * q := by
    rintro ⟨t, ht⟩
    exact hqN ⟨t, Nat.eq_of_mul_eq_mul_right hq.pos (by rw [ht]; ring)⟩
  obtain ⟨W⟩ := ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hq hqM hsq
  haveI : NeZero W.R := ⟨(ModularForm.AtkinLehnerDatum.R_pos W).ne'⟩
  have hRM : W.R ∣ N * q := ⟨q, W.hM.trans (Nat.mul_comm q W.R)⟩
  have hWR : W.R = N :=
    (Nat.eq_of_mul_eq_mul_left hq.pos ((Nat.mul_comm q N).trans W.hM)).symm

  have hfeig := (CuspForm.isNormalizedEigenform_iff_heckeT f).mp hf
  have hginv : ∀ γ ∈ (CongruenceSubgroup.Gamma0 (N * q) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ ⇑f = ⇑f :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ

  set g : CuspForm (CongruenceSubgroup.Gamma0 W.R) 2 :=
    CuspForm.traceLin W hq (CuspForm.atkinLehnerLin W 2 f) with hgdef
  have hgcoe : ⇑g = ModularForm.alSlash W 2 ⇑f + ModularForm.heckeU 2 q ⇑f := by
    rw [hgdef, CuspForm.coe_traceLin_apply, CuspForm.coe_atkinLehnerLin_apply]
    have h := ModularForm.alSlash_add_heckeU_alSlash_alSlash W 2 hginv
    have h2 : ((q : ℂ) ^ ((2 : ℤ) - 2)) = 1 := by norm_num
    rw [h2, one_smul] at h
    exact h
  by_cases hvanish : g = 0
  ·
    left
    have eU : ModularForm.heckeU 2 q ⇑f = ModularFormClass.qCoeff f q • ⇑f := (hfeig.2 q hq).2 hqM
    have h0 : ModularForm.alSlash W 2 ⇑f + ModularForm.heckeU 2 q ⇑f = 0 := by
      rw [← hgcoe, hvanish]; rfl
    have h1 : CuspForm.atkinLehnerLin W 2 f = (-ModularFormClass.qCoeff f q) • f := by
      apply DFunLike.coe_injective
      show ⇑(CuspForm.atkinLehnerLin W 2 f) = ⇑((-ModularFormClass.qCoeff f q) • f)
      rw [CuspForm.coe_atkinLehnerLin_apply, CuspForm.IsGLPos.coe_smul, _root_.neg_smul, ← eU]
      exact eq_neg_of_add_eq_zero_left h0
    have h2 := CuspForm.sq_eq_one_of_atkinLehnerLin_eq_smul W hf.ne_zero h1
    show ModularFormClass.qCoeff f q ^ 2 = 1
    linear_combination h2
  ·
    right
    have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓR : ¬ ℓ ∣ W.R), ℓ ∉ {ℓ | ℓ ∣ N * q} →
        CuspForm.heckeTLin 2 hℓ hℓR g = ModularFormClass.qCoeff f ℓ • g := by
      intro ℓ hℓ hℓR hℓS
      have hℓM : ¬ ℓ ∣ N * q := hℓS
      have e1 : ModularForm.heckeT 2 ℓ ⇑f = ModularFormClass.qCoeff f ℓ • ⇑f := (hfeig.2 ℓ hℓ).1 hℓM
      have hcop : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr (fun h => hℓM (h ▸ hqM))
      apply DFunLike.coe_injective
      show ⇑(CuspForm.heckeTLin 2 hℓ hℓR g) = ⇑(ModularFormClass.qCoeff f ℓ • g)
      rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul, hgcoe, ModularForm.heckeT_add,
        ← ModularForm.alSlash_heckeT_comm W 2 hℓ hℓM hginv,
        ModularFormClass.heckeT_heckeU_comm f (hΓ (N * q)) hcop, e1, ModularForm.alSlash_smul,
        ModularForm.heckeU_smul, smul_add]
    obtain ⟨h, hh, hcoeff⟩ := CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
      hvanish (fun ℓ => ModularFormClass.qCoeff f ℓ) {ℓ | ℓ ∣ N * q} hT
    have hocc : f.GoodEigensystemOccursAt W.R :=
      ⟨h, hh, fun ℓ hℓ hℓM => hcoeff ℓ hℓ (fun hd => hℓM (hd.trans hRM)) hℓM⟩
    rwa [hWR] at hocc

end S_CuspForm_isNewAt_or_goodEigensystemOccursAt
end P2MW
export P2MW.S_CuspForm_isNewAt_or_goodEigensystemOccursAt (solution)
