-- Prove2me | solution 1 for CuspForm.heckeTLin_rescaleLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a0ac7bf1-2ec7-5bf9-b106-502b1c27d24d

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeTLin_rescaleLin

set_option autoImplicit false

namespace AlliAux2O7

open CongruenceSubgroup ModularForm ModularFormClass FreyPackage.ModMCarrier

private lemma qCoeff_rescaleLin {R M d : ℕ} [NeZero M] (hdRM : d * R ∣ M)
    (f : CuspForm (Gamma0 R) 2) (n : ℕ) :
    qCoeff ⇑(rescaleLin hdRM 2 f) n
      = (d : ℂ) * (if d ∣ n then qCoeff ⇑f (n / d) else 0) := by
  have hΓM : (1 : ℝ) ∈ Subgroup.strictPeriods (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by simp
  have hΓR : (1 : ℝ) ∈ Subgroup.strictPeriods (Gamma0 R : Subgroup (GL (Fin 2) ℝ)) := by simp
  have hdM : d ∣ M := dvd_of_mul_right_dvd hdRM
  have hd0 : d ≠ 0 := fun h => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h ▸ hdM))

  set g : UpperHalfPlane → ℂ := fun τ ↦ ⇑f (heckeDiagMatrix d • τ) with hg_def
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hcoe : ⇑(rescaleLin hdRM 2 f) = (d : ℂ) • g := by
    funext τ
    simp only [hg_def, Pi.smul_apply, smul_eq_mul, coe_rescaleLin_apply]
    rw [slash_heckeDiagMatrix_apply 2 hd0]
    congr 1
    norm_num
  have hgcoe : g = ⇑((1 / (d : ℂ)) • rescaleLin hdRM 2 f) := by
    funext τ
    rw [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, hcoe, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, one_div, inv_mul_cancel₀ hdc, one_mul]
  have hganalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 g) 0 := by
    rw [hgcoe]
    exact ModularFormClass.analyticAt_cuspFunction_zero ((1 / (d:ℂ)) • rescaleLin hdRM 2 f)
      one_pos hΓM

  rw [hcoe]
  unfold qCoeff
  rw [UpperHalfPlane.qExpansion_smul hganalytic (d : ℂ), PowerSeries.coeff_smul, smul_eq_mul]
  congr 1

  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f hΓR hd0 n

private lemma coeffHeckeT_dshift_comm {ℓ d : ℕ} (hℓ0 : ℓ ≠ 0) (hd0 : d ≠ 0)
    (hℓd : Nat.Coprime ℓ d) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT 2 ℓ (fun m ↦ (d : ℂ) * (if d ∣ m then a (m / d) else 0)) n
      = (d : ℂ) * (if d ∣ n then coeffHeckeT 2 ℓ a (n / d) else 0) := by
  have hdpos := Nat.pos_of_ne_zero hd0
  have hℓpos := Nat.pos_of_ne_zero hℓ0
  rw [coeffHeckeT_apply, coeffHeckeT_apply]
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    simp only [if_pos (dvd_mul_right d m)]
    have hdnℓ : d ∣ d * m * ℓ := ⟨m * ℓ, by ring⟩
    rw [if_pos hdnℓ, Nat.mul_div_cancel_left m hdpos,
      show d * m * ℓ / d = m * ℓ from by
        rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hdpos]]
    by_cases hℓn : ℓ ∣ d * m
    · have hℓm : ℓ ∣ m := hℓd.dvd_of_dvd_mul_left hℓn
      obtain ⟨c, rfl⟩ := hℓm
      rw [if_pos hℓn, if_pos (dvd_mul_right ℓ c),
        show d * (ℓ * c) / ℓ = d * c from by
          rw [← Nat.mul_assoc, Nat.mul_comm d ℓ, Nat.mul_assoc, Nat.mul_div_cancel_left _ hℓpos],
        if_pos (dvd_mul_right d c), Nat.mul_div_cancel_left c hdpos,
        Nat.mul_div_cancel_left c hℓpos]
      ring
    · have hℓm : ¬ ℓ ∣ m := fun h => hℓn (h.mul_left d)
      rw [if_neg hℓn, if_neg hℓm]; ring
  · rw [if_neg hdn]
    have hdnℓ : ¬ d ∣ n * ℓ := fun h => hdn (hℓd.symm.dvd_of_dvd_mul_right h)
    rw [if_neg hdnℓ]
    by_cases hℓn : ℓ ∣ n
    · have hdnℓ' : ¬ d ∣ n / ℓ := fun h => hdn (by
        obtain ⟨c, rfl⟩ := hℓn; obtain ⟨e, he⟩ := h
        rw [Nat.mul_div_cancel_left c hℓpos] at he
        exact ⟨ℓ * e, by rw [he]; ring⟩)
      rw [if_pos hℓn, if_neg hdnℓ']; ring
    · rw [if_neg hℓn]; ring

end AlliAux2O7

open AlliAux2O7 CongruenceSubgroup ModularFormClass ModularForm FreyPackage.ModMCarrier in
theorem solution {R M d ℓ : ℕ} [NeZero M] (hdRM : d * R ∣ M)
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓR : ¬ ℓ ∣ R)
    (f : CuspForm (Gamma0 R) 2) :
    CuspForm.heckeTLin 2 hℓ hℓM (rescaleLin hdRM 2 f)
      = rescaleLin hdRM 2 (CuspForm.heckeTLin 2 hℓ hℓR f) := by
  have hΓM : (1 : ℝ) ∈ Subgroup.strictPeriods (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by simp
  have hΓR : (1 : ℝ) ∈ Subgroup.strictPeriods (Gamma0 R : Subgroup (GL (Fin 2) ℝ)) := by simp

  have hdM : d ∣ M := dvd_of_mul_right_dvd hdRM
  have hd0 : d ≠ 0 := fun h => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h ▸ hdM))
  have hℓd : Nat.Coprime ℓ d := hℓ.coprime_iff_not_dvd.mpr (fun h => hℓM (h.trans hdM))

  refine eq_of_forall_qCoeff_eq hΓM ?_
  intro n

  show qCoeff ⇑(CuspForm.heckeTLin 2 hℓ hℓM (rescaleLin hdRM 2 f)) n
      = qCoeff ⇑(rescaleLin hdRM 2 (CuspForm.heckeTLin 2 hℓ hℓR f)) n
  rw [show ⇑(CuspForm.heckeTLin 2 hℓ hℓM (rescaleLin hdRM 2 f))
        = heckeT 2 ℓ ⇑(rescaleLin hdRM 2 f) from CuspForm.coe_heckeTLin_apply 2 hℓ hℓM _]
  rw [qCoeff_heckeT (rescaleLin hdRM 2 f) hΓM hℓ.ne_zero n]

  rw [show (qCoeff ⇑(rescaleLin hdRM 2 f))
    = (fun m => (d : ℂ) * (if d ∣ m then qCoeff ⇑f (m / d) else 0)) from
      funext fun m => qCoeff_rescaleLin hdRM f m]

  rw [qCoeff_rescaleLin hdRM (CuspForm.heckeTLin 2 hℓ hℓR f) n]

  rw [show ⇑(CuspForm.heckeTLin 2 hℓ hℓR f) = heckeT 2 ℓ ⇑f from
    CuspForm.coe_heckeTLin_apply 2 hℓ hℓR f]
  rw [show (if d ∣ n then qCoeff (heckeT 2 ℓ ⇑f) (n / d) else 0)
    = if d ∣ n then coeffHeckeT 2 ℓ (qCoeff ⇑f) (n / d) else 0 from by
      split_ifs with h
      · exact qCoeff_heckeT f hΓR hℓ.ne_zero (n / d)
      · rfl]

  exact coeffHeckeT_dshift_comm hℓ.ne_zero hd0 hℓd (qCoeff ⇑f) n

end S_CuspForm_heckeTLin_rescaleLin
end P2MW
export P2MW.S_CuspForm_heckeTLin_rescaleLin (solution)
