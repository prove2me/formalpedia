-- Prove2me | solution 1 for CuspForm.qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f9ce0690-54cb-55c2-9d4c-1e71619878cd

import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero

set_option autoImplicit false
open CongruenceSubgroup ModularFormClass

namespace AlliAux2AZERO

open UpperHalfPlane ModularForm

private lemma qCoeff_rec_of_heckeTLin_eq_smul {M ℓ : ℕ} [NeZero M] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {v : CuspForm (Gamma0 M) 2} {c : ℂ} (hc : CuspForm.heckeTLin 2 hℓ hℓM v = c • v) (m : ℕ) :
    qCoeff v (m * ℓ) + (if ℓ ∣ m then (ℓ : ℂ) * qCoeff v (m / ℓ) else 0) = c * qCoeff v m := by
  have hΓM : (1 : ℝ) ∈ Subgroup.strictPeriods (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by simp

  have hfun : heckeT 2 ℓ ⇑v = (c • ⇑v : UpperHalfPlane → ℂ) := by
    have := congrArg (DFunLike.coe (F := CuspForm (Gamma0 M) 2)) hc
    rwa [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul] at this

  have hLHS : qCoeff (heckeT 2 ℓ ⇑v) m = coeffHeckeT 2 ℓ (fun n => qCoeff ⇑v n) m :=
    ModularFormClass.qCoeff_heckeT v hΓM hℓ.pos.ne' m
  have hRHS : qCoeff (c • ⇑v : UpperHalfPlane → ℂ) m = c * qCoeff ⇑v m := by
    unfold ModularFormClass.qCoeff
    rw [show (c • ⇑v : UpperHalfPlane → ℂ) = c • (v : UpperHalfPlane → ℂ) from rfl,
      ModularForm.qExpansion_smul one_pos hΓM c v, PowerSeries.coeff_smul, smul_eq_mul]
  rw [hfun, hRHS] at hLHS
  rw [coeffHeckeT_apply] at hLHS

  have hpow : (ℓ : ℂ) ^ ((2 : ℤ) - 1) = (ℓ : ℂ) := by norm_num
  rw [hpow] at hLHS

  exact hLHS.symm

end AlliAux2AZERO

open AlliAux2AZERO CongruenceSubgroup ModularFormClass in
theorem solution
    {M : ℕ} [NeZero M] {v : CuspForm (Gamma0 M) 2}
    (hv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
      CuspForm.heckeTLin 2 hℓ hℓM v = c • v)
    (h1 : qCoeff v 1 = 0)
    {n : ℕ} (hn : Nat.Coprime n M) :
    qCoeff v n = 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 =>
    exact CuspFormClass.qExpansion_coeff_zero v one_pos (by simp)
  | 1 => exact h1
  | n + 2 =>

    obtain ⟨ℓ, hℓ, hℓn⟩ := (n + 2).exists_prime_and_dvd (by omega)
    have hℓM : ¬ ℓ ∣ M := hℓ.coprime_iff_not_dvd.mp (hn.coprime_dvd_left hℓn)
    obtain ⟨c, hc⟩ := hv ℓ hℓ hℓM
    obtain ⟨m, hm⟩ := hℓn
    have hm' : n + 2 = m * ℓ := hm.trans (mul_comm ℓ m)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp only [mul_zero] at hm; omega
      · exact h
    have hm_lt : m < n + 2 :=
      calc m = 1 * m := (one_mul m).symm
        _ < ℓ * m := (Nat.mul_lt_mul_right hm0).mpr hℓ.one_lt
        _ = n + 2 := hm.symm
    have hmM : Nat.Coprime m M := hn.coprime_dvd_left ⟨ℓ, hm'⟩

    have hrec := qCoeff_rec_of_heckeTLin_eq_smul hℓ hℓM hc m
    rw [← hm', ih m hm_lt hmM, mul_zero] at hrec
    have hif0 : (if ℓ ∣ m then (ℓ : ℂ) * qCoeff v (m / ℓ) else 0) = 0 := by
      split_ifs with hℓm
      · have hml_lt : m / ℓ < n + 2 := lt_of_le_of_lt (Nat.div_le_self m ℓ) hm_lt
        have hmlM : Nat.Coprime (m / ℓ) M :=
          hn.coprime_dvd_left ((Nat.div_dvd_of_dvd hℓm).trans ⟨ℓ, hm'⟩)
        rw [ih (m / ℓ) hml_lt hmlM, mul_zero]
      · rfl
    rw [hif0, add_zero] at hrec
    exact hrec

end S_CuspForm_qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero
end P2MW
export P2MW.S_CuspForm_qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero (solution)
