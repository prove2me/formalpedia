-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:32.107505+00:00
-- url     : https://prove2.me/submissions/f66473b3-3f6f-422b-b51f-b52632d73c3a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b)
    (v : ι × Fin n × Fin n) :
    TGood (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) ((b : ℕ) - a) (v.2.1 : ℕ)
      (Polynomial.C (X v) + (if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0)) := by
  classical
  intro j m h
  rw [Polynomial.coeff_add, coeff_add] at h
  by_cases hj : j = 0
  · subst hj
    have h0 : coeff m ((if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0 : Polynomial (MvPolynomial (ι × Fin n × Fin n) ℂ)).coeff 0) = 0 := by
      split_ifs <;> simp
    rw [h0, add_zero, Polynomial.coeff_C_zero, coeff_X] at h
    by_cases hm : Finsupp.single v 1 = m
    · subst hm; simp [Finsupp.weight_single]
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [Polynomial.coeff_C, if_neg hj, coeff_zero, zero_add] at h
    by_cases hc : v.1 = τ ∧ v.2.1 = b
    · rw [if_pos hc, Polynomial.X_mul_C, Polynomial.coeff_C_mul_X] at h
      by_cases hj1 : j = 1
      · subst hj1
        rw [if_pos rfl, coeff_X] at h
        by_cases hm : Finsupp.single (τ, a, v.2.2) 1 = m
        · subst hm
          rw [Finsupp.weight_single, smul_eq_mul, one_mul, one_mul]
          have hb : (v.2.1 : ℕ) = b := congrArg Fin.val hc.2
          have hab' : (a : ℕ) < b := hab
          dsimp only
          omega
        · rw [if_neg hm] at h; exact absurd rfl h
      · rw [if_neg hj1, coeff_zero] at h; exact absurd rfl h
    · rw [if_neg hc, Polynomial.coeff_zero, coeff_zero] at h; exact absurd rfl h
end Formalism.L2.SG.Pf.ColDictValCPf
