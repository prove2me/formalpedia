-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.isEigenformWith_one_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ea365bbc-43a5-592a-b858-49cfd1827896

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_CuspForm_qCoeff_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

namespace Ws41
namespace B4

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

theorem isUnit_entry_one_one_of_mem_Gamma0' {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    IsUnit (((γ 1 1 : ℤ) : ZMod M)) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := by
    have := Gamma0_mem.mp hγ
    exact_mod_cast this
  have h : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  exact IsUnit.of_mul_eq_one_right _ h

theorem hasNebentypus_one_of_coe_eq' {M : ℕ} {k : ℤ} (g : CuspForm (Gamma0 M) k)
    (g₁ : CuspForm (Gamma1 M) k) (hg₁ : (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g) :
    CuspForm.HasNebentypus (1 : DirichletCharacter ℂ M) g₁ := by
  intro γ hγ τ
  rw [MulChar.one_apply (isUnit_entry_one_one_of_mem_Gamma0' hγ), one_mul]
  have h1 := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  rw [show g₁ (γ • τ) = g (γ • τ) from congrFun hg₁ _, show g₁ τ = g τ from congrFun hg₁ _, h1]
  congr 1

variable {N : ℕ} {g : CuspForm (Gamma0 N) 2}

theorem qCoeff_pow_succ_of_dvd (hg : g.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    ∀ r : ℕ, qCoeff g (ℓ ^ (r + 1)) = qCoeff g ℓ * qCoeff g (ℓ ^ r)
  | 0 => by rw [zero_add, pow_one, pow_zero, hg.qCoeff_one, mul_one]
  | (r + 1) => by
    rw [show r + 1 + 1 = r + 2 from rfl, hg.qCoeff_prime_pow_of_dvd ℓ r hℓ hℓN]

theorem qCoeff_zero' : qCoeff g 0 = 0 := CuspForm.qCoeff_zero g

end Ws41.B4

open Ws41.B4 ModularFormClass in
theorem solution
    {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    (g₁ : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hg₁ : (⇑g₁ : UpperHalfPlane → ℂ) = ⇑g) :
    CuspForm.IsEigenformWith (1 : DirichletCharacter ℂ N) g₁ := by
  have hq : ∀ n, qCoeff g₁ n = qCoeff g n := fun n => by rw [hg₁]
  refine ⟨by rw [hq, hg.qCoeff_one], ?_, ?_, hasNebentypus_one_of_coe_eq' g g₁ hg₁⟩
  ·
    intro p hp hpN n
    simp only [hq]
    have hunit : IsUnit ((p : ZMod N)) := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hpN
    rw [MulChar.one_apply hunit, one_mul, show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [qCoeff_zero']
    obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
    have hpm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
    have hcop : ∀ s : ℕ, Nat.Coprime (p ^ s) m := fun s => Nat.Coprime.pow_left s hpm
    cases r with
    | zero =>
      rw [pow_zero, one_mul, if_neg hm, mul_zero, add_zero]
      exact hg.qCoeff_mul_of_coprime p m hpm
    | succ r =>
      have hdvd : p ∣ p ^ (r + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero r)) m
      rw [if_pos hdvd, show p ^ (r + 1) * m / p = p ^ r * m by
            rw [pow_succ, mul_comm (p ^ r) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos],
        show p * (p ^ (r + 1) * m) = p ^ (r + 2) * m by ring,
        hg.qCoeff_mul_of_coprime _ _ (hcop (r + 2)), hg.qCoeff_mul_of_coprime _ _ (hcop (r + 1)),
        hg.qCoeff_mul_of_coprime _ _ (hcop r), hg.qCoeff_prime_pow_of_not_dvd p r hp hpN]
      ring
  ·
    intro ℓ hℓ hℓN n
    simp only [hq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [qCoeff_zero']
    obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' ℓ hℓ.one_lt.ne'
    have hcop : Nat.Coprime (ℓ ^ r) m := (Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm))
    have hcop1 : Nat.Coprime (ℓ ^ (r + 1)) m := (Nat.Coprime.pow_left (r+1) ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm))
    rw [show ℓ * (ℓ ^ r * m) = ℓ ^ (r + 1) * m by ring, hg.qCoeff_mul_of_coprime _ _ hcop1,
      hg.qCoeff_mul_of_coprime _ _ hcop, qCoeff_pow_succ_of_dvd hg hℓ hℓN r]
    ring

end S_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq (solution)
