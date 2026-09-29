-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.qCoeff_eq_of_coprime_of_forall_prime_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e23e50ac-4741-5eb6-b83a-019f51f9b364

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd

open ModularFormClass

namespace AlliAux1

theorem qCoeff_prime_pow_eq {M R R' : ℕ}
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNormalizedEigenform g) (hg' : CuspForm.IsNormalizedEigenform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → qCoeff g ℓ = qCoeff g' ℓ)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (j : ℕ) :
    qCoeff g (p ^ j) = qCoeff g' (p ^ j) ∧ qCoeff g (p ^ (j + 1)) = qCoeff g' (p ^ (j + 1)) := by
  have hpR : ¬ p ∣ R := fun hd => hpM (hd.trans hR)
  have hpR' : ¬ p ∣ R' := fun hd => hpM (hd.trans hR')
  induction j with
  | zero =>
    exact ⟨by rw [pow_zero, hg.qCoeff_one, hg'.qCoeff_one], by rw [zero_add, pow_one]; exact h p hp hpM⟩
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    rw [show j + 1 + 1 = j + 2 from rfl,
      hg.qCoeff_prime_pow_of_not_dvd p j hp hpR, hg'.qCoeff_prime_pow_of_not_dvd p j hp hpR',
      ih.1, ih.2, h p hp hpM]

theorem qCoeff_zero_eq_zero {S : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 S) 2) :
    qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (by simp)

end AlliAux1

open AlliAux1 in
theorem solution
    {M R R' : ℕ}
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNormalizedEigenform g) (hg' : CuspForm.IsNormalizedEigenform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ)
    {n : ℕ} (hn : Nat.Coprime n M) :
    ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => rw [qCoeff_zero_eq_zero, qCoeff_zero_eq_zero]
  | one => rw [hg.qCoeff_one, hg'.qCoeff_one]
  | prime_pow p k hp hk =>
    have hpM : ¬ p ∣ M :=
      (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk.ne') hn)
    exact (qCoeff_prime_pow_eq hg hg' hR hR' h hp hpM k).1
  | coprime a b ha hb hab iha ihb =>
    rw [hg.qCoeff_mul_of_coprime a b hab, hg'.qCoeff_mul_of_coprime a b hab,
      iha hn.coprime_mul_right, ihb hn.coprime_mul_left]

end S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd (solution)
