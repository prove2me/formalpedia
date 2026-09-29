-- Prove2me | solution 1 for CuspForm.isNormalizedEigenform_iff_coeffHecke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/70f4ccd7-863f-5a57-8d6c-e6e9b82333cf

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_qCoeff_zero
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isNormalizedEigenform_iff_coeffHecke

set_option autoImplicit false

namespace M4cP2
namespace W25c

open ModularForm

section Arithmetic

variable (a : ℕ → ℂ)

theorem zpow_two_sub_one (p : ℕ) : (p : ℂ) ^ ((2 : ℤ) - 1) = p := by norm_num

theorem coeffHeckeT_two (p n : ℕ) :
    coeffHeckeT 2 p a n = a (n * p) + if p ∣ n then (p : ℂ) * a (n / p) else 0 := by
  rw [coeffHeckeT_apply, zpow_two_sub_one]

theorem coprime_pow_of_not_dvd {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (k : ℕ) :
    (p ^ k).Coprime m :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)

theorem heckeT_eigen_of_rec {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r)) (n : ℕ) :
    coeffHeckeT 2 p a n = a p * a n := by
  rw [coeffHeckeT_two]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  cases r with
  | zero =>
    have hpm : ¬ p ∣ p ^ 0 * m := by simpa using hm
    rw [if_neg hpm, add_zero, pow_zero, one_mul, hmul m p
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)), mul_comm]
  | succ s =>
    have hpn : p ∣ p ^ (s + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
    have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
      rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [if_pos hpn, hdiv, show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 2)), hmul _ _ (coprime_pow_of_not_dvd hp hm s),
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 1)), hrec s]
    ring

theorem heckeU_eigen_of_rec {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1))) (n : ℕ) :
    coeffHeckeU p a n = a p * a n := by
  rw [coeffHeckeU_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hstep : a (p ^ (r + 1)) = a p * a (p ^ r) := by
    cases r with
    | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
    | succ s => exact hrec s
  rw [show p ^ r * m * p = p ^ (r + 1) * m by ring, hmul _ _ (coprime_pow_of_not_dvd hp hm (r + 1)),
    hmul _ _ (coprime_pow_of_not_dvd hp hm r), hstep]
  ring

theorem rec_of_heckeT_eigen {p : ℕ} (hp : p.Prime)
    (hT : ∀ n : ℕ, coeffHeckeT 2 p a n = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r) := by
  have h := hT (p ^ (r + 1))
  have hpn : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
  have hdiv : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ', Nat.mul_div_cancel_left _ hp.pos]
  rw [coeffHeckeT_two, if_pos hpn, hdiv, ← pow_succ] at h
  linear_combination h

theorem rec_of_heckeU_eigen {p : ℕ} (hU : ∀ n : ℕ, coeffHeckeU p a n = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) := by
  have h := hU (p ^ (r + 1))
  rwa [coeffHeckeU_apply, ← pow_succ] at h

theorem pow_mul_of_heckeT_eigen {p : ℕ} (hp : p.Prime) (h1 : a 1 = 1)
    (hT : ∀ n : ℕ, coeffHeckeT 2 p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro m hm
    match r, ih with
    | 0, _ => rw [pow_zero, one_mul, h1, one_mul]
    | 1, _ =>
      have h := hT m
      rw [coeffHeckeT_two, if_neg hm, add_zero] at h
      rw [pow_one, mul_comm p m, h]
    | s + 2, ih =>
      have h := hT (p ^ (s + 1) * m)
      have hpn : p ∣ p ^ (s + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
      have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
        rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
      rw [coeffHeckeT_two, if_pos hpn, hdiv, show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
        ih (s + 1) (by omega) m hm, ih s (by omega) m hm] at h
      rw [rec_of_heckeT_eigen a hp hT s]
      linear_combination h

theorem pow_mul_of_heckeU_eigen {p : ℕ} (h1 : a 1 = 1)
    (hU : ∀ n : ℕ, coeffHeckeU p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r with
  | zero => intro m _; rw [pow_zero, one_mul, h1, one_mul]
  | succ s ih =>
    intro m hm
    have h := hU (p ^ s * m)
    rw [coeffHeckeU_apply, show p ^ s * m * p = p ^ (s + 1) * m by ring, ih m hm] at h
    have hstep : a (p ^ (s + 1)) = a p * a (p ^ s) := by
      cases s with
      | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
      | succ t => exact rec_of_heckeU_eigen a hU t
    rw [h, hstep]
    ring

theorem mul_of_coprime_of_pow_mul (h1 : a 1 = 1)
    (hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [Nat.coprime_zero_left] at hmn
        subst hmn
        rw [mul_one, h1, mul_one]
      · rw [one_mul, h1, one_mul]
    · have hm0 : m ≠ 0 := by omega
      have hm1 : m ≠ 1 := by omega
      set p := m.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      obtain ⟨r, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
      have hr : r ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hmeq
        exact hm' (hmeq ▸ hpm)
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero (fun h0 => hm0 (by rw [hmeq, h0, mul_zero]))
      have hm'lt : m' < m := by
        have hpr : 2 ≤ p ^ r := by
          calc 2 ≤ p := hp.two_le
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hr)
        calc m' = 1 * m' := (one_mul _).symm
          _ < p ^ r * m' := Nat.mul_lt_mul_of_pos_right (by omega) hm'pos
          _ = m := hmeq.symm
      have hpn : ¬ p ∣ n := fun hdvd =>
        hp.ne_one (Nat.eq_one_of_dvd_coprimes hmn hpm hdvd)
      have hm'n : m'.Coprime n :=
        Nat.Coprime.coprime_dvd_left (⟨p ^ r, by rw [hmeq]; ring⟩ : m' ∣ m) hmn
      have hpm'n : ¬ p ∣ m' * n := fun hdvd =>
        (hp.dvd_mul.mp hdvd).elim hm' hpn
      rw [hmeq, show p ^ r * m' * n = p ^ r * (m' * n) by ring, hpow p hp r (m' * n) hpm'n,
        ih m' hm'lt n hm'n, hpow p hp r m' hm']
      ring

end Arithmetic

open ModularFormClass

theorem isNormalizedEigenform_iff_coeffHecke {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔
      (qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
        ((¬ p ∣ N → ∀ n : ℕ, coeffHeckeT 2 p (qCoeff f) n = qCoeff f p * qCoeff f n) ∧
          (p ∣ N → ∀ n : ℕ, coeffHeckeU p (qCoeff f) n = qCoeff f p * qCoeff f n))) := by
  have h0 : qCoeff f 0 = 0 := CuspForm.qCoeff_zero f
  constructor
  · intro hf
    refine ⟨hf.qCoeff_one, fun p hp => ⟨fun hpN n => ?_, fun hpN n => ?_⟩⟩
    · exact heckeT_eigen_of_rec (qCoeff f) hp h0 hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_not_dvd p r hp hpN) n
    · exact heckeU_eigen_of_rec (qCoeff f) hp h0 hf.qCoeff_one hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_dvd p r hp hpN) n
  · rintro ⟨h1, hE⟩
    have hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m →
        qCoeff f (p ^ r * m) = qCoeff f (p ^ r) * qCoeff f m := by
      intro p hp
      by_cases hpN : p ∣ N
      · exact pow_mul_of_heckeU_eigen (qCoeff f) h1 ((hE p hp).2 hpN)
      · exact pow_mul_of_heckeT_eigen (qCoeff f) hp h1 ((hE p hp).1 hpN)
    exact
      { qCoeff_one := h1
        qCoeff_mul_of_coprime := mul_of_coprime_of_pow_mul (qCoeff f) h1 hpow
        qCoeff_prime_pow_of_not_dvd := fun p r hp hpN =>
          rec_of_heckeT_eigen (qCoeff f) hp ((hE p hp).1 hpN) r
        qCoeff_prime_pow_of_dvd := fun p r hp hpN =>
          rec_of_heckeU_eigen (qCoeff f) ((hE p hp).2 hpN) r }

end M4cP2.W25c

theorem solution {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime → ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧ (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n))) :=
  M4cP2.W25c.isNormalizedEigenform_iff_coeffHecke f

end S_CuspForm_isNormalizedEigenform_iff_coeffHecke
end P2MW
export P2MW.S_CuspForm_isNormalizedEigenform_iff_coeffHecke (solution)
