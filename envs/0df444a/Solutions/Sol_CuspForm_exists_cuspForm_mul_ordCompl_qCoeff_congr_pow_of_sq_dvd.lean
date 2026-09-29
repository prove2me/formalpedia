-- Prove2me | solution 1 for CuspForm.exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f632ac03-c155-5d67-b17f-a7aed8b26108

import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open CuspForm ModularFormClass

private lemma sub_pow_mem {R : Type} [CommRing R] (I : Ideal R) {x y : R}
    (h : x - y ∈ I) (m : ℕ) : x ^ m - y ^ m ∈ I := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hid : x ^ (t + 1) - y ^ (t + 1) = x * (x ^ t - y ^ t) + (x - y) * y ^ t := by ring
      rw [hid]
      exact I.add_mem (I.mul_mem_left _ ih) (I.mul_mem_right _ h)

theorem solution (p : ℕ) [Fact p.Prime] {L : ℕ} [NeZero L] {v : ℕ} (hv : 2 ≤ v)
    (hvL : L.factorization p = v)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2)
    (hgint : ∀ n : ℕ, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g n) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 (p * (L / p ^ v))) (2 * (p : ℤ) ^ (v - 1)),
      (∀ n : ℕ, ∃ A : integralClosure ℤ ℂ, (A : ℂ) = ModularFormClass.qCoeff F n) ∧
      (∀ K : IntermediateField ℚ ℂ, (∀ n : ℕ, ModularFormClass.qCoeff g n ∈ K) →
        ∀ n : ℕ, ModularFormClass.qCoeff F n ∈ K) ∧
      (∀ (n : ℕ) (a A : integralClosure ℤ ℂ), (a : ℂ) = ModularFormClass.qCoeff g n →
        (A : ℂ) = ModularFormClass.qCoeff F n →
        A - a ^ p ^ (v - 1) ∈ Ideal.span {(p : integralClosure ℤ ℂ)}):= by
  have hp' : p.Prime := Fact.out
  have hL0 : L ≠ 0 := NeZero.ne L

  obtain ⟨m, hm⟩ : p ^ v ∣ L := hvL ▸ Nat.ordProj_dvd L p
  have hm0 : m ≠ 0 := by
    intro h
    exact hL0 (by rw [hm, h, mul_zero])
  have hlev : ∀ t : ℕ, t ≤ v → L / p ^ t = p ^ (v - t) * m := by
    intro t ht
    rw [hm, show p ^ v = p ^ t * p ^ (v - t) from by rw [← pow_add]; congr 1; omega,
      mul_assoc, Nat.mul_div_cancel_left _ (pow_pos hp'.pos t)]

  suffices h : ∀ t : ℕ, t ≤ v - 1 →
      ∃ F : CuspForm (CongruenceSubgroup.Gamma0 (L / p ^ t)) (2 * (p : ℤ) ^ t),
        (∀ n : ℕ, ∃ A : integralClosure ℤ ℂ, (A : ℂ) = ModularFormClass.qCoeff F n) ∧
        (∀ K : IntermediateField ℚ ℂ, (∀ n : ℕ, ModularFormClass.qCoeff g n ∈ K) →
          ∀ n : ℕ, ModularFormClass.qCoeff F n ∈ K) ∧
        (∀ (n : ℕ) (a A : integralClosure ℤ ℂ), (a : ℂ) = ModularFormClass.qCoeff g n →
          (A : ℂ) = ModularFormClass.qCoeff F n →
          A - a ^ p ^ t ∈ Ideal.span {(p : integralClosure ℤ ℂ)}) by
    obtain ⟨F, h1, h2, h3⟩ := h (v - 1) le_rfl
    have hfin : L / p ^ (v - 1) = p * (L / p ^ v) := by
      rw [hlev (v - 1) (by omega), hlev v le_rfl]
      rw [show v - (v - 1) = 1 from by omega, pow_one, Nat.sub_self, pow_zero, one_mul]
    rw [← hfin]
    exact ⟨F, h1, h2, h3⟩
  intro t
  induction t with
  | zero =>
      intro _
      rw [pow_zero, Nat.div_one, pow_zero, mul_one]
      refine ⟨g, hgint, fun K hK n => hK n, fun n a A ha hA => ?_⟩
      have hAa : A = a := Subtype.coe_injective (by
        show ((A : integralClosure ℤ ℂ) : ℂ) = ((a : integralClosure ℤ ℂ) : ℂ)
        rw [hA, ha])
      rw [hAa, pow_one, sub_self]
      exact Ideal.zero_mem _
  | succ t ih =>
      intro ht
      obtain ⟨F, h1, h2, h3⟩ := ih (by omega)

      haveI : NeZero (L / p ^ t) := ⟨by
        rw [hlev t (by omega)]
        exact Nat.mul_ne_zero (pow_ne_zero _ hp'.ne_zero) hm0⟩
      have hp2 : p ^ 2 ∣ L / p ^ t := by
        rw [hlev t (by omega)]
        exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) m
      obtain ⟨F', hFcoe, hFint, hFK, hFcong⟩ :=
        CuspForm.exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span p hp2 (2 * (p : ℤ) ^ t) F h1

      rw [show L / p ^ (t + 1) = (L / p ^ t) / p from by
          rw [Nat.div_div_eq_div_mul, ← pow_succ],
        show (2 * (p : ℤ) ^ (t + 1) : ℤ) = p * (2 * (p : ℤ) ^ t) from by ring]
      refine ⟨F', hFint, fun K hK => hFK K (h2 K hK), fun n a A ha hA => ?_⟩

      obtain ⟨b, hb⟩ := h1 n
      have hstep := hFcong n b A hb hA
      have hih := h3 n a b ha hb
      have hpow := sub_pow_mem _ hih p
      have hsplit : A - a ^ p ^ (t + 1) =
          (A - b ^ p) + (b ^ p - (a ^ p ^ t) ^ p) := by
        rw [← pow_mul, ← pow_succ]
        ring
      rw [hsplit]
      exact Ideal.add_mem _ hstep hpow

end S_CuspForm_exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd
end P2MW
export P2MW.S_CuspForm_exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd (solution)
