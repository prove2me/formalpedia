-- Prove2me | solution 1 for BundledPay.Base.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:58:03.855225+00:00
-- url     : https://prove2.me/submissions/be3cb358-298a-4b45-90db-181cb7c05960

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace Aux_BundledW31
open BundledPay.Base

lemma best (v : ℝ → ℝ) (K wb k J : ℝ) (hwb : 0 < wb) (hk : 0 < k) (hJ : 0 < J)
    (hv : ∀ y, v y = K - wb * (k * y - J) ^ 2) (c : Prop) [Decidable c] (hc : c ↔ J ≤ k)
    (ip : ℝ) :
    (ip ∈ Set.Icc (0:ℝ) 1 ∧ ∀ y ∈ Set.Icc (0:ℝ) 1, v y ≤ v ip) ↔
      ip = if c then J / k else 1 := by
  have e : k * (J / k) = J := by field_simp
  by_cases hc' : c
  · rw [if_pos hc']
    have h := hc.1 hc'
    constructor
    · rintro ⟨hip, hmax⟩
      have := hmax (J / k) ⟨div_nonneg hJ.le hk.le, (div_le_one hk).2 h⟩
      rw [hv, hv, e] at this
      have h2 : (k * ip - J) ^ 2 ≤ 0 := by nlinarith
      have h3 : k * ip - J = 0 := by nlinarith [sq_nonneg (k * ip - J)]
      field_simp
      linarith
    · intro hip
      subst hip
      refine ⟨⟨div_nonneg hJ.le hk.le, (div_le_one hk).2 h⟩, fun y hy => ?_⟩
      rw [hv, hv, e]
      nlinarith [sq_nonneg (k * y - J)]
  · rw [if_neg hc']
    have h : k < J := by
      by_contra h'; push_neg at h'; exact hc' (hc.2 h')
    constructor
    · rintro ⟨hip, hmax⟩
      have := hmax 1 ⟨zero_le_one, le_rfl⟩
      rw [hv, hv] at this
      have h2 : wb * (k * ip - J) ^ 2 ≤ wb * (k * 1 - J) ^ 2 := by linarith
      have h2' := le_of_mul_le_mul_left h2 hwb
      apply le_antisymm hip.2
      have hki : k * ip ≤ k := by nlinarith [hip.2]
      have h3 : 0 < 2 * J - k * ip - k := by linarith
      by_contra hlt
      push_neg at hlt
      have := mul_pos (mul_pos hk (sub_pos.2 hlt)) h3
      nlinarith
    · intro hip
      subst hip
      refine ⟨⟨zero_le_one, le_rfl⟩, fun y hy => ?_⟩
      rw [hv, hv]
      have hky : k * y ≤ k := by nlinarith [hy.2]
      have hX : 0 ≤ (k - k * y) * (2 * J - k - k * y) :=
        mul_nonneg (by linarith) (by nlinarith [hy.1])
      have : (k * 1 - J) ^ 2 ≤ (k * y - J) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hwb.le]

lemma hdrp (P : Params) (hS : P.Standing) :
    P.r1p - P.r2p = 2 * P.wb * (P.drp / (2 * P.wb)) := by
  obtain ⟨_, _, hwb, _⟩ := hS
  unfold Params.drp; field_simp

lemma hJ (P : Params) (hS : P.Standing) : 0 < P.I0 + P.drp / (2 * P.wb) := by
  obtain ⟨_, h2, hwb, hI0, _⟩ := hS
  have : 0 < P.drp := by unfold Params.drp; linarith
  have := div_pos this (by linarith : (0:ℝ) < 2 * P.wb)
  linarith

lemma hc (P : Params) :
    P.psi ≤ psiBar P ↔ P.I0 + P.drp / (2 * P.wb) ≤ 1 - P.psi := by
  unfold psiBar; constructor <;> intro h <;> linarith

end Aux_BundledW31

open BundledPay.Base Aux_BundledW31 in
theorem solution (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (ih ip : ℝ) :
    IsNashFFS P ih ip ↔
      (ih = 1 ∧ ip = (if P.psi ≤ psiBar P then
        (P.I0 + P.drp / (2 * P.wb)) / (1 - P.psi) else 1)) := by
  have hS' := hS
  obtain ⟨hc12, hr12, hwb, hI0, hI1, hpsi0, hpsi1⟩ := hS'
  have hD : 0 < P.c1 - P.c2 := by linarith
  have hk : 0 < 1 - P.psi := by linarith
  have hv : ∀ y, physFFS P 1 y = (P.r2p + (P.r1p - P.r2p) * (P.I0 + P.drp / (2 * P.wb))
      - P.wb * (P.drp / (2 * P.wb)) ^ 2)
      - P.wb * ((1 - P.psi) * y - (P.I0 + P.drp / (2 * P.wb))) ^ 2 := by
    intro y
    simp only [physFFS, intensity]
    linear_combination ((1 - P.psi) * y - P.I0 - P.drp / (2 * P.wb)) * hdrp P hS
  have hB := best (physFFS P 1) _ P.wb (1 - P.psi) _ hwb hk (hJ P hS) hv _ (hc P) ip
  unfold IsNashFFS IsNash
  constructor
  · rintro ⟨hih, hip, hu, hvv⟩
    have h1 : ih = 1 := by
      have := hu 1 ⟨zero_le_one, le_rfl⟩
      simp only [hospFFS, intensity, hwq] at this
      apply le_antisymm hih.2
      by_contra hlt; push_neg at hlt
      have := mul_pos (mul_pos hD hpsi0) (sub_pos.2 hlt)
      nlinarith
    subst h1
    exact ⟨rfl, hB.1 ⟨hip, hvv⟩⟩
  · rintro ⟨rfl, h⟩
    obtain ⟨hip, hvv⟩ := hB.2 h
    refine ⟨⟨zero_le_one, le_rfl⟩, hip, fun x hx => ?_, hvv⟩
    simp only [hospFFS, intensity, hwq]
    nlinarith [mul_nonneg (mul_pos hD hpsi0).le (sub_nonneg.2 hx.2)]
