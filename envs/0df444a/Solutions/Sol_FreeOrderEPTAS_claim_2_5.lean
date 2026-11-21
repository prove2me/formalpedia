-- Prove2me | solution 1 for FreeOrderEPTAS.claim_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:21:52.381125+00:00
-- url     : https://prove2.me/submissions/da6e1013-7ee3-4540-947d-bc00eb336459

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace Aux_Types

open FreeOrderEPTAS

lemma typeOf_rho {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (j : Fin n) :
    typeOf I ϵ δ (rho I ϵ δ j) = typeVec I ϵ δ j := by
  unfold typeOf rho
  exact List.idxOf_get _

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by unfold bit; split_ifs <;> norm_num

lemma bit_le_one (b : Bool) : bit b ≤ 1 := by unfold bit; split_ifs <;> norm_num

/-- Loads of a common positive segment `s' + 1` lie in `(δ(1+ϵ)^s', δ(1+ϵ)^(s'+1)]`. -/
lemma seg_bounds {ϵ δ v : ℝ} (hϵ : 0 < ϵ) (hδ : 0 < δ) (s' : ℕ) (h : seg ϵ δ v = s' + 1) :
    δ * (1 + ϵ) ^ s' < v ∧ v ≤ δ * (1 + ϵ) ^ (s' + 1) := by
  unfold seg at h
  by_cases hv0 : v ≤ δ
  · rw [if_pos hv0] at h; omega
  rw [if_neg hv0] at h
  have hv : δ < v := lt_of_not_ge hv0
  have hl : 0 < Real.log (1 + ϵ) := Real.log_pos (by linarith)
  have hvδ : 0 < v / δ := div_pos (by linarith) hδ
  have hup : Real.log (v / δ) / Real.log (1 + ϵ) ≤ ((s' + 1 : ℕ) : ℝ) := by
    rw [← h]; exact Nat.le_ceil _
  have hlo : ((s' : ℕ) : ℝ) < Real.log (v / δ) / Real.log (1 + ϵ) := by
    have : s' < ⌈Real.log (v / δ) / Real.log (1 + ϵ)⌉₊ := by rw [h]; omega
    exact Nat.lt_ceil.1 this
  rw [div_le_iff₀ hl] at hup
  rw [lt_div_iff₀ hl] at hlo
  have hp1 : 0 < (1 + ϵ) ^ (s' + 1) := by positivity
  have hp0 : 0 < (1 + ϵ) ^ s' := by positivity
  have e1 : ((s' + 1 : ℕ) : ℝ) * Real.log (1 + ϵ) = Real.log ((1 + ϵ) ^ (s' + 1)) := by
    rw [Real.log_pow]
  have e0 : ((s' : ℕ) : ℝ) * Real.log (1 + ϵ) = Real.log ((1 + ϵ) ^ s') := by
    rw [Real.log_pow]
  rw [e1] at hup
  rw [e0] at hlo
  have h1 : v / δ ≤ (1 + ϵ) ^ (s' + 1) := (Real.log_le_log_iff hvδ hp1).1 hup
  have h0 : (1 + ϵ) ^ s' < v / δ := (Real.log_lt_log_iff hp0 hvδ).1 hlo
  constructor
  · rw [lt_div_iff₀ hδ] at h0; linarith
  · rw [div_le_iff₀ hδ] at h1; linarith

lemma Nip_eq {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (x : Assignment m n) (i : Fin m)
    (t : Fin (numTypes I ϵ δ)) :
    (Nip I ϵ δ x i t : ℝ) = ∑ j with rho I ϵ δ j = t, bit (x i j) := by
  unfold Nip bit
  rw [Finset.sum_boole, Finset.filter_filter]

lemma Sip_nonneg {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (x : Assignment m n) (i : Fin m)
    (d : Fin D) (t : Fin (numTypes I ϵ δ)) : 0 ≤ Sip I ϵ δ x i d t := by
  unfold Sip
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (I.ℓ_mem i j d).1 (bit_nonneg _))

/-- Large types keep their load (Claim 2.5). -/
theorem large_type {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (x : Assignment m n)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo)
    (Y : Assignment m n)
    (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)) (hd : d ∈ I.A i)
    (hlarge : 1 ≤ typeOf I ϵ δ t i d)
    (hcnt : (Nlo i t : ℝ) ≤ ∑ j with rho I ϵ δ j = t, bit (Y i j) ∧
      ∑ j with rho I ϵ δ j = t, bit (Y i j) ≤ (Nhi i t : ℝ)) :
    (1 - ϵ) * min (Sip I ϵ δ x i d t) 1 ≤
      ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j) := by
  obtain ⟨s', hs'⟩ : ∃ s', typeOf I ϵ δ t i d = s' + 1 := ⟨typeOf I ϵ δ t i d - 1, by omega⟩
  have hseg : ∀ j, rho I ϵ δ j = t → seg ϵ δ (I.ℓ i j d) = s' + 1 := by
    intro j hj
    rw [← hs', ← hj, typeOf_rho]
    unfold typeVec; rw [if_pos hd]
  obtain ⟨W, hW⟩ : ∃ W, W = δ * (1 + ϵ) ^ s' := ⟨_, rfl⟩
  have hU : δ * (1 + ϵ) ^ (s' + 1) = (1 + ϵ) * W := by rw [hW, pow_succ]; ring
  have hWδ : δ ≤ W := by
    rw [hW]
    have : (1 : ℝ) ≤ (1 + ϵ) ^ s' := one_le_pow₀ (by linarith)
    nlinarith
  have hW0 : 0 ≤ W := by linarith
  have hlbY : W * ∑ j with rho I ϵ δ j = t, bit (Y i j) ≤
      ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : rho I ϵ δ j = t := (Finset.mem_filter.1 hj).2
    have := (seg_bounds hϵ0 hδ0 s' (hseg j hj')).1
    rw [← hW] at this
    exact mul_le_mul_of_nonneg_right this.le (bit_nonneg _)
  have hubx : Sip I ϵ δ x i d t ≤ (1 + ϵ) * W * Nip I ϵ δ x i t := by
    rw [Nip_eq, Finset.mul_sum]
    unfold Sip
    apply Finset.sum_le_sum
    intro j hj
    have hj' : rho I ϵ δ j = t := (Finset.mem_filter.1 hj).2
    have := (seg_bounds hϵ0 hδ0 s' (hseg j hj')).2
    rw [hU] at this
    exact mul_le_mul_of_nonneg_right this (bit_nonneg _)
  have hS0 := Sip_nonneg I ϵ δ x i d t
  have hmin0 : 0 ≤ min (Sip I ϵ δ x i d t) 1 := le_min hS0 zero_le_one
  have hminS : min (Sip I ϵ δ x i d t) 1 ≤ Sip I ϵ δ x i d t := min_le_left _ _
  have hmin1 : min (Sip I ϵ δ x i d t) 1 ≤ 1 := min_le_right _ _
  by_cases hsm : (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ
  · obtain ⟨hlo, hhi⟩ := hg.exact i t hsm
    have hcount : ∑ j with rho I ϵ δ j = t, bit (Y i j) = (Nip I ϵ δ x i t : ℝ) := by
      have h1 := hcnt.1; have h2 := hcnt.2
      rw [hlo] at h1; rw [hhi] at h2
      linarith
    rw [hcount] at hlbY
    have hN0 : (0 : ℝ) ≤ Nip I ϵ δ x i t := Nat.cast_nonneg _
    have hWN : 0 ≤ W * (Nip I ϵ δ x i t : ℝ) := mul_nonneg hW0 hN0
    have h1 : (1 - ϵ) * min (Sip I ϵ δ x i d t) 1 ≤ (1 - ϵ) * Sip I ϵ δ x i d t :=
      mul_le_mul_of_nonneg_left hminS (by linarith)
    have h2 : (1 - ϵ) * Sip I ϵ δ x i d t ≤ (1 - ϵ) * ((1 + ϵ) * W * Nip I ϵ δ x i t) :=
      mul_le_mul_of_nonneg_left hubx (by linarith)
    have h3 : (1 - ϵ) * ((1 + ϵ) * W * Nip I ϵ δ x i t) ≤ W * Nip I ϵ δ x i t := by
      have : (1 - ϵ) * ((1 + ϵ) * W * Nip I ϵ δ x i t) = (1 - ϵ ^ 2) * (W * Nip I ϵ δ x i t) := by
        ring
      rw [this]
      nlinarith [sq_nonneg ϵ]
    linarith
  · push_neg at hsm
    obtain ⟨hlo, _, _⟩ := hg.approx i t hsm
    have h1 := hcnt.1
    rw [hlo] at h1
    have hcnt0 : 0 ≤ ∑ j with rho I ϵ δ j = t, bit (Y i j) :=
      Finset.sum_nonneg (fun j _ => bit_nonneg _)
    have h2 : (1 : ℝ) ≤ W * ∑ j with rho I ϵ δ j = t, bit (Y i j) := by
      have h3 : δ * (1 / δ) ≤ W * ∑ j with rho I ϵ δ j = t, bit (Y i j) :=
        mul_le_mul hWδ h1 (div_nonneg zero_le_one hδ0.le) hW0
      rw [mul_one_div_cancel hδ0.ne'] at h3
      exact h3
    have h4 : (1 - ϵ) * min (Sip I ϵ δ x i d t) 1 ≤ 1 := by nlinarith
    linarith

end Aux_Types

open FreeOrderEPTAS in
theorem solution {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (x : Assignment m n)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ ξ Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ ξ Nlo Nhi Slo).MeetsS123 y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd)
    (Y : Assignment m n) (hY : Y ∈ (rnd (mkLP I ϵ δ ξ Nlo Nhi Slo) y).support)
    (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)) (hd : d ∈ I.A i)
    (hlarge : 1 ≤ typeOf I ϵ δ t i d) :
    (1 - ϵ) * min (Sip I ϵ δ x i d t) 1 ≤
      ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j) := by
  have h := ((hrnd _ y hy).degree Y hY).2 i t
  exact Aux_Types.large_type I ϵ δ ξ hϵ0 hϵ1 hδ0 x Nlo Nhi Slo hg Y i d t hd hlarge ⟨h.1, h.2⟩
