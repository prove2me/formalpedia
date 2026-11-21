-- Prove2me | solution 1 for FreeOrderEPTAS.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:41:32.366363+00:00
-- url     : https://prove2.me/submissions/aab9314f-1ead-410c-8822-5b9896fd2863

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

namespace Aux_Small

open FreeOrderEPTAS

lemma pr_eq_sum {α : Type} [Fintype α] (p : PMF α) (S : Set α) :
    pr p S = ∑ a, S.indicator (fun a => (p a).toReal) a := by
  unfold pr
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]; simp
  · intro a _
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha]; exact PMF.apply_ne_top _ a
    · rw [Set.indicator_of_notMem ha]; exact ENNReal.zero_ne_top

lemma sum_toReal {α : Type} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  have : ∑ a, p a = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]; exact PMF.tsum_coe p
  rw [this]; simp

lemma pr_toReal_nonneg {α : Type} [Fintype α] (p : PMF α) (a : α) : 0 ≤ (p a).toReal :=
  ENNReal.toReal_nonneg

lemma pr_add_compl {α : Type} [Fintype α] (p : PMF α) (S : Set α) :
    pr p S + pr p Sᶜ = 1 := by
  rw [pr_eq_sum, pr_eq_sum, ← Finset.sum_add_distrib]
  simp only [Set.indicator_self_add_compl_apply]
  exact sum_toReal p

lemma pr_mono {α : Type} [Fintype α] (p : PMF α) {S T : Set α} (h : S ⊆ T) :
    pr p S ≤ pr p T := by
  rw [pr_eq_sum, pr_eq_sum]
  apply Finset.sum_le_sum
  intro a _
  exact Set.indicator_le_indicator_of_subset h (fun a => pr_toReal_nonneg p a) a

lemma pr_le_one {α : Type} [Fintype α] (p : PMF α) (S : Set α) : pr p S ≤ 1 := by
  have h := pr_add_compl p S
  have : 0 ≤ pr p Sᶜ := by
    rw [pr_eq_sum]
    exact Finset.sum_nonneg (fun a _ => Set.indicator_nonneg (fun a _ => pr_toReal_nonneg p a) a)
  linarith

lemma pr_nonneg {α : Type} [Fintype α] (p : PMF α) (S : Set α) : 0 ≤ pr p S := by
  rw [pr_eq_sum]
  exact Finset.sum_nonneg (fun a _ => Set.indicator_nonneg (fun a _ => pr_toReal_nonneg p a) a)

lemma exp_bit {m n : ℕ} (p : PMF (Assignment m n)) (i : Fin m) (j : Fin n) :
    ∑ Y, (p Y).toReal * bit (Y i j) = pr p {Y | Y i j = true} := by
  rw [pr_eq_sum]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases h : Y i j = true
  · rw [Set.indicator_of_mem (show Y ∈ {Y : Assignment m n | Y i j = true} from h)]
    simp [bit, h]
  · rw [Set.indicator_of_notMem (show Y ∉ {Y : Assignment m n | Y i j = true} from h)]
    simp [bit, h]

lemma seg_zero {ϵ δ v : ℝ} (hϵ : 0 < ϵ) (hδ : 0 < δ) (h : seg ϵ δ v = 0) : v ≤ δ := by
  unfold seg at h
  by_cases hv0 : v ≤ δ
  · exact hv0
  · exfalso
    rw [if_neg hv0] at h
    have hv : δ < v := lt_of_not_ge hv0
    have hl : 0 < Real.log (1 + ϵ) := Real.log_pos (by linarith)
    have hq : 0 < Real.log (v / δ) := Real.log_pos (by rw [one_lt_div hδ]; exact hv)
    have : 0 < ⌈Real.log (v / δ) / Real.log (1 + ϵ)⌉₊ := Nat.ceil_pos.2 (div_pos hq hl)
    omega

lemma typeOf_rho {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (j : Fin n) :
    typeOf I ϵ δ (rho I ϵ δ j) = typeVec I ϵ δ j := by
  unfold typeOf rho
  exact List.idxOf_get _

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by unfold bit; split_ifs <;> norm_num

lemma bit_le_one (b : Bool) : bit b ≤ 1 := by unfold bit; split_ifs <;> norm_num

/-- Claim 2.4: concentration for a small type. -/
theorem small_type {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h9 : δ ≤ ϵ ^ 3 / (16 * (numTypes I ϵ δ : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ))))
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (y : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Feasible y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd)
    (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)) (hd : d ∈ I.A i)
    (hsmall : typeOf I ϵ δ t i d = 0)
    (hS : ∃ k : ℕ, Slo i d t = (k : ℝ) * (ϵ / (numTypes I ϵ δ : ℝ))) :
    1 - 1 / (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ)) ≤
      pr (rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y)
        {Y | (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)} := by
  have hp := hrnd _ y hy.1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos d).ne'
  have hN1 : (1 : ℝ) ≤ (numTypes I ϵ δ : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.pos t).ne'
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (numTypes I ϵ δ : ℝ) := ⟨_, rfl⟩
  rw [← hN] at h9 hS hN1 ⊢
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (m : ℝ) * (D : ℝ) * N := ⟨_, rfl⟩
  have hM2 : 2 ≤ M := by
    rw [hM]
    have : (1 : ℝ) ≤ (m : ℝ) * D := by nlinarith
    have : (1 : ℝ) ≤ (m : ℝ) * D * N := by nlinarith
    nlinarith
  rw [show 2 * (m : ℝ) * (D : ℝ) * N = M from hM.symm] at h9 ⊢
  -- small loads
  have hsml : ∀ j, rho I ϵ δ j = t → I.ℓ i j d ≤ δ := by
    intro j hj
    apply seg_zero hϵ0 hδ0
    have := hsmall
    rw [← hj, typeOf_rho] at this
    simp only [typeVec, if_pos hd] at this
    exact this
  obtain ⟨k, hk⟩ := hS
  -- the target set and its complement
  set p := rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y with hpdef
  have hcompl := pr_add_compl p
    {Y | (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)}
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- Slo = 0: the event is certain
    have hS0 : Slo i d t = 0 := by rw [hk, hk0]; simp
    have h0 : pr p {Y | (1 - ϵ) * Slo i d t ≤
        ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)}ᶜ ≤ pr p ∅ := by
      apply pr_mono p
      intro Y hY
      exfalso
      apply (Set.mem_compl_iff _ _).1 hY
      show (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)
      rw [hS0, mul_zero]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (I.ℓ_mem i j d).1 (bit_nonneg _))
    have hempty : pr p ∅ = 0 := by rw [pr_eq_sum]; simp
    have hMpos : 0 < 1 / M := by positivity
    linarith
  · -- Chernoff
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hNpos : 0 < N := by linarith
    have hSlo : ϵ / N ≤ Slo i d t := by
      rw [hk]; have : 0 < ϵ / N := div_pos hϵ0 hNpos; nlinarith
    -- S4
    have hS4 : (1 - ϵ / 2) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * y i j := by
      have := hy.2 i d t (by simp [mkLP, hd, hsmall])
      exact this
    have hα : ∀ j, (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).ρ j = t →
        (fun j => I.ℓ i j d / δ) j ∈ Set.Icc (0 : ℝ) 1 := by
      intro j hj
      refine ⟨div_nonneg (I.ℓ_mem i j d).1 hδ0.le, ?_⟩
      show I.ℓ i j d / δ ≤ 1
      rw [div_le_one hδ0]; exact hsml j hj
    obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = (1 - ϵ / 2) * Slo i d t / δ := ⟨_, rfl⟩
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (ϵ / 2) / (1 - ϵ / 2) := ⟨_, rfl⟩
    have he2 : 0 < 1 - ϵ / 2 := by linarith
    have hη : η ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [hηdef]
      constructor
      · positivity
      · rw [div_lt_one he2]; linarith
    have hmarg : ∀ j, ∑ Y, (p Y).toReal * bit (Y i j) = y i j := by
      intro j; exact (exp_bit p i j).trans (hp.marginal i j)
    have hexp : ∑ Y, (p Y).toReal * ∑ j with rho I ϵ δ j = t, I.ℓ i j d / δ * bit (Y i j) =
        ∑ j with rho I ϵ δ j = t, I.ℓ i j d / δ * y i j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hmarg j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _; ring
    have hlam : lam ≤ ∑ Y, (p Y).toReal *
        ∑ j with rho I ϵ δ j = t, I.ℓ i j d / δ * bit (Y i j) := by
      rw [hexp, hlamdef]
      have : ∑ j with rho I ϵ δ j = t, I.ℓ i j d / δ * y i j =
          (∑ j with rho I ϵ δ j = t, I.ℓ i j d * y i j) / δ := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring
      rw [this]
      exact div_le_div_of_nonneg_right hS4 hδ0.le
    have hconc := hp.concentration i t (fun j => I.ℓ i j d / δ) hα lam η hlam hη
    -- complement is inside the Chernoff event
    have hbad : pr p {Y | (1 - ϵ) * Slo i d t ≤
        ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)}ᶜ ≤
        Real.exp (-(lam * η ^ 2 / 2)) := by
      refine le_trans ?_ hconc
      apply pr_mono p
      intro Y hY
      have hY' : ¬ ((1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)) :=
        hY
      push_neg at hY'
      show ∑ j with rho I ϵ δ j = t, I.ℓ i j d / δ * bit (Y i j) ≤ (1 - η) * lam
      have e1 : ∑ j with rho I ϵ δ j = t, I.ℓ i j d / δ * bit (Y i j) =
          (∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)) / δ := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring
      have e2 : (1 - η) * lam = (1 - ϵ) * Slo i d t / δ := by
        have h2ne : (1 : ℝ) - ϵ / 2 ≠ 0 := he2.ne'
        have h2ne' : (2 : ℝ) - ϵ ≠ 0 := by intro h; linarith
        rw [hηdef, hlamdef]; field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hY'.le hδ0.le
    -- the exponent
    have hLpos : 0 < Real.log M := Real.log_pos (by linarith)
    have hL : Real.log M * (16 * N * δ) ≤ ϵ ^ 3 := by
      have hden : 0 < 16 * N * Real.log M := by positivity
      rw [le_div_iff₀ hden] at h9
      linarith
    have hexpo : Real.log M ≤ lam * η ^ 2 / 2 := by
      have hQ : lam * η ^ 2 / 2 = Slo i d t * ϵ ^ 2 / (8 * δ * (1 - ϵ / 2)) := by
        have h2ne : (1 : ℝ) - ϵ / 2 ≠ 0 := he2.ne'
        have h2ne' : (2 : ℝ) - ϵ ≠ 0 := by intro h; linarith
        rw [hlamdef, hηdef]; field_simp; ring
      rw [hQ, le_div_iff₀ (mul_pos (by linarith : (0 : ℝ) < 8 * δ) he2)]
      have h1 : Real.log M * (8 * δ * (1 - ϵ / 2)) ≤ Real.log M * (8 * δ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hLpos.le
      have h2 : N * (Real.log M * (8 * δ)) ≤ ϵ ^ 3 / 2 := by nlinarith
      have h3 : Real.log M * (8 * δ) ≤ ϵ ^ 3 / 2 / N := by
        rw [le_div_iff₀ hNpos]; linarith
      have h4 : ϵ ^ 3 / 2 / N ≤ ϵ ^ 3 / N := by
        apply div_le_div_of_nonneg_right _ hNpos.le; nlinarith [pow_pos hϵ0 3]
      have h5 : ϵ ^ 3 / N ≤ Slo i d t * ϵ ^ 2 := by
        have : ϵ / N * ϵ ^ 2 ≤ Slo i d t * ϵ ^ 2 :=
          mul_le_mul_of_nonneg_right hSlo (by positivity)
        have e : ϵ / N * ϵ ^ 2 = ϵ ^ 3 / N := by ring
        linarith
      linarith
    have hexpb : Real.exp (-(lam * η ^ 2 / 2)) ≤ 1 / M := by
      calc Real.exp (-(lam * η ^ 2 / 2)) ≤ Real.exp (-Real.log M) :=
            Real.exp_le_exp.2 (by linarith)
        _ = 1 / M := by
            rw [Real.exp_neg, Real.exp_log (show (0 : ℝ) < M by linarith), one_div]
    linarith

end Aux_Small

namespace Aux_L23

open FreeOrderEPTAS Aux_Small

lemma pr_mono_supp {α : Type} [Fintype α] (p : PMF α) {S T : Set α}
    (h : ∀ a, p a ≠ 0 → a ∈ S → a ∈ T) : pr p S ≤ pr p T := by
  rw [pr_eq_sum, pr_eq_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases haS : a ∈ S
  · rw [Set.indicator_of_mem haS]
    by_cases hp0 : p a = 0
    · rw [hp0, ENNReal.toReal_zero]
      exact Set.indicator_nonneg (fun a _ => pr_toReal_nonneg p a) a
    · rw [Set.indicator_of_mem (h a hp0 haS)]
  · rw [Set.indicator_of_notMem haS]
    exact Set.indicator_nonneg (fun a _ => pr_toReal_nonneg p a) a

lemma pr_union {α ι : Type} [Fintype α] (p : PMF α) (T : Finset ι) (S : ι → Set α) (U : Set α)
    (hU : ∀ a ∈ U, ∃ τ ∈ T, a ∈ S τ) : pr p U ≤ ∑ τ ∈ T, pr p (S τ) := by
  simp only [pr_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases haU : a ∈ U
  · obtain ⟨τ, hτ, haτ⟩ := hU a haU
    rw [Set.indicator_of_mem haU]
    calc (p a).toReal = (S τ).indicator (fun a => (p a).toReal) a := by
          rw [Set.indicator_of_mem haτ]
      _ ≤ ∑ τ ∈ T, (S τ).indicator (fun a => (p a).toReal) a :=
          Finset.single_le_sum (f := fun τ => (S τ).indicator (fun a => (p a).toReal) a)
            (fun τ _ => Set.indicator_nonneg (fun a _ => pr_toReal_nonneg p a) a) hτ
  · rw [Set.indicator_of_notMem haU]
    exact Finset.sum_nonneg (fun τ _ => Set.indicator_nonneg (fun a _ => pr_toReal_nonneg p a) a)

lemma sum_min_ge {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (h1 : 1 ≤ ∑ i ∈ s, f i) : 1 ≤ ∑ i ∈ s, min (f i) 1 := by
  by_cases h : ∃ i ∈ s, 1 ≤ f i
  · obtain ⟨i, hi, hfi⟩ := h
    have : min (f i) 1 = 1 := min_eq_right hfi
    calc (1 : ℝ) = min (f i) 1 := this.symm
      _ ≤ ∑ i ∈ s, min (f i) 1 :=
          Finset.single_le_sum (f := fun i => min (f i) 1)
            (fun j _ => le_min (hf j) zero_le_one) hi
  · push_neg at h
    have : ∑ i ∈ s, min (f i) 1 = ∑ i ∈ s, f i :=
      Finset.sum_congr rfl (fun i hi => min_eq_left (h i hi).le)
    rw [this]; exact h1

lemma floor_bound (a u : ℝ) (hu : 0 < u) : a - u ≤ (⌊a / u⌋₊ : ℝ) * u ∨ a < 0 := by
  by_cases ha : 0 ≤ a
  · left
    have h1 : a / u < ⌊a / u⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : a < (⌊a / u⌋₊ + 1) * u := by rw [div_lt_iff₀ hu] at h1; exact h1
    nlinarith
  · right; linarith

theorem main {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h9 : 0 < m * D * numTypes I ϵ δ → δ ≤ ϵ ^ 3 / (16 * (numTypes I ϵ δ : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ))))
    (x : Assignment m n) (hload : LoadAtLeast I x 1)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ (ϵ / 2) x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Feasible y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd) :
    (1 / 2 : ℝ) ≤ pr (rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y)
      {Y | LoadAtLeast I Y (1 - 2 * ϵ)} := by
  have hp := hrnd _ y hy.1
  set p := rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y with hpdef
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin m × Fin D × Fin (numTypes I ϵ δ)),
      T = Finset.univ.filter (fun τ => τ.2.1 ∈ I.A τ.1 ∧ typeOf I ϵ δ τ.2.2 τ.1 τ.2.1 = 0) :=
    ⟨_, rfl⟩
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Fin m × Fin D × Fin (numTypes I ϵ δ) → Set (Assignment m n),
      Sg = fun τ => {Y | (1 - ϵ) * Slo τ.1 τ.2.1 τ.2.2 ≤
        ∑ j with rho I ϵ δ j = τ.2.2, I.ℓ τ.1 j τ.2.1 * bit (Y τ.1 j)} := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Set (Assignment m n), G = {Y | ∀ τ ∈ T, Y ∈ Sg τ} := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ) := ⟨_, rfl⟩
  -- each bad event is rare
  have hbad : ∀ τ ∈ T, pr p (Sg τ)ᶜ ≤ 1 / M := by
    intro τ hτ
    obtain ⟨i, d, t⟩ := τ
    rw [hT] at hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨hd, hsm⟩ := hτ
    have hpos : 0 < m * D * numTypes I ϵ δ :=
      Nat.mul_pos (Nat.mul_pos (Fin.pos i) (Fin.pos d)) (Fin.pos t)
    have hS : ∃ k : ℕ, Slo i d t = (k : ℝ) * (ϵ / (numTypes I ϵ δ : ℝ)) :=
      ⟨_, hg.small i d hd t hsm⟩
    have h1 := small_type I ϵ δ hϵ0 hϵ1 hδ0 hδ1 (h9 hpos) Nlo Nhi Slo y hy rnd hrnd i d t hd hsm hS
    have h2 := pr_add_compl p
      {Y | (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)}
    rw [hSg]
    show pr p {Y | (1 - ϵ) * Slo i d t ≤
      ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)}ᶜ ≤ 1 / M
    rw [hM]
    linarith
  -- union bound
  have hGc : pr p Gᶜ ≤ ∑ τ ∈ T, pr p (Sg τ)ᶜ := by
    apply pr_union p T (fun τ => (Sg τ)ᶜ) Gᶜ
    intro Y hY
    rw [hG] at hY
    have hY' : ¬ ∀ τ ∈ T, Y ∈ Sg τ := hY
    push_neg at hY'
    exact hY'
  have hsum : ∑ τ ∈ T, pr p (Sg τ)ᶜ ≤ (T.card : ℝ) * (1 / M) := by
    calc ∑ τ ∈ T, pr p (Sg τ)ᶜ ≤ ∑ τ ∈ T, (1 / M) := Finset.sum_le_sum hbad
      _ = (T.card : ℝ) * (1 / M) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (T.card : ℝ) * (1 / M) ≤ 1 / 2 := by
    by_cases hT0 : T.card = 0
    · rw [hT0]; norm_num
    · have hle : T.card ≤ m * D * numTypes I ϵ δ := by
        have := Finset.card_le_univ T
        simpa [Fintype.card_prod, Fintype.card_fin, mul_assoc] using this
      have hpos : 0 < m * D * numTypes I ϵ δ := by
        apply Nat.pos_of_ne_zero
        intro h; rw [h] at hle; omega
      have hMpos : 0 < M := by
        rw [hM]
        have : (0 : ℝ) < (m * D * numTypes I ϵ δ : ℕ) := by exact_mod_cast hpos
        push_cast at this
        linarith
      have hle' : (T.card : ℝ) ≤ M / 2 := by
        rw [hM]
        have : (T.card : ℝ) ≤ (m * D * numTypes I ϵ δ : ℕ) := by exact_mod_cast hle
        push_cast at this
        linarith
      rw [mul_one_div, div_le_iff₀ hMpos]
      linarith
  have hGcompl := pr_add_compl p G
  -- the good event implies the load bound (on the support)
  have hGL : pr p G ≤ pr p {Y | LoadAtLeast I Y (1 - 2 * ϵ)} := by
    apply pr_mono_supp p
    intro Y hY0 hYG
    have hYs : Y ∈ p.support := (PMF.mem_support_iff _ _).2 hY0
    rw [hG] at hYG
    have hYG' : ∀ τ ∈ T, Y ∈ Sg τ := hYG
    show LoadAtLeast I Y (1 - 2 * ϵ)
    intro i d hd
    have hl := hload i d hd
    unfold load at hl ⊢
    have hfib : ∀ z : Assignment m n, ∑ j, I.ℓ i j d * bit (z i j) =
        ∑ t, ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (z i j) := by
      intro z
      exact (Finset.sum_fiberwise Finset.univ (rho I ϵ δ) _).symm
    rw [hfib x] at hl
    have hYfib := hfib Y
    have hN : 0 < numTypes I ϵ δ := by
      by_contra h0
      push_neg at h0
      have h00 : numTypes I ϵ δ = 0 := by omega
      have : ∑ t : Fin (numTypes I ϵ δ), ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (x i j) = 0 := by
        apply Finset.sum_eq_zero; intro t _; exact absurd t.pos (by omega)
      linarith
    have hNr : (0 : ℝ) < numTypes I ϵ δ := by exact_mod_cast hN
    have hu : 0 < ϵ / (numTypes I ϵ δ : ℝ) := div_pos hϵ0 hNr
    have hper : ∀ t, (1 - ϵ) * (min (Sip I ϵ δ x i d t) 1 - ϵ / (numTypes I ϵ δ : ℝ)) ≤
        ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j) := by
      intro t
      have hS0 := Aux_Types.Sip_nonneg I ϵ δ x i d t
      have hmin0 : 0 ≤ min (Sip I ϵ δ x i d t) 1 := le_min hS0 zero_le_one
      by_cases hsm : typeOf I ϵ δ t i d = 0
      · have hτ : (i, d, t) ∈ T := by rw [hT]; simp [hd, hsm]
        have h1 : (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j) := by
          have := hYG' _ hτ
          rw [hSg] at this
          exact this
        have h2 : min (Sip I ϵ δ x i d t) 1 - ϵ / (numTypes I ϵ δ : ℝ) ≤ Slo i d t := by
          rw [hg.small i d hd t hsm]
          rcases floor_bound (min (Sip I ϵ δ x i d t) 1) _ hu with h | h
          · exact h
          · linarith
        have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - ϵ)
        linarith
      · have hlarge : 1 ≤ typeOf I ϵ δ t i d := by omega
        have hcnt := (hp.degree Y hYs).2 i t
        have h1 := Aux_Types.large_type I ϵ δ (ϵ / 2) hϵ0 hϵ1 hδ0 x Nlo Nhi Slo hg Y i d t hd
          hlarge ⟨hcnt.1, hcnt.2⟩
        have h2 : (1 - ϵ) * (min (Sip I ϵ δ x i d t) 1 - ϵ / (numTypes I ϵ δ : ℝ)) ≤
            (1 - ϵ) * min (Sip I ϵ δ x i d t) 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
        linarith
    have hsumt := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hper t)
    have hmin : 1 ≤ ∑ t, min (Sip I ϵ δ x i d t) 1 := by
      apply sum_min_ge _ _ (fun t => Aux_Types.Sip_nonneg I ϵ δ x i d t)
      unfold Sip; exact hl
    have hcalc : ∑ t : Fin (numTypes I ϵ δ),
        (1 - ϵ) * (min (Sip I ϵ δ x i d t) 1 - ϵ / (numTypes I ϵ δ : ℝ)) =
        (1 - ϵ) * (∑ t, min (Sip I ϵ δ x i d t) 1 - ϵ) := by
      have e : (numTypes I ϵ δ : ℝ) * (ϵ / (numTypes I ϵ δ : ℝ)) = ϵ := by
        field_simp
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, e]
    rw [hcalc] at hsumt
    have : (1 - ϵ) * (1 - ϵ) ≤ (1 - ϵ) * (∑ t, min (Sip I ϵ δ x i d t) 1 - ϵ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [hYfib, hsumt, this]
  linarith

end Aux_L23

open FreeOrderEPTAS in
theorem solution {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h9 : 0 < m * D * numTypes I ϵ δ → δ ≤ ϵ ^ 3 / (16 * (numTypes I ϵ δ : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ))))
    (x : Assignment m n) (hload : LoadAtLeast I x 1)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ (ϵ / 2) x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Feasible y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd) :
    (1 / 2 : ℝ) ≤ pr (rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y)
      {Y | LoadAtLeast I Y (1 - 2 * ϵ)} :=
  Aux_L23.main I ϵ δ hϵ0 hϵ1 hδ0 hδ1 h9 x hload Nlo Nhi Slo hg y hy rnd hrnd
