-- Prove2me | solution 1 for FreeOrderEPTAS.claim_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:30:32.782188+00:00
-- url     : https://prove2.me/submissions/8519b55f-74db-40fe-862a-5922e4e7e4b7

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

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

open FreeOrderEPTAS in
theorem solution {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
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
        {Y | (1 - ϵ) * Slo i d t ≤ ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (Y i j)} :=
  Aux_Small.small_type I ϵ δ hϵ0 hϵ1 hδ0 hδ1 h9 Nlo Nhi Slo y hy rnd hrnd i d t hd hsmall hS
