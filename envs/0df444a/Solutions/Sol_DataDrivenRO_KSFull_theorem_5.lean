-- Prove2me | solution 1 for DataDrivenRO.KSFull.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T05:37:22.027708+00:00
-- url     : https://prove2.me/submissions/856d3748-145d-4aa8-b82d-f38f76d09a11

import Mathlib
import Definitions.Def_DataDrivenRO_KSFull_Setting

set_option maxHeartbeats 2000000

set_option autoImplicit false

open MeasureTheory


namespace GibbsMaxAux9f

lemma term_le (c pj qj Z : ℝ) (hp : 0 ≤ pj) (hq : 0 ≤ qj) (hZ : 0 < Z)
    (habs : 0 < qj → 0 < pj) :
    c * qj - qj * Real.log (qj / pj) - qj * Real.log Z ≤ pj * Real.exp c / Z - qj := by
  rcases hq.eq_or_lt with h | h
  · subst h
    simp only [zero_mul, mul_zero, sub_zero, zero_div, Real.log_zero]
    positivity
  · have hpj : 0 < pj := habs h
    set a : ℝ := pj * Real.exp c / (Z * qj) with ha
    have ha0 : 0 < a := by positivity
    have hlog : Real.log a = Real.log pj + c - Real.log Z - Real.log qj := by
      rw [ha, Real.log_div (by positivity) (by positivity),
        Real.log_mul hpj.ne' (Real.exp_pos c).ne', Real.log_mul hZ.ne' h.ne', Real.log_exp]
      ring
    have hdiv : Real.log (qj / pj) = Real.log qj - Real.log pj :=
      Real.log_div h.ne' hpj.ne'
    have key := Real.log_le_sub_one_of_pos ha0
    have h1 : qj * Real.log a ≤ qj * (a - 1) := mul_le_mul_of_nonneg_left key h.le
    have h2 : qj * a = pj * Real.exp c / Z := by
      rw [ha]; field_simp
    rw [hdiv]
    rw [hlog] at h1
    nlinarith [h1, h2]

lemma term_eq (c pj Z : ℝ) (hp : 0 ≤ pj) (hZ : 0 < Z) :
    c * (pj * Real.exp c / Z) - (pj * Real.exp c / Z) * Real.log ((pj * Real.exp c / Z) / pj)
      = (pj * Real.exp c / Z) * Real.log Z := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp
  · have : (pj * Real.exp c / Z) / pj = Real.exp c / Z := by
      field_simp
    rw [this, Real.log_div (Real.exp_pos c).ne' hZ.ne', Real.log_exp]
    ring

end GibbsMaxAux9f

open DataDrivenRO.KS in
theorem gibbs_max {n : ℕ} (c p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    IsGreatest
      {s | ∃ q ∈ stdSimplex ℝ (Fin n), AbsCont q p ∧
        s = ∑ j, c j * q j - relEntropy q p}
      (Real.log (∑ j, p j * Real.exp (c j))) := by
  obtain ⟨hp0, hp1⟩ := hp
  set Z : ℝ := ∑ j, p j * Real.exp (c j) with hZdef
  have hZ : 0 < Z := by
    have hne : ∃ j, 0 < p j := by
      by_contra hcon
      push Not at hcon
      have : ∑ j, p j = 0 :=
        Finset.sum_eq_zero (fun j _ => le_antisymm (hcon j) (hp0 j))
      rw [hp1] at this; exact one_ne_zero this
    obtain ⟨j, hj⟩ := hne
    calc 0 < p j * Real.exp (c j) := by positivity
      _ ≤ Z := Finset.single_le_sum (f := fun j => p j * Real.exp (c j))
            (fun i _ => mul_nonneg (hp0 i) (Real.exp_pos _).le) (Finset.mem_univ j)
  constructor
  · refine ⟨fun j => p j * Real.exp (c j) / Z, ⟨fun j => by have := hp0 j; positivity, ?_⟩, ?_, ?_⟩
    · rw [← Finset.sum_div, ← hZdef, div_self hZ.ne']
    · intro j hj
      rcases (hp0 j).eq_or_lt with h | h
      · simp [← h] at hj
      · exact h
    · unfold relEntropy
      rw [← Finset.sum_sub_distrib]
      simp only [GibbsMaxAux9f.term_eq (c _) (p _) Z (hp0 _) hZ]
      rw [← Finset.sum_mul, ← Finset.sum_div, ← hZdef, div_self hZ.ne', one_mul]
  · rintro s ⟨q, ⟨hq0, hq1⟩, habs, rfl⟩
    unfold relEntropy
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      GibbsMaxAux9f.term_le (c j) (p j) (q j) Z (hp0 j) (hq0 j) hZ (habs j))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hq1, ← Finset.sum_div, ← hZdef, div_self hZ.ne'] at hsum
    linarith



open DataDrivenRO.KS in
theorem b95d1723_mix_sum (N : ℕ) (Γ θ : ℝ) (w : Fin (N + 2) → ℝ) :
    ∑ j, mix N Γ θ j * w j
      = θ * (∑ j, qL N Γ j * w j) + (1 - θ) * (∑ j, qR N Γ j * w j) := by
  simp only [mix, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

open DataDrivenRO.KS in
theorem theta_endpoint (N : ℕ) (Γ : ℝ) (w : Fin (N + 2) → ℝ) :
    IsGreatest ((fun θ : ℝ => ∑ j, mix N Γ θ j * w j) '' Set.Icc 0 1)
      (max (∑ j, qL N Γ j * w j) (∑ j, qR N Γ j * w j)) := by
  set A := ∑ j, qL N Γ j * w j
  set B := ∑ j, qR N Γ j * w j
  constructor
  · rcases le_total A B with h | h
    · refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      simp only [b95d1723_mix_sum]
      rw [max_eq_right h]; ring
    · refine ⟨1, ⟨zero_le_one, le_refl _⟩, ?_⟩
      simp only [b95d1723_mix_sum]
      rw [max_eq_left h]; ring
  · rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp only [b95d1723_mix_sum]
    have hA : A ≤ max A B := le_max_left _ _
    have hB : B ≤ max A B := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hA h0, mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr h1)]


namespace DataDrivenRO.KS

lemma c2_logsum {a1 a2 b1 b2 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : 0 < a1 → 0 < b1) (h2 : 0 < a2 → 0 < b2) :
    (a1 + a2) * Real.log ((a1 + a2) / (b1 + b2)) ≤ a1 * Real.log (a1 / b1) + a2 * Real.log (a2 / b2) := by
  rcases ha1.eq_or_lt with rfl | ha1'
  · simp only [zero_add, zero_mul]
    rcases ha2.eq_or_lt with rfl | ha2'
    · simp
    · have hb2' := h2 ha2'
      apply mul_le_mul_of_nonneg_left _ ha2
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left ha2 hb2' (by linarith)
  · rcases ha2.eq_or_lt with rfl | ha2'
    · simp only [add_zero, zero_mul]
      have hb1' := h1 ha1'
      apply mul_le_mul_of_nonneg_left _ ha1
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left ha1 hb1' (by linarith)
    · have hb1' := h1 ha1'
      have hb2' := h2 ha2'
      have hB : 0 < b1 + b2 := by linarith
      have key := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (by positivity : 0 ≤ a1 / b1))
        (Set.mem_Ici.2 (by positivity : 0 ≤ a2 / b2))
        (by positivity : 0 ≤ b1 / (b1 + b2)) (by positivity : 0 ≤ b2 / (b1 + b2))
        (by field_simp : b1 / (b1 + b2) + b2 / (b1 + b2) = 1)
      simp only [smul_eq_mul] at key
      have e1 : b1 / (b1 + b2) * (a1 / b1) + b2 / (b1 + b2) * (a2 / b2) = (a1 + a2) / (b1 + b2) := by
        field_simp
      rw [e1] at key
      have e2 : b1 / (b1 + b2) * (a1 / b1 * Real.log (a1 / b1)) + b2 / (b1 + b2) * (a2 / b2 * Real.log (a2 / b2))
          = (a1 * Real.log (a1 / b1) + a2 * Real.log (a2 / b2)) / (b1 + b2) := by
        field_simp
      rw [e2] at key
      have := mul_le_mul_of_nonneg_left key hB.le
      have e3 : (b1 + b2) * ((a1 + a2) / (b1 + b2) * Real.log ((a1 + a2) / (b1 + b2)))
          = (a1 + a2) * Real.log ((a1 + a2) / (b1 + b2)) := by field_simp
      have e4 : (b1 + b2) * ((a1 * Real.log (a1 / b1) + a2 * Real.log (a2 / b2)) / (b1 + b2))
          = a1 * Real.log (a1 / b1) + a2 * Real.log (a2 / b2) := by field_simp
      rw [e3, e4] at this
      exact this

lemma c2_term {s t a1 a2 b1 b2 : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (h1 : 0 < a1 → 0 < b1) (h2 : 0 < a2 → 0 < b2) :
    (s * a1 + t * a2) * Real.log ((s * a1 + t * a2) / (s * b1 + t * b2))
      ≤ s * (a1 * Real.log (a1 / b1)) + t * (a2 * Real.log (a2 / b2)) := by
  have hs' : ∀ a b : ℝ, s * a * Real.log (s * a / (s * b)) = s * (a * Real.log (a / b)) := by
    intro a b
    rcases hs.eq_or_lt with rfl | hs0
    · simp
    · rw [mul_div_mul_left _ _ hs0.ne']; ring
  have ht' : ∀ a b : ℝ, t * a * Real.log (t * a / (t * b)) = t * (a * Real.log (a / b)) := by
    intro a b
    rcases ht.eq_or_lt with rfl | ht0
    · simp
    · rw [mul_div_mul_left _ _ ht0.ne']; ring
  have := c2_logsum (a1 := s * a1) (a2 := t * a2) (b1 := s * b1) (b2 := t * b2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (fun h => by
      rcases hs.eq_or_lt with rfl | hs0
      · simp at h
      · exact mul_pos hs0 (h1 (lt_of_le_of_ne ha1 (fun e => by rw [← e] at h; simp at h))))
    (fun h => by
      rcases ht.eq_or_lt with rfl | ht0
      · simp at h
      · exact mul_pos ht0 (h2 (lt_of_le_of_ne ha2 (fun e => by rw [← e] at h; simp at h))))
  rw [hs', ht'] at this
  exact this


lemma qL_nonneg (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (j : Fin (N + 2)) :
    0 ≤ qL N Γ j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold qL
  split_ifs with h1 h2 h3
  · exact hΓ0.le
  · positivity
  · have : (⌊(N : ℝ) * (1 - Γ)⌋₊ : ℝ) ≤ N * (1 - Γ) := Nat.floor_le (by nlinarith)
    have h4 : (⌊(N : ℝ) * (1 - Γ)⌋₊ : ℝ) / N ≤ 1 - Γ := by
      rw [div_le_iff₀ hNr]; linarith
    linarith
  · exact le_refl _

lemma qR_nonneg (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (j : Fin (N + 2)) :
    0 ≤ qR N Γ j := qL_nonneg N hN Γ hΓ0 hΓ1 _

lemma mix_nonneg (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (j : Fin (N + 2)) : 0 ≤ mix N Γ θ j := by
  unfold mix
  have := qL_nonneg N hN Γ hΓ0 hΓ1 j
  have := qR_nonneg N hN Γ hΓ0 hΓ1 j
  have := hθ.1
  have := hθ.2
  have : 0 ≤ 1 - θ := by linarith
  positivity

lemma mix_comb (N : ℕ) (Γ θ θ' s t : ℝ) (hst : s + t = 1) (j : Fin (N + 2)) :
    mix N Γ (s * θ + t * θ') j = s * mix N Γ θ j + t * mix N Γ θ' j := by
  unfold mix
  linear_combination (-(qR N Γ j)) * hst

lemma relEntropy_comb {n : ℕ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (q q' p p' : Fin n → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hq' : ∀ j, 0 ≤ q' j) (hp : ∀ j, 0 ≤ p j) (hp' : ∀ j, 0 ≤ p' j)
    (h : AbsCont q p) (h' : AbsCont q' p') :
    relEntropy (fun j => s * q j + t * q' j) (fun j => s * p j + t * p' j)
      ≤ s * relEntropy q p + t * relEntropy q' p' := by
  unfold relEntropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact c2_term hs ht (hq j) (hq' j) (hp j) (hp' j) (h j) (h' j)

lemma absCont_comb {n : ℕ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (q q' p p' : Fin n → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hq' : ∀ j, 0 ≤ q' j) (hp : ∀ j, 0 ≤ p j) (hp' : ∀ j, 0 ≤ p' j)
    (h : AbsCont q p) (h' : AbsCont q' p') :
    AbsCont (fun j => s * q j + t * q' j) (fun j => s * p j + t * p' j) := by
  intro j hj
  have a1 := mul_nonneg hs (hq j)
  have a2 := mul_nonneg ht (hq' j)
  have b1 := mul_nonneg hs (hp j)
  have b2 := mul_nonneg ht (hp' j)
  by_cases h1 : 0 < s * q j
  · have : 0 < p j := h j (lt_of_le_of_ne (hq j) (fun e => by rw [← e] at h1; simp at h1))
    have hs0 : 0 < s := lt_of_le_of_ne hs (fun e => by rw [← e] at h1; simp at h1)
    have := mul_pos hs0 this
    simp only; linarith
  · have h2 : 0 < t * q' j := by simp only at hj; push Not at h1; linarith
    have : 0 < p' j := h' j (lt_of_le_of_ne (hq' j) (fun e => by rw [← e] at h2; simp at h2))
    have ht0 : 0 < t := lt_of_le_of_ne ht (fun e => by rw [← e] at h2; simp at h2)
    have := mul_pos ht0 this
    simp only; linarith

theorem UI_convex {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ ε : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) :
    Convex ℝ (UI uhat Γ ε) := by
  intro u hu u' hu' s t hs ht hst
  obtain ⟨θ, q, hθ, hq, hu1, hac, hD⟩ := hu
  obtain ⟨θ', q', hθ', hq', hu1', hac', hD'⟩ := hu'
  refine ⟨fun i => s * θ i + t * θ' i, fun i j => s * q i j + t * q' i j, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨by have := (hθ i).1; have := (hθ' i).1; positivity, ?_⟩
    have := (hθ i).2; have := (hθ' i).2
    nlinarith
  · intro i
    exact (convex_stdSimplex ℝ (Fin (N + 2))) (hq i) (hq' i) hs ht hst
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ j, uhat i j * (s * q i j + t * q' i j)
        = s * ∑ j, uhat i j * q i j + t * ∑ j, uhat i j * q' i j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this, hu1 i, hu1' i]
  · intro i
    have hmix : mix N Γ (s * θ i + t * θ' i) = fun j => s * mix N Γ (θ i) j + t * mix N Γ (θ' i) j := by
      funext j; exact mix_comb N Γ _ _ s t hst j
    simp only
    rw [hmix]
    exact absCont_comb hs ht _ _ _ _ (fun j => (hq i).1 j) (fun j => (hq' i).1 j)
      (mix_nonneg N hN Γ hΓ0 hΓ1 (hθ i)) (mix_nonneg N hN Γ hΓ0 hΓ1 (hθ' i)) (hac i) (hac' i)
  · have hle : ∀ i, relEntropy (fun j => s * q i j + t * q' i j) (mix N Γ (s * θ i + t * θ' i))
        ≤ s * relEntropy (q i) (mix N Γ (θ i)) + t * relEntropy (q' i) (mix N Γ (θ' i)) := by
      intro i
      have hmix : mix N Γ (s * θ i + t * θ' i) = fun j => s * mix N Γ (θ i) j + t * mix N Γ (θ' i) j := by
        funext j; exact mix_comb N Γ _ _ s t hst j
      rw [hmix]
      exact relEntropy_comb hs ht _ _ _ _ (fun j => (hq i).1 j) (fun j => (hq' i).1 j)
        (mix_nonneg N hN Γ hΓ0 hΓ1 (hθ i)) (mix_nonneg N hN Γ hΓ0 hΓ1 (hθ' i)) (hac i) (hac' i)
    calc ∑ i, relEntropy (fun j => s * q i j + t * q' i j) (mix N Γ (s * θ i + t * θ' i))
        ≤ ∑ i, (s * relEntropy (q i) (mix N Γ (θ i)) + t * relEntropy (q' i) (mix N Γ (θ' i))) :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ = s * ∑ i, relEntropy (q i) (mix N Γ (θ i)) + t * ∑ i, relEntropy (q' i) (mix N Γ (θ' i)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ Real.log (1 / ε) := by
          have h1 := mul_le_mul_of_nonneg_left hD hs
          have h2 := mul_le_mul_of_nonneg_left hD' ht
          have h3 : s * Real.log (1 / ε) + t * Real.log (1 / ε) = Real.log (1 / ε) := by
            rw [← add_mul, hst, one_mul]
          linarith

end DataDrivenRO.KS

namespace DataDrivenRO.KS

lemma qL_sum (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) :
    ∑ j, qL N Γ j = 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set m := ⌊(N : ℝ) * (1 - Γ)⌋₊ with hm
  have hm1 : (m : ℝ) ≤ N * (1 - Γ) := Nat.floor_le (by nlinarith)
  have hmN : m < N := by
    have : (m : ℝ) < N := by nlinarith
    exact_mod_cast this
  let g : ℕ → ℝ := fun j =>
    if j = 0 then Γ else if j ≤ m then 1 / N else if j = m + 1 then 1 - Γ - (m : ℝ) / N else 0
  have h1 : ∑ j : Fin (N + 2), qL N Γ j = ∑ j : Fin (N + 2), g (j : ℕ) := rfl
  rw [h1, Fin.sum_univ_eq_sum_range g (N + 2)]
  have h2 : ∑ j ∈ Finset.range (N + 2), g j = ∑ j ∈ Finset.range (m + 2), g j := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro x hx hx'
    simp only [Finset.mem_range] at hx hx'
    simp only [g]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [h2, Finset.sum_range_succ, Finset.sum_range_succ']
  have e0 : g 0 = Γ := by simp [g]
  have e1 : g (m + 1) = 1 - Γ - (m : ℝ) / N := by simp [g]
  have e2 : ∑ i ∈ Finset.range m, g (i + 1) = m * (1 / N) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 / (N : ℝ)))]
    · simp
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega)]
  rw [e0, e1, e2]
  field_simp
  ring

lemma qR_sum (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) :
    ∑ j, qR N Γ j = 1 := by
  unfold qR
  rw [← qL_sum N hN Γ hΓ0 hΓ1]
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 2))) (qL N Γ)

lemma mix_mem_simplex (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : mix N Γ θ ∈ stdSimplex ℝ (Fin (N + 2)) := by
  refine ⟨fun j => mix_nonneg N hN Γ hΓ0 hΓ1 hθ j, ?_⟩
  have : ∑ j, mix N Γ θ j = θ * ∑ j, qL N Γ j + (1 - θ) * ∑ j, qR N Γ j := by
    simp only [mix, Finset.sum_add_distrib, Finset.mul_sum]
  rw [this, qL_sum N hN Γ hΓ0 hΓ1, qR_sum N hN Γ hΓ0 hΓ1]; ring

end DataDrivenRO.KS

namespace DataDrivenRO.KS

lemma c1_scale {n : ℕ} (x q c : Fin n → ℝ) (v lam : ℝ) (hlam : 0 < lam)
    (hc : ∀ j, c j = v * x j / lam) :
    lam * ∑ j, c j * q j = v * ∑ j, x j * q j := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hc j]; field_simp

lemma c1_coord_bound {N : ℕ} (x : Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (v lam : ℝ) (hlam : 0 < lam)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (q : Fin (N + 2) → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin (N + 2))) (hac : AbsCont q (mix N Γ θ)) :
    v * ∑ j, x j * q j - lam * relEntropy q (mix N Γ θ) ≤ lam * Real.log (max
      (∑ j, qL N Γ j * Real.exp (v * x j / lam))
      (∑ j, qR N Γ j * Real.exp (v * x j / lam))) := by
  set c : Fin (N + 2) → ℝ := fun j => v * x j / lam with hc
  have hmix := mix_mem_simplex N hN Γ hΓ0 hΓ1 hθ
  have hg := (gibbs_max c (mix N Γ θ) hmix).2 ⟨q, hq, hac, rfl⟩
  have hZpos : 0 < ∑ j, mix N Γ θ j * Real.exp (c j) := by
    have hex : ∃ j, 0 < mix N Γ θ j := by
      by_contra h
      push Not at h
      have h0 : ∑ j, mix N Γ θ j = 0 :=
        Finset.sum_eq_zero (fun j _ => le_antisymm (h j) (hmix.1 j))
      linarith [hmix.2]
    obtain ⟨j0, hj0⟩ := hex
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hmix.1 j) (Real.exp_pos _).le)
      ⟨j0, Finset.mem_univ _, mul_pos hj0 (Real.exp_pos _)⟩
  have hte := (theta_endpoint N Γ (fun j => Real.exp (c j))).2 ⟨θ, hθ, rfl⟩
  have hle : Real.log (∑ j, mix N Γ θ j * Real.exp (c j)) ≤ Real.log (max
      (∑ j, qL N Γ j * Real.exp (c j)) (∑ j, qR N Γ j * Real.exp (c j))) :=
    Real.log_le_log hZpos hte
  have h1 : ∑ j, c j * q j - relEntropy q (mix N Γ θ) ≤ Real.log (max
      (∑ j, qL N Γ j * Real.exp (c j)) (∑ j, qR N Γ j * Real.exp (c j))) := hg.trans hle
  have h2 := mul_le_mul_of_nonneg_left h1 hlam.le
  have h3 := c1_scale x q c v lam hlam (fun j => rfl)
  rw [mul_sub, h3] at h2
  exact h2

lemma c1_coord_attain {N : ℕ} (x : Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (v lam : ℝ) (hlam : 0 < lam) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, ∃ q ∈ stdSimplex ℝ (Fin (N + 2)), AbsCont q (mix N Γ θ) ∧
      v * ∑ j, x j * q j - lam * relEntropy q (mix N Γ θ) = lam * Real.log (max
      (∑ j, qL N Γ j * Real.exp (v * x j / lam))
      (∑ j, qR N Γ j * Real.exp (v * x j / lam))) := by
  set c : Fin (N + 2) → ℝ := fun j => v * x j / lam with hc
  obtain ⟨θ, hθ, hθeq⟩ := (theta_endpoint N Γ (fun j => Real.exp (c j))).1
  have hmix := mix_mem_simplex N hN Γ hΓ0 hΓ1 hθ
  obtain ⟨q, hq, hac, hqeq⟩ := (gibbs_max c (mix N Γ θ) hmix).1
  refine ⟨θ, hθ, q, hq, hac, ?_⟩
  have h3 := c1_scale x q c v lam hlam (fun j => rfl)
  have e : Real.log (∑ j, mix N Γ θ j * Real.exp (c j)) = Real.log (max
      (∑ j, qL N Γ j * Real.exp (c j)) (∑ j, qR N Γ j * Real.exp (c j))) := by
    simp only at hθeq
    rw [hθeq]
  have : lam * (∑ j, c j * q j - relEntropy q (mix N Γ θ)) = lam * Real.log (max
      (∑ j, qL N Γ j * Real.exp (c j)) (∑ j, qR N Γ j * Real.exp (c j))) := by
    rw [← e, hqeq]
  rw [mul_sub, h3] at this
  exact this

theorem inner_isGreatest {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (v : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    IsGreatest {s | ∃ (θ : Fin d → ℝ) (q : Fin d → Fin (N + 2) → ℝ),
        (∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ i, q i ∈ stdSimplex ℝ (Fin (N + 2))) ∧
        (∀ i, AbsCont (q i) (mix N Γ (θ i))) ∧
        s = ∑ i, v i * ∑ j, uhat i j * q i j - lam * ∑ i, relEntropy (q i) (mix N Γ (θ i))}
      (lam * ∑ i, Real.log (max
        (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
        (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam)))) := by
  constructor
  · have H := fun i => c1_coord_attain (uhat i) Γ hN hΓ0 hΓ1 (v i) lam hlam
    choose θ hθ q hq hac heq using H
    refine ⟨θ, q, hθ, hq, hac, ?_⟩
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => (heq i).symm)
  · rintro s ⟨θ, q, hθ, hq, hac, rfl⟩
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact c1_coord_bound (uhat i) Γ hN hΓ0 hΓ1 (v i) lam hlam (θ i) (hθ i) (q i) (hq i) (hac i)

end DataDrivenRO.KS

namespace DataDrivenRO.KS

lemma c3_term_lb {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * Real.log (a / b) := by
  have h := Real.self_sub_one_le_mul_log (x := a / b) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h hb.le
  have e1 : b * (a / b - 1) = a - b := by field_simp
  have e2 : b * (a / b * Real.log (a / b)) = a * Real.log (a / b) := by field_simp
  rw [e1, e2] at h2
  exact h2

lemma c3_term_split {q c : ℝ} (hq : 0 ≤ q) (hc : 0 < c) :
    q * Real.log (q / c) = q * Real.log q - q * Real.log c := by
  rcases hq.eq_or_lt with rfl | hq0
  · simp
  · rw [Real.log_div hq0.ne' hc.ne']; ring

lemma c3_term_mono {q p δ : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hδ : 0 < δ) (h : 0 < q → 0 < p) :
    q * Real.log (q / (p + δ)) ≤ q * Real.log (q / p) := by
  rcases hq.eq_or_lt with rfl | hq0
  · simp
  · have hp0 := h hq0
    apply mul_le_mul_of_nonneg_left _ hq
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hq hp0 (by linarith)

lemma c3_term_cont {X : Type*} [TopologicalSpace X] {q p : X → ℝ} (hq : Continuous q)
    (hp : Continuous p) (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ x, 0 ≤ p x) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun x => q x * Real.log (q x / (p x + δ)) := by
  have hc : ∀ x, 0 < p x + δ := fun x => by have := hp0 x; linarith
  have h1 : Continuous fun x => q x * Real.log (q x) - q x * Real.log (p x + δ) :=
    (Real.continuous_mul_log.comp hq).sub (hq.mul ((hp.add continuous_const).log (fun x => (hc x).ne')))
  refine h1.congr ?_
  intro x
  exact (c3_term_split (hq0 x) (hc x)).symm

lemma c3_term_tendsto {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (h : 0 < q → 0 < p) :
    Filter.Tendsto (fun δ : ℝ => q * Real.log (q / (p + δ))) (nhds 0) (nhds (q * Real.log (q / p))) := by
  rcases hq.eq_or_lt with rfl | hq0
  · simp
  · have hp0 := h hq0
    have hcont : ContinuousAt (fun δ : ℝ => q * Real.log (q / (p + δ))) 0 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log
      · exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; exact hp0.ne')
      · simp; exact ⟨hq0.ne', hp0.ne'⟩
    have := hcont.tendsto
    simpa using this

theorem c3_closed {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] (q p : X → ι → ℝ)
    (hq : ∀ k, Continuous fun x => q x k) (hp : ∀ k, Continuous fun x => p x k)
    (hq0 : ∀ x k, 0 ≤ q x k) (hp0 : ∀ x k, 0 ≤ p x k) (hp1 : ∀ x k, p x k ≤ 1) (L : ℝ) :
    IsClosed {x | (∀ k, 0 < q x k → 0 < p x k) ∧
      ∑ k, q x k * Real.log (q x k / p x k) ≤ L} := by
  have hS : {x | (∀ k, 0 < q x k → 0 < p x k) ∧
      ∑ k, q x k * Real.log (q x k / p x k) ≤ L} =
      ⋂ δ : {δ : ℝ // 0 < δ}, {x | ∑ k, q x k * Real.log (q x k / (p x k + δ)) ≤ L} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
    constructor
    · rintro ⟨hac, hD⟩ δ hδ
      exact le_trans (Finset.sum_le_sum fun k _ =>
        c3_term_mono (hq0 x k) (hp0 x k) hδ (hac k)) hD
    · intro h
      have hac : ∀ k, 0 < q x k → 0 < p x k := by
        intro k0 hk0
        by_contra hpk
        have hp00 : p x k0 = 0 := le_antisymm (not_lt.1 hpk) (hp0 x k0)
        set K0 : ℝ := |L| + 2 * (Fintype.card ι : ℝ) + 1 with hK0
        have hK0pos : 0 < K0 := by
          have := abs_nonneg L
          have : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
          linarith
        set a0 := q x k0 with ha0
        set δ0 := a0 * Real.exp (-K0 / a0) with hδ0def
        have hδ0 : 0 < δ0 := by positivity
        set δ := min 1 δ0 with hδdef
        have hδpos : 0 < δ := lt_min one_pos hδ0
        have hδ1 : δ ≤ 1 := min_le_left _ _
        have hδ2 : δ ≤ δ0 := min_le_right _ _
        have hge := h δ hδpos
        have hall : ∀ k, q x k - (p x k + δ) ≤ q x k * Real.log (q x k / (p x k + δ)) :=
          fun k => c3_term_lb (hq0 x k) (by have := hp0 x k; linarith)
        have hsum := Finset.add_sum_erase Finset.univ
          (fun k => q x k * Real.log (q x k / (p x k + δ))) (Finset.mem_univ k0)
        have hrest : ∑ k ∈ Finset.univ.erase k0, (-2 : ℝ) ≤
            ∑ k ∈ Finset.univ.erase k0, q x k * Real.log (q x k / (p x k + δ)) := by
          apply Finset.sum_le_sum
          intro k _
          have := hall k
          have := hq0 x k
          have := hp1 x k
          linarith
        have hcard : ∑ k ∈ Finset.univ.erase k0, (-2 : ℝ) ≥ -(2 * (Fintype.card ι : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have : ((Finset.univ.erase k0).card : ℝ) ≤ Fintype.card ι := by
            exact_mod_cast (Finset.card_erase_le).trans (by simp)
          linarith
        have hmain : K0 ≤ a0 * Real.log (a0 / (p x k0 + δ)) := by
          rw [hp00, zero_add]
          have h1 : Real.exp (K0 / a0) ≤ a0 / δ := by
            have : a0 / δ0 = Real.exp (K0 / a0) := by
              have e : Real.exp (-K0 / a0) * Real.exp (K0 / a0) = 1 := by
                rw [← Real.exp_add]
                have : -K0 / a0 + K0 / a0 = 0 := by ring
                rw [this]; simp
              rw [hδ0def, div_eq_iff (by positivity)]
              calc a0 = a0 * (Real.exp (-K0 / a0) * Real.exp (K0 / a0)) := by rw [e, mul_one]
                _ = _ := by ring
            rw [← this]
            exact div_le_div_of_nonneg_left hk0.le hδpos hδ2
          have h2 : K0 / a0 ≤ Real.log (a0 / δ) := by
            have := Real.log_le_log (Real.exp_pos _) h1
            rwa [Real.log_exp] at this
          calc K0 = a0 * (K0 / a0) := by field_simp
            _ ≤ a0 * Real.log (a0 / δ) := mul_le_mul_of_nonneg_left h2 hk0.le
        have hcardnn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
        have habs := le_abs_self L
        linarith
      refine ⟨hac, ?_⟩
      have htend : Filter.Tendsto
          (fun δ : ℝ => ∑ k, q x k * Real.log (q x k / (p x k + δ))) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∑ k, q x k * Real.log (q x k / p x k))) := by
        have : Filter.Tendsto
            (fun δ : ℝ => ∑ k, q x k * Real.log (q x k / (p x k + δ))) (nhds 0)
            (nhds (∑ k, q x k * Real.log (q x k / p x k))) :=
          tendsto_finset_sum _ (fun k _ => c3_term_tendsto (hq0 x k) (hp0 x k) (hac k))
        exact this.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun δ hδ => h δ hδ)
  rw [hS]
  refine isClosed_iInter fun δ => isClosed_le ?_ continuous_const
  exact continuous_finset_sum _ (fun k _ =>
    c3_term_cont (hq k) (hp k) (fun x => hq0 x k) (fun x => hp0 x k) δ.2)

end DataDrivenRO.KS

namespace DataDrivenRO.KS

lemma mix_continuous (N : ℕ) (Γ : ℝ) (j : Fin (N + 2)) : Continuous fun θ : ℝ => mix N Γ θ j := by
  unfold mix; fun_prop

lemma mix_le_one (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (j : Fin (N + 2)) : mix N Γ θ j ≤ 1 := by
  have hm := mix_mem_simplex N hN Γ hΓ0 hΓ1 hθ
  calc mix N Γ θ j ≤ ∑ k, mix N Γ θ k :=
        Finset.single_le_sum (fun k _ => hm.1 k) (Finset.mem_univ j)
    _ = 1 := hm.2

theorem UI_isCompact {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (ε : ℝ) :
    IsCompact (UI uhat Γ ε) := by
  set Dom : Set ((Fin d → ℝ) × (Fin d → Fin (N + 2) → ℝ)) :=
    (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) ×ˢ
      (Set.pi Set.univ fun _ => stdSimplex ℝ (Fin (N + 2))) with hDom
  have hDomc : IsCompact Dom :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_stdSimplex ℝ (Fin (N + 2)))
  haveI : CompactSpace Dom := isCompact_iff_compactSpace.1 hDomc
  have hmem : ∀ x : Dom, (∀ i, x.1.1 i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ i, x.1.2 i ∈ stdSimplex ℝ (Fin (N + 2)) := by
    intro x
    have := x.2
    simp only [hDom, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies] at this
    exact this
  let q : Dom → (Fin d × Fin (N + 2)) → ℝ := fun x k => x.1.2 k.1 k.2
  let p : Dom → (Fin d × Fin (N + 2)) → ℝ := fun x k => mix N Γ (x.1.1 k.1) k.2
  have hq : ∀ k, Continuous fun x => q x k := by
    intro k
    exact ((continuous_apply k.2).comp ((continuous_apply k.1).comp
      (continuous_snd.comp continuous_subtype_val)))
  have hp : ∀ k, Continuous fun x => p x k := by
    intro k
    exact (mix_continuous N Γ k.2).comp ((continuous_apply k.1).comp
      (continuous_fst.comp continuous_subtype_val))
  have hq0 : ∀ x k, 0 ≤ q x k := fun x k => (hmem x).2 k.1 |>.1 k.2
  have hp0 : ∀ x k, 0 ≤ p x k := fun x k => mix_nonneg N hN Γ hΓ0 hΓ1 ((hmem x).1 k.1) k.2
  have hp1 : ∀ x k, p x k ≤ 1 := fun x k => mix_le_one N hN Γ hΓ0 hΓ1 ((hmem x).1 k.1) k.2
  have hK := c3_closed q p hq hp hq0 hp0 hp1 (Real.log (1 / ε))
  have hKc : IsCompact {x : Dom | (∀ k, 0 < q x k → 0 < p x k) ∧
      ∑ k, q x k * Real.log (q x k / p x k) ≤ Real.log (1 / ε)} := hK.isCompact
  let f : Dom → (Fin d → ℝ) := fun x i => ∑ j, uhat i j * x.1.2 i j
  have hf : Continuous f := by
    apply continuous_pi; intro i
    apply continuous_finset_sum; intro j _
    exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_snd.comp continuous_subtype_val)))
  have heq : UI uhat Γ ε = f '' {x : Dom | (∀ k, 0 < q x k → 0 < p x k) ∧
      ∑ k, q x k * Real.log (q x k / p x k) ≤ Real.log (1 / ε)} := by
    ext u
    constructor
    · rintro ⟨θ, q', hθ, hq', hu, hac, hD⟩
      have hxD : (θ, q') ∈ Dom := by
        simp only [hDom, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
        exact ⟨hθ, hq'⟩
      refine ⟨⟨(θ, q'), hxD⟩, ⟨?_, ?_⟩, ?_⟩
      · intro k hk
        exact hac k.1 k.2 hk
      · rw [Fintype.sum_prod_type]
        exact hD
      · funext i; exact hu i
    · rintro ⟨x, ⟨hac, hD⟩, rfl⟩
      refine ⟨x.1.1, x.1.2, (hmem x).1, (hmem x).2, fun i => rfl, ?_, ?_⟩
      · intro i j hj
        exact hac (i, j) hj
      · rw [Fintype.sum_prod_type] at hD
        exact hD
  rw [heq]
  exact hKc.image hf

end DataDrivenRO.KS

namespace DataDrivenRO.KS

lemma lag_abstract {X : Type*} (F : Set X) (dd ww : X → ℝ) (r0 G : ℝ) (x0 : X)
    (hx0 : x0 ∈ F) (hd0 : dd x0 < r0)
    (hconv : ∀ x ∈ F, ∀ y ∈ F, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
      ∃ z ∈ F, dd z ≤ s * dd x + t * dd y ∧ ww z = s * ww x + t * ww y)
    (hG : ∀ x ∈ F, dd x ≤ r0 → ww x ≤ G) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ x ∈ F, ww x - lam * dd x ≤ G - lam * r0 := by
  -- cross inequality
  have cross : ∀ x ∈ F, r0 < dd x → ∀ y ∈ F, dd y < r0 →
      (ww x - G) / (dd x - r0) ≤ (G - ww y) / (r0 - dd y) := by
    intro x hx hxd y hy hyd
    have ha : 0 < dd x - r0 := by linarith
    have hb : 0 < r0 - dd y := by linarith
    have hab : 0 < (dd x - r0) + (r0 - dd y) := by linarith
    obtain ⟨a, ha_def⟩ : ∃ a, a = dd x - r0 := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b, b = r0 - dd y := ⟨_, rfl⟩
    rw [← ha_def] at ha hab ⊢
    rw [← hb_def] at hb hab ⊢
    obtain ⟨z, hz, hzd, hzw⟩ := hconv x hx y hy (b / (a + b)) (a / (a + b))
      (by positivity) (by positivity)
      (by rw [← add_div, add_comm b a, div_self hab.ne'])
    have hzG : ww z ≤ G := hG z hz (by
      have e : b / (a + b) * dd x + a / (a + b) * dd y = r0 := by
        have hx' : dd x = r0 + a := by linarith
        have hy' : dd y = r0 - b := by linarith
        rw [hx', hy']; field_simp; ring
      linarith)
    rw [hzw] at hzG
    rw [div_le_div_iff₀ ha hb]
    have h1 : b / (a + b) * ww x + a / (a + b) * ww y ≤ G := hzG
    have h2 : b * ww x + a * ww y ≤ (a + b) * G := by
      have := mul_le_mul_of_nonneg_left h1 hab.le
      have e : (a + b) * (b / (a + b) * ww x + a / (a + b) * ww y) = b * ww x + a * ww y := by
        field_simp
      linarith
    nlinarith
  set P : Set ℝ := {0} ∪ {c | ∃ x ∈ F, r0 < dd x ∧ c = (ww x - G) / (dd x - r0)} with hP
  have hy0 : 0 ≤ (G - ww x0) / (r0 - dd x0) := by
    apply div_nonneg
    · have := hG x0 hx0 hd0.le; linarith
    · linarith
  have hbdd : ∀ y ∈ F, dd y < r0 → ∀ c ∈ P, c ≤ (G - ww y) / (r0 - dd y) := by
    intro y hy hyd c hc
    rcases hc with hc | ⟨x, hx, hxd, rfl⟩
    · simp only [Set.mem_singleton_iff] at hc
      rw [hc]
      apply div_nonneg
      · have := hG y hy hyd.le; linarith
      · linarith
    · exact cross x hx hxd y hy hyd
  have hne : P.Nonempty := ⟨0, Or.inl rfl⟩
  have hbd : BddAbove P := ⟨_, fun c hc => hbdd x0 hx0 hd0 c hc⟩
  refine ⟨sSup P, le_csSup hbd (Or.inl rfl), ?_⟩
  intro x hx
  rcases lt_trichotomy (dd x) r0 with h | h | h
  · have hle : sSup P ≤ (G - ww x) / (r0 - dd x) := csSup_le hne (fun c hc => hbdd x hx h c hc)
    have hpos : 0 < r0 - dd x := by linarith
    rw [le_div_iff₀ hpos] at hle
    nlinarith
  · have := hG x hx h.le
    rw [h]; linarith
  · have hmem : (ww x - G) / (dd x - r0) ∈ P := Or.inr ⟨x, hx, h, rfl⟩
    have hle := le_csSup hbd hmem
    have hpos : 0 < dd x - r0 := by linarith
    rw [div_le_iff₀ hpos] at hle
    nlinarith

lemma relEntropy_nonneg {n : ℕ} (q p : Fin n → ℝ) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hac : AbsCont q p) : 0 ≤ relEntropy q p := by
  have h : ∀ j, q j - p j ≤ q j * Real.log (q j / p j) := by
    intro j
    rcases (hq.1 j).eq_or_lt with h0 | h0
    · rw [← h0]; simp only [zero_mul, zero_sub, neg_nonpos]; exact hp.1 j
    · exact c3_term_lb (hq.1 j) (hac j h0)
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
  rw [Finset.sum_sub_distrib, hq.2, hp.2] at this
  unfold relEntropy
  linarith

lemma relEntropy_self {n : ℕ} (p : Fin n → ℝ) : relEntropy p p = 0 := by
  unfold relEntropy
  apply Finset.sum_eq_zero
  intro j _
  rcases eq_or_ne (p j) 0 with h | h
  · rw [h]; simp
  · rw [div_self h, Real.log_one, mul_zero]

theorem strong_duality {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    IsGLB (boundKS uhat Γ ε v '' Set.Ioi 0)
      (RobustMDP.Shared.supportFunction (UI uhat Γ ε) v) := by
  have hr0pos : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    rw [one_div]; exact one_lt_inv₀ hε0 |>.2 hε1
  set r0 := Real.log (1 / ε) with hr0
  let F : Set ((Fin d → ℝ) × (Fin d → Fin (N + 2) → ℝ)) :=
    {x | (∀ i, x.1 i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, x.2 i ∈ stdSimplex ℝ (Fin (N + 2))) ∧
      ∀ i, AbsCont (x.2 i) (mix N Γ (x.1 i))}
  let dd : (Fin d → ℝ) × (Fin d → Fin (N + 2) → ℝ) → ℝ :=
    fun x => ∑ i, relEntropy (x.2 i) (mix N Γ (x.1 i))
  let ww : (Fin d → ℝ) × (Fin d → Fin (N + 2) → ℝ) → ℝ :=
    fun x => ∑ i, v i * ∑ j, uhat i j * x.2 i j
  have hdd0 : ∀ x ∈ F, 0 ≤ dd x := by
    intro x hx
    exact Finset.sum_nonneg (fun i _ => relEntropy_nonneg _ _ (hx.2.1 i)
      (mix_mem_simplex N hN Γ hΓ0 hΓ1 (hx.1 i)) (hx.2.2 i))
  have hconv : ∀ x ∈ F, ∀ y ∈ F, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
      ∃ z ∈ F, dd z ≤ s * dd x + t * dd y ∧ ww z = s * ww x + t * ww y := by
    intro x hx y hy s t hs ht hst
    refine ⟨(fun i => s * x.1 i + t * y.1 i, fun i j => s * x.2 i j + t * y.2 i j), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine ⟨by have := (hx.1 i).1; have := (hy.1 i).1; positivity, ?_⟩
      have := (hx.1 i).2; have := (hy.1 i).2
      nlinarith
    · intro i
      exact (convex_stdSimplex ℝ (Fin (N + 2))) (hx.2.1 i) (hy.2.1 i) hs ht hst
    · intro i
      have hmix : mix N Γ (s * x.1 i + t * y.1 i) =
          fun j => s * mix N Γ (x.1 i) j + t * mix N Γ (y.1 i) j := by
        funext j; exact mix_comb N Γ _ _ s t hst j
      show AbsCont (fun j => s * x.2 i j + t * y.2 i j) (mix N Γ (s * x.1 i + t * y.1 i))
      rw [hmix]
      exact absCont_comb hs ht _ _ _ _ (fun j => (hx.2.1 i).1 j) (fun j => (hy.2.1 i).1 j)
        (mix_nonneg N hN Γ hΓ0 hΓ1 (hx.1 i)) (mix_nonneg N hN Γ hΓ0 hΓ1 (hy.1 i))
        (hx.2.2 i) (hy.2.2 i)
    · have hle : ∀ i, relEntropy (fun j => s * x.2 i j + t * y.2 i j)
          (mix N Γ (s * x.1 i + t * y.1 i))
          ≤ s * relEntropy (x.2 i) (mix N Γ (x.1 i)) + t * relEntropy (y.2 i) (mix N Γ (y.1 i)) := by
        intro i
        have hmix : mix N Γ (s * x.1 i + t * y.1 i) =
            fun j => s * mix N Γ (x.1 i) j + t * mix N Γ (y.1 i) j := by
          funext j; exact mix_comb N Γ _ _ s t hst j
        rw [hmix]
        exact relEntropy_comb hs ht _ _ _ _ (fun j => (hx.2.1 i).1 j) (fun j => (hy.2.1 i).1 j)
          (mix_nonneg N hN Γ hΓ0 hΓ1 (hx.1 i)) (mix_nonneg N hN Γ hΓ0 hΓ1 (hy.1 i))
          (hx.2.2 i) (hy.2.2 i)
      show ∑ i, relEntropy (fun j => s * x.2 i j + t * y.2 i j) (mix N Γ (s * x.1 i + t * y.1 i))
        ≤ s * dd x + t * dd y
      calc _ ≤ ∑ i, (s * relEntropy (x.2 i) (mix N Γ (x.1 i)) +
            t * relEntropy (y.2 i) (mix N Γ (y.1 i))) := Finset.sum_le_sum (fun i _ => hle i)
        _ = s * dd x + t * dd y := by
          show _ = s * ∑ i, relEntropy (x.2 i) (mix N Γ (x.1 i)) + t * ∑ i, relEntropy (y.2 i) (mix N Γ (y.1 i))
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    · show ∑ i, v i * ∑ j, uhat i j * (s * x.2 i j + t * y.2 i j) = s * ww x + t * ww y
      show _ = s * ∑ i, v i * ∑ j, uhat i j * x.2 i j + t * ∑ i, v i * ∑ j, uhat i j * y.2 i j
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      have : ∑ j, uhat i j * (s * x.2 i j + t * y.2 i j) =
          s * ∑ j, uhat i j * x.2 i j + t * ∑ j, uhat i j * y.2 i j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this]; ring
  -- Slater point
  have hx0 : ((fun _ => 0), (fun _ => mix N Γ 0)) ∈ F := by
    refine ⟨fun i => ⟨le_refl _, zero_le_one⟩, fun i => ?_, fun i => fun j hj => hj⟩
    exact mix_mem_simplex N hN Γ hΓ0 hΓ1 ⟨le_refl _, zero_le_one⟩
  have hd0 : dd ((fun _ => 0), (fun _ => mix N Γ 0)) < r0 := by
    show ∑ i, relEntropy (mix N Γ 0) (mix N Γ 0) < r0
    simp only [relEntropy_self, Finset.sum_const_zero]
    exact hr0pos
  -- the support function is sSup of ww on S
  set S : Set ((Fin d → ℝ) × (Fin d → Fin (N + 2) → ℝ)) := {x | x ∈ F ∧ dd x ≤ r0} with hS
  have himg : (fun p : Fin d → ℝ => ∑ j, p j * v j) '' UI uhat Γ ε = ww '' S := by
    ext s
    constructor
    · rintro ⟨u, ⟨θ, q, hθ, hq, hu, hac, hD⟩, rfl⟩
      refine ⟨(θ, q), ⟨⟨hθ, hq, hac⟩, hD⟩, ?_⟩
      show ∑ i, v i * ∑ j, uhat i j * q i j = ∑ j, u j * v j
      apply Finset.sum_congr rfl; intro i _
      rw [hu i, mul_comm]
    · rintro ⟨x, ⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
      refine ⟨fun i => ∑ j, uhat i j * x.2 i j, ⟨x.1, x.2, h1, h2, fun i => rfl, h3, h4⟩, ?_⟩
      show ∑ i, (∑ j, uhat i j * x.2 i j) * v i = ∑ i, v i * ∑ j, uhat i j * x.2 i j
      apply Finset.sum_congr rfl; intro i _; rw [mul_comm]
  have hσ : RobustMDP.Shared.supportFunction (UI uhat Γ ε) v = sSup (ww '' S) := by
    unfold RobustMDP.Shared.supportFunction
    rw [himg]
  rw [hσ]
  have hSne : (ww '' S).Nonempty := ⟨ww _, _, ⟨hx0, hd0.le⟩, rfl⟩
  -- weak duality
  have hweak : ∀ lam, 0 < lam → ∀ x ∈ S, ww x ≤ boundKS uhat Γ ε v lam := by
    intro lam hlam x hx
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
    have := (inner_isGreatest uhat Γ hN hΓ0 hΓ1 v lam hlam).2 ⟨x.1, x.2, h1, h2, h3, rfl⟩
    have h5 : lam * dd x ≤ lam * r0 := mul_le_mul_of_nonneg_left h4 hlam.le
    unfold boundKS
    have h6 : ww x - lam * dd x ≤ lam * ∑ i, Real.log (max
        (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
        (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam))) := this
    linarith
  have hlb : ∀ lam, 0 < lam → sSup (ww '' S) ≤ boundKS uhat Γ ε v lam := by
    intro lam hlam
    apply csSup_le hSne
    rintro _ ⟨x, hx, rfl⟩
    exact hweak lam hlam x hx
  have hbdd : BddAbove (ww '' S) := ⟨boundKS uhat Γ ε v 1, by
    rintro _ ⟨x, hx, rfl⟩; exact hweak 1 one_pos x hx⟩
  have hG : ∀ x ∈ F, dd x ≤ r0 → ww x ≤ sSup (ww '' S) :=
    fun x hx hd => le_csSup hbdd ⟨x, ⟨hx, hd⟩, rfl⟩
  obtain ⟨ls, hls0, hls⟩ := lag_abstract F dd ww r0 (sSup (ww '' S)) _ hx0 hd0 hconv hG
  constructor
  · rintro _ ⟨lam, hlam, rfl⟩
    exact hlb lam hlam
  · intro m hm
    have hm' : ∀ lam, 0 < lam → m ≤ boundKS uhat Γ ε v lam := fun lam hlam => hm ⟨lam, hlam, rfl⟩
    rcases hls0.eq_or_lt with h0 | hpos
    · -- ls = 0
      rw [← h0] at hls
      have hall : ∀ x ∈ F, ww x ≤ sSup (ww '' S) := by
        intro x hx; have := hls x hx; linarith
      by_contra hcon
      push Not at hcon
      set G := sSup (ww '' S)
      set lam : ℝ := (m - G) / (2 * r0) with hlam
      have hlampos : 0 < lam := by positivity
      obtain ⟨θ, q, hθ, hq, hac, heq⟩ := (inner_isGreatest uhat Γ hN hΓ0 hΓ1 v lam hlampos).1
      have hxF : (θ, q) ∈ F := ⟨hθ, hq, hac⟩
      have h1 := hall _ hxF
      have h2 := hdd0 _ hxF
      have h3 : lam * dd (θ, q) ≥ 0 := mul_nonneg hlampos.le h2
      have h4 := hm' lam hlampos
      unfold boundKS at h4
      have h5 : lam * ∑ i, Real.log (max
        (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
        (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam))) = ww (θ, q) - lam * dd (θ, q) := heq
      have h6 : lam * r0 = (m - G) / 2 := by
        rw [hlam]; field_simp
      linarith
    · obtain ⟨θ, q, hθ, hq, hac, heq⟩ := (inner_isGreatest uhat Γ hN hΓ0 hΓ1 v ls hpos).1
      have hxF : (θ, q) ∈ F := ⟨hθ, hq, hac⟩
      have h1 := hls _ hxF
      have h4 := hm' ls hpos
      unfold boundKS at h4
      have h5 : ls * ∑ i, Real.log (max
        (∑ j, qL N Γ j * Real.exp (v i * uhat i j / ls))
        (∑ j, qR N Γ j * Real.exp (v i * uhat i j / ls))) = ww (θ, q) - ls * dd (θ, q) := heq
      linarith

end DataDrivenRO.KS

namespace DataDrivenRO.KS


noncomputable def qLn (N : ℕ) (Γ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then Γ
  else if j ≤ ⌊(N : ℝ) * (1 - Γ)⌋₊ then 1 / N
  else if j = ⌊(N : ℝ) * (1 - Γ)⌋₊ + 1 then 1 - Γ - (⌊(N : ℝ) * (1 - Γ)⌋₊ : ℝ) / N
  else 0

lemma qL_eq_qLn (N : ℕ) (Γ : ℝ) (j : Fin (N + 2)) : qL N Γ j = qLn N Γ (j : ℕ) := rfl

lemma qLn_partial (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), qLn N Γ j = min (Γ + (n : ℝ) / N) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set m := ⌊(N : ℝ) * (1 - Γ)⌋₊ with hm
  have hm1 : (m : ℝ) ≤ N * (1 - Γ) := Nat.floor_le (by nlinarith)
  have hm2 : (N : ℝ) * (1 - Γ) < m + 1 := Nat.lt_floor_add_one _
  -- facts: k ≤ m → k/N ≤ 1 - Γ ; k ≥ m+1 → k/N > 1 - Γ
  have hle : ∀ k : ℕ, k ≤ m → Γ + (k : ℝ) / N ≤ 1 := by
    intro k hk
    have : (k : ℝ) ≤ m := by exact_mod_cast hk
    have : (k : ℝ) / N ≤ 1 - Γ := by rw [div_le_iff₀ hNr]; linarith
    linarith
  have hgt : ∀ k : ℕ, m + 1 ≤ k → 1 < Γ + (k : ℝ) / N := by
    intro k hk
    have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have : 1 - Γ < (k : ℝ) / N := by rw [lt_div_iff₀ hNr]; linarith
    linarith
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, qLn, if_true, Nat.cast_zero,
      zero_div, add_zero]
    rw [min_eq_left hΓ1.le]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h1 : n + 1 ≤ m
    · have hq : qLn N Γ (n + 1) = 1 / N := by
        simp only [qLn]; rw [if_neg (by omega), if_pos h1]
      rw [hq, min_eq_left (hle n (by omega)), min_eq_left (hle (n + 1) h1)]
      push_cast; ring
    · by_cases h2 : n + 1 = m + 1
      · have hq : qLn N Γ (n + 1) = 1 - Γ - (m : ℝ) / N := by
          simp only [qLn]; rw [if_neg (by omega), if_neg h1, if_pos h2]
        have hnm : (n : ℝ) = m := by
          have : n = m := by omega
          rw [this]
        rw [hq, min_eq_left (hle n (by omega)), min_eq_right (hgt (n + 1) (by omega)).le, hnm]
        ring
      · have hq : qLn N Γ (n + 1) = 0 := by
          simp only [qLn]; rw [if_neg (by omega), if_neg h1, if_neg h2]
        rw [hq, min_eq_right (hgt n (by omega)).le, min_eq_right (hgt (n + 1) (by omega)).le]
        ring

lemma abel_sum (p w : ℕ → ℝ) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), p j * w j =
      w M * ∑ j ∈ Finset.range (M + 1), p j
        - ∑ k ∈ Finset.range M, (w (k + 1) - w k) * ∑ j ∈ Finset.range (k + 1), p j := by
  induction M with
  | zero => simp [mul_comm]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (w (k + 1) - w k) *
      ∑ j ∈ Finset.range (k + 1), p j) M, Finset.sum_range_succ p (M + 1)]
    ring

lemma abel_qL (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (w : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N + 2), qLn N Γ j * w j =
      w (N + 1) + ∑ k ∈ Finset.range (N + 1), (w k - w (k + 1)) * min (Γ + (k : ℝ) / N) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have := abel_sum (qLn N Γ) w (N + 1)
  simp only [qLn_partial N hN Γ hΓ0 hΓ1] at this
  rw [show N + 1 + 1 = N + 2 from rfl] at this
  rw [this]
  have hone : min (Γ + ((N + 1 : ℕ) : ℝ) / N) 1 = 1 := by
    apply min_eq_right
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / N := by
      rw [le_div_iff₀ hNr]; push_cast; linarith
    linarith
  rw [hone, mul_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro k _; ring



lemma pw_anti (u : ℕ → ℝ) (hu : Monotone u) (g : ℝ → ℝ) (hg : Antitone g) :
    ∀ (M : ℕ) (x : ℝ), u 0 ≤ x → x ≤ u M →
      g x ≤ g (u M) + ∑ k ∈ Finset.range M,
        (g (u k) - g (u (k + 1))) * (if x < u (k + 1) then (1 : ℝ) else 0) := by
  intro M
  induction M with
  | zero =>
    intro x h0 h1
    have : x = u 0 := le_antisymm h1 h0
    simp [this]
  | succ M ih =>
    intro x h0 h1
    rw [Finset.sum_range_succ]
    by_cases hx : u M < x
    · have hz : ∀ k ∈ Finset.range M, (g (u k) - g (u (k + 1))) *
          (if x < u (k + 1) then (1 : ℝ) else 0) = 0 := by
        intro k hk
        have : u (k + 1) ≤ u M := hu (by simpa using hk)
        rw [if_neg (by linarith), mul_zero]
      rw [Finset.sum_eq_zero hz, zero_add]
      by_cases hlt : x < u (M + 1)
      · rw [if_pos hlt, mul_one]
        have := hg hx.le
        linarith
      · rw [if_neg hlt, mul_zero, add_zero]
        have : x = u (M + 1) := le_antisymm h1 (not_lt.1 hlt)
        rw [this]
    · have hxM : x ≤ u M := not_lt.1 hx
      have ih' := ih x h0 hxM
      by_cases hlt : x < u (M + 1)
      · rw [if_pos hlt, mul_one]
        linarith
      · have hle : u (M + 1) ≤ x := not_lt.1 hlt
        have heq : u M = u (M + 1) := le_antisymm (hu (Nat.le_succ M)) (le_trans hle hxM)
        rw [if_neg hlt, mul_zero, add_zero, ← heq]
        linarith

lemma pw_mono (u : ℕ → ℝ) (hu : Monotone u) (g : ℝ → ℝ) (hg : Monotone g) :
    ∀ (M : ℕ) (x : ℝ), u 0 ≤ x → x ≤ u M →
      g x ≤ g (u 0) + ∑ k ∈ Finset.range M,
        (g (u (k + 1)) - g (u k)) * (if u k < x then (1 : ℝ) else 0) := by
  intro M
  induction M with
  | zero =>
    intro x h0 h1
    have : x = u 0 := le_antisymm h1 h0
    simp [this]
  | succ M ih =>
    intro x h0 h1
    rw [Finset.sum_range_succ]
    by_cases hx : u M < x
    · have hall : ∀ k ∈ Finset.range (M + 1), (g (u (k + 1)) - g (u k)) *
          (if u k < x then (1 : ℝ) else 0) = g (u (k + 1)) - g (u k) := by
        intro k hk
        have : u k ≤ u M := hu (by simpa [Nat.lt_succ_iff] using hk)
        rw [if_pos (by linarith), mul_one]
      have hs := Finset.sum_congr rfl hall
      rw [Finset.sum_range_succ] at hs
      rw [hs, Finset.sum_range_sub (fun k => g (u k))]
      · have := hg h1
        linarith
    · have hxM : x ≤ u M := not_lt.1 hx
      have ih' := ih x h0 hxM
      rw [if_neg hx, mul_zero, add_zero]
      exact ih'



lemma int_le_step {Q : Measure ℝ} [IsProbabilityMeasure Q] (g : ℝ → ℝ) (hgm : Measurable g)
    (a b C : ℝ) (hsupp : Q (Set.Icc a b)ᶜ = 0) (hbd : ∀ x ∈ Set.Icc a b, |g x| ≤ C)
    (c : ℝ) (s : ℕ → Set ℝ) (hs : ∀ k, MeasurableSet (s k)) (coef : ℕ → ℝ) (M : ℕ)
    (hle : ∀ x ∈ Set.Icc a b, g x ≤ c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) :
    ∫ x, g x ∂Q ≤ c + ∑ k ∈ Finset.range M, coef k * Q.real (s k) := by
  have hae : ∀ᵐ x ∂Q, x ∈ Set.Icc a b := mem_ae_iff.mpr hsupp
  have hint : Integrable g Q := by
    refine Integrable.of_bound hgm.aestronglyMeasurable C ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]; exact hbd x hx
  have hind : ∀ k, Integrable (fun x => coef k * (s k).indicator (1 : ℝ → ℝ) x) Q := by
    intro k
    have : Integrable ((s k).indicator (1 : ℝ → ℝ)) Q :=
      (integrable_const (1 : ℝ)).indicator (hs k)
    exact this.const_mul _
  have hrint : Integrable (fun x => c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) Q :=
    (integrable_const c).add (integrable_finset_sum _ (fun k _ => hind k))
  have h1 : ∫ x, g x ∂Q ≤ ∫ x, (c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) ∂Q := by
    apply integral_mono_ae hint hrint
    filter_upwards [hae] with x hx
    exact hle x hx
  have h2 : ∫ x, (c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) ∂Q
      = c + ∑ k ∈ Finset.range M, coef k * Q.real (s k) := by
    rw [integral_add (integrable_const c) (integrable_finset_sum _ (fun k _ => hind k))]
    rw [integral_finset_sum _ (fun k _ => hind k)]
    simp only [integral_const, probReal_univ, one_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, integral_indicator_one (hs k)]
  linarith


noncomputable def uSeq {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (i : Fin d) (k : ℕ) : ℝ :=
  uhat i ⟨min k (N + 1), by omega⟩

lemma uSeq_of_lt {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (i : Fin d) {k : ℕ} (hk : k < N + 2) :
    uSeq uhat i k = uhat i ⟨k, hk⟩ := by
  unfold uSeq
  congr 1
  apply Fin.ext
  simp only
  omega

lemma uSeq_mono {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (hmono : ∀ i, Monotone (uhat i))
    (i : Fin d) : Monotone (uSeq uhat i) := by
  intro a b hab
  exact hmono i (Fin.mk_le_mk.2 (min_le_min_right _ hab))

lemma ind_Iio (a x : ℝ) : (Set.Iio a).indicator (1 : ℝ → ℝ) x = if x < a then 1 else 0 := by
  simp [Set.indicator_apply]

lemma ind_Ioi (a x : ℝ) : (Set.Ioi a).indicator (1 : ℝ → ℝ) x = if a < x then 1 else 0 := by
  simp [Set.indicator_apply]

lemma real_Iio_le {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hcons : ∀ j : Fin N, Q (Set.Iio (uhat i (obsIdx j))) ≤ ENNReal.ofReal ((j : ℝ) / N + Γ))
    (k : ℕ) (hk : k ≤ N) (hN : 0 < N) (hΓ0 : 0 < Γ) :
    Q.real (Set.Iio (uSeq uhat i (k + 1))) ≤ min (Γ + (k : ℝ) / N) 1 := by
  apply le_min
  · rcases Nat.lt_or_ge k N with hlt | hge
    · have h := hcons ⟨k, hlt⟩
      have e : uSeq uhat i (k + 1) = uhat i (obsIdx (⟨k, hlt⟩ : Fin N)) :=
        uSeq_of_lt uhat i (by omega)
      rw [e]
      have : (0 : ℝ) ≤ (k : ℝ) / N + Γ := by positivity
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rw [ENNReal.toReal_ofReal this] at h2
      simp only [measureReal_def]
      linarith
    · have hkN : k = N := le_antisymm hk hge
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have : (k : ℝ) / N = 1 := by rw [hkN]; exact div_self hNr.ne'
      have h1 : Q.real (Set.Iio (uSeq uhat i (k + 1))) ≤ 1 := by
        have := measureReal_le_one (μ := Q) (s := Set.Iio (uSeq uhat i (k + 1)))
        exact this
      linarith
  · exact measureReal_le_one

lemma real_Ioi_le {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hcons : ∀ j : Fin N, ENNReal.ofReal (((j : ℝ) + 1) / N - Γ) ≤ Q (Set.Iic (uhat i (obsIdx j))))
    (m : ℕ) (hm : m ≤ N) (hN : 0 < N) (hΓ0 : 0 < Γ) :
    Q.real (Set.Ioi (uSeq uhat i m)) ≤ min (Γ + ((N - m : ℕ) : ℝ) / N) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_min
  · have h1 : Q.real (Set.Ioi (uSeq uhat i m)) ≤ 1 := measureReal_le_one
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · have : ((N - m : ℕ) : ℝ) / N = 1 := by
        rw [h0, Nat.sub_zero]; exact div_self hNr.ne'
      linarith
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hj : j < N := by omega
      have h := hcons ⟨j, hj⟩
      have e : uSeq uhat i (j + 1) = uhat i (obsIdx (⟨j, hj⟩ : Fin N)) :=
        uSeq_of_lt uhat i (by omega)
      rw [e] at *
      have h2 := ENNReal.toReal_mono (measure_ne_top Q _) h
      rw [ENNReal.toReal_ofReal'] at h2
      have h3 : Q.real (Set.Ioi (uhat i (obsIdx (⟨j, hj⟩ : Fin N)))) =
          1 - Q.real (Set.Iic (uhat i (obsIdx (⟨j, hj⟩ : Fin N)))) := by
        rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
      rw [h3]
      have h4 : ((N - (j + 1) : ℕ) : ℝ) = (N : ℝ) - ((j : ℝ) + 1) := by
        rw [Nat.cast_sub hm]; push_cast; ring
      have h5 : ((N : ℝ) - ((j : ℝ) + 1)) / N = 1 - ((j : ℝ) + 1) / N := by
        field_simp
      rw [h4, h5]
      have h6 : ((j : ℝ) + 1) / N - Γ ≤ Q.real (Set.Iic (uhat i (obsIdx (⟨j, hj⟩ : Fin N)))) := by
        have := le_max_left (((j : ℝ) + 1) / N - Γ) 0
        simp only [measureReal_def]
        simp only at h2
        linarith
      linarith
  · exact measureReal_le_one


lemma sum_fin_qL {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d) (g : ℝ → ℝ) :
    ∑ j : Fin (N + 2), qL N Γ j * g (uhat i j) =
      ∑ j ∈ Finset.range (N + 2), qLn N Γ j * g (uSeq uhat i j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => qLn N Γ j * g (uSeq uhat i j)) (N + 2)]
  apply Finset.sum_congr rfl
  intro j _
  rw [uSeq_of_lt uhat i j.isLt]
  rfl

lemma sum_fin_qR {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d) (g : ℝ → ℝ) :
    ∑ j : Fin (N + 2), qR N Γ j * g (uhat i j) =
      ∑ j ∈ Finset.range (N + 2), qLn N Γ j * g (uSeq uhat i (N + 1 - j)) := by
  have h1 : ∑ j : Fin (N + 2), qR N Γ j * g (uhat i j) =
      ∑ j : Fin (N + 2), qL N Γ j * g (uhat i (Fin.rev j)) := by
    rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 2)))
      (fun j => qL N Γ j * g (uhat i (Fin.rev j)))]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.revPerm_apply, Fin.rev_rev, qR]
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => qLn N Γ j * g (uSeq uhat i (N + 1 - j))) (N + 2)]
  apply Finset.sum_congr rfl
  intro j _
  have hlt : N + 1 - (j : ℕ) < N + 2 := by omega
  rw [uSeq_of_lt uhat i hlt]
  have : (Fin.rev j) = (⟨N + 1 - (j : ℕ), hlt⟩ : Fin (N + 2)) := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [this]
  rfl


theorem ec2_anti {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d)
    (Q : Measure ℝ) (hQ : Q ∈ ksRegion uhat Γ i) (g : ℝ → ℝ) (hg : Antitone g) :
    ∫ x, g x ∂Q ≤ ∑ j, qL N Γ j * g (uhat i j) := by
  obtain ⟨hprob, hsupp, hcons⟩ := hQ
  haveI := hprob
  set u := uSeq uhat i with hu_def
  have hu : Monotone u := uSeq_mono uhat hmono i
  have e0 : u 0 = uhat i 0 := by rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have eN : u (N + 1) = uhat i (Fin.last (N + 1)) := by
    rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have hsupp' : Q (Set.Icc (u 0) (u (N + 1)))ᶜ = 0 := by rw [e0, eN]; exact hsupp
  have hbd : ∀ x ∈ Set.Icc (u 0) (u (N + 1)), |g x| ≤ |g (u 0)| + |g (u (N + 1))| := by
    intro x hx
    have h1 := hg hx.1
    have h2 := hg hx.2
    have := le_abs_self (g (u 0)); have := neg_abs_le (g (u 0))
    have := le_abs_self (g (u (N + 1))); have := neg_abs_le (g (u (N + 1)))
    have := abs_nonneg (g (u 0)); have := abs_nonneg (g (u (N + 1)))
    rw [abs_le]; constructor <;> linarith
  have step1 := int_le_step (Q := Q) g hg.measurable (u 0) (u (N + 1)) _ hsupp' hbd
    (g (u (N + 1))) (fun k => Set.Iio (u (k + 1))) (fun k => measurableSet_Iio)
    (fun k => g (u k) - g (u (k + 1))) (N + 1) (by
      intro x hx
      have := pw_anti u hu g hg (N + 1) x hx.1 hx.2
      simpa only [ind_Iio] using this)
  have hcons2 : ∀ j : Fin N, Q (Set.Iio (uhat i (obsIdx j))) ≤ ENNReal.ofReal ((j : ℝ) / N + Γ) :=
    fun j => (hcons j).2
  have step2 : ∑ k ∈ Finset.range (N + 1), (g (u k) - g (u (k + 1))) * Q.real (Set.Iio (u (k + 1)))
      ≤ ∑ k ∈ Finset.range (N + 1), (g (u k) - g (u (k + 1))) * min (Γ + (k : ℝ) / N) 1 := by
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left
    · exact real_Iio_le uhat Γ i Q hcons2 k (by simpa [Nat.lt_succ_iff] using hk) hN hΓ0
    · exact sub_nonneg.2 (hg (hu (Nat.le_succ k)))
  have step3 := abel_qL N hN Γ hΓ0 hΓ1 (fun j => g (u j))
  rw [sum_fin_qL uhat Γ i g]
  linarith

theorem ec2_mono {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d)
    (Q : Measure ℝ) (hQ : Q ∈ ksRegion uhat Γ i) (g : ℝ → ℝ) (hg : Monotone g) :
    ∫ x, g x ∂Q ≤ ∑ j, qR N Γ j * g (uhat i j) := by
  obtain ⟨hprob, hsupp, hcons⟩ := hQ
  haveI := hprob
  set u := uSeq uhat i with hu_def
  have hu : Monotone u := uSeq_mono uhat hmono i
  have e0 : u 0 = uhat i 0 := by rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have eN : u (N + 1) = uhat i (Fin.last (N + 1)) := by
    rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have hsupp' : Q (Set.Icc (u 0) (u (N + 1)))ᶜ = 0 := by rw [e0, eN]; exact hsupp
  have hbd : ∀ x ∈ Set.Icc (u 0) (u (N + 1)), |g x| ≤ |g (u 0)| + |g (u (N + 1))| := by
    intro x hx
    have h1 := hg hx.1
    have h2 := hg hx.2
    have := le_abs_self (g (u 0)); have := neg_abs_le (g (u 0))
    have := le_abs_self (g (u (N + 1))); have := neg_abs_le (g (u (N + 1)))
    have := abs_nonneg (g (u 0)); have := abs_nonneg (g (u (N + 1)))
    rw [abs_le]; constructor <;> linarith
  have step1 := int_le_step (Q := Q) g hg.measurable (u 0) (u (N + 1)) _ hsupp' hbd
    (g (u 0)) (fun k => Set.Ioi (u k)) (fun k => measurableSet_Ioi)
    (fun k => g (u (k + 1)) - g (u k)) (N + 1) (by
      intro x hx
      have := pw_mono u hu g hg (N + 1) x hx.1 hx.2
      simpa only [ind_Ioi] using this)
  have hcons1 : ∀ j : Fin N, ENNReal.ofReal (((j : ℝ) + 1) / N - Γ) ≤ Q (Set.Iic (uhat i (obsIdx j))) :=
    fun j => (hcons j).1
  have step2 : ∑ k ∈ Finset.range (N + 1), (g (u (k + 1)) - g (u k)) * Q.real (Set.Ioi (u k))
      ≤ ∑ k ∈ Finset.range (N + 1), (g (u (k + 1)) - g (u k)) *
          min (Γ + ((N - k : ℕ) : ℝ) / N) 1 := by
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left
    · exact real_Ioi_le uhat Γ i Q hcons1 k (by simpa [Nat.lt_succ_iff] using hk) hN hΓ0
    · exact sub_nonneg.2 (hg (hu (Nat.le_succ k)))
  have step3 := abel_qL N hN Γ hΓ0 hΓ1 (fun j => g (u (N + 1 - j)))
  simp only [Nat.sub_self] at step3
  have step4 : ∑ k ∈ Finset.range (N + 1), (g (u (N + 1 - k)) - g (u (N + 1 - (k + 1)))) *
        min (Γ + (k : ℝ) / N) 1
      = ∑ k ∈ Finset.range (N + 1), (g (u (k + 1)) - g (u k)) *
          min (Γ + ((N - k : ℕ) : ℝ) / N) 1 := by
    rw [← Finset.sum_range_reflect (fun k => (g (u (k + 1)) - g (u k)) *
          min (Γ + ((N - k : ℕ) : ℝ) / N) 1) (N + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using hk
    have a1 : N + 1 - k = N + 1 - 1 - k + 1 := by omega
    have a2 : N + 1 - (k + 1) = N + 1 - 1 - k := by omega
    have a3 : N - (N + 1 - 1 - k) = k := by omega
    rw [a1, a2, a3]
  rw [sum_fin_qR uhat Γ i g]
  linarith

end DataDrivenRO.KS

namespace D3de75af

lemma integrable_exp_lin (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hsupp : ∃ a b : ℝ, Q (Set.Icc a b)ᶜ = 0) (c : ℝ) :
    Integrable (fun x => Real.exp (c * x)) Q := by
  obtain ⟨a, b, h⟩ := hsupp
  have hae : ∀ᵐ x ∂Q, x ∈ Set.Icc a b := mem_ae_iff.mpr h
  refine Integrable.of_bound (by fun_prop) (Real.exp (|c| * (|a| + |b|))) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hx' : |x| ≤ |a| + |b| := by
    rw [abs_le]; constructor
    · have := hx.1; have := neg_abs_le a; have := abs_nonneg b; linarith
    · have := hx.2; have := le_abs_self b; have := abs_nonneg a; linarith
  calc c * x ≤ |c * x| := le_abs_self _
    _ = |c| * |x| := abs_mul _ _
    _ ≤ |c| * (|a| + |b|) := mul_le_mul_of_nonneg_left hx' (abs_nonneg _)

end D3de75af

theorem ns_bound {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hsupp : ∀ i, ∃ a b : ℝ, Q i (Set.Icc a b)ᶜ = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    DataDrivenRO.KS.VaR (Measure.pi Q) ε v ≤
      lam * Real.log (1 / ε) + lam * ∑ i, Real.log (∫ x, Real.exp (v i * x / lam) ∂(Q i)) := by
  set P := Measure.pi Q with hP
  set f : (Fin d → ℝ) → ℝ := fun u => u ⬝ᵥ v with hf
  set M : Fin d → ℝ := fun i => ∫ x, Real.exp (v i * x / lam) ∂(Q i) with hM
  have hint : ∀ i, Integrable (fun x => Real.exp (v i * x / lam)) (Q i) := by
    intro i
    have := D3de75af.integrable_exp_lin (Q i) (hsupp i) (v i / lam)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hMpos : ∀ i, 0 < M i := fun i => integral_exp_pos (hint i)
  set T := lam * Real.log (1 / ε) + lam * ∑ i, Real.log (M i) with hT
  have hfm : Measurable f := by
    simp only [hf]; fun_prop
  -- exp (f u / lam) = ∏ exp (v i * u i / lam)
  have hexp : ∀ u : Fin d → ℝ, Real.exp (f u / lam) = ∏ i, Real.exp (v i * u i / lam) := by
    intro u
    rw [← Real.exp_sum]
    congr 1
    simp only [hf, dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hEint : Integrable (fun u => Real.exp (f u / lam)) P := by
    have := Integrable.fintype_prod (μ := Q) (f := fun i x => Real.exp (v i * x / lam)) hint
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hexp]
  have hE : ∫ u, Real.exp (f u / lam) ∂P = ∏ i, M i := by
    simp_rw [hexp]
    exact integral_fintype_prod_eq_prod (fun i x => Real.exp (v i * x / lam))
  have hprodpos : 0 < ∏ i, M i := Finset.prod_pos fun i _ => hMpos i
  have hexpT : Real.exp (T / lam) = (1 / ε) * ∏ i, M i := by
    have : T / lam = Real.log (1 / ε) + ∑ i, Real.log (M i) := by
      rw [hT]; field_simp
    rw [this, Real.exp_add, Real.exp_log (by positivity), Real.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun i _ => Real.exp_log (hMpos i)
  -- Markov
  set S := {u | Real.exp (T / lam) ≤ Real.exp (f u / lam)} with hS
  have hmarkov : Real.exp (T / lam) * P.real S ≤ ∫ u, Real.exp (f u / lam) ∂P :=
    mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun u => (Real.exp_pos (f u / lam)).le) hEint (Real.exp (T / lam))
  rw [hE] at hmarkov
  have hbad : P.real S ≤ ε := by
    have h1 : (1 / ε) * ((∏ i, M i) * P.real S) ≤ ∏ i, M i := by
      rw [← mul_assoc, ← hexpT]; exact hmarkov
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hε0] at h1
    have h2 : (∏ i, M i) * (P.real S - ε) ≤ 0 := by nlinarith
    have := nonpos_of_mul_nonpos_right h2 hprodpos
    linarith
  have hsub : {u | T < f u} ⊆ S := by
    intro u hu
    simp only [hS, Set.mem_setOf_eq] at hu ⊢
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hu.le hlam.le)
  have hgt : P.real {u | T < f u} ≤ ε := (measureReal_mono hsub).trans hbad
  have hmem : ENNReal.ofReal (1 - ε) ≤ P {u | f u ≤ T} := by
    have hc : {u | f u ≤ T} = {u | T < f u}ᶜ := by
      ext u; simp
    have hms : MeasurableSet {u | T < f u} := measurableSet_lt measurable_const hfm
    have hr : P.real {u | f u ≤ T} = 1 - P.real {u | T < f u} := by
      rw [hc, probReal_compl_eq_one_sub hms]
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    change 1 - ε ≤ P.real {u | f u ≤ T}
    rw [hr]; linarith
  -- bounded below
  have hbdd : BddBelow {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {u | f u ≤ y}} := by
    have hten := tendsto_measure_iInter_atTop (μ := P) (s := fun n : ℕ => {u | f u ≤ -(n : ℝ)})
      (fun n => (measurableSet_le hfm measurable_const).nullMeasurableSet)
      (by
        intro m n hmn u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith)
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {u : Fin d → ℝ | f u ≤ -(n : ℝ)}) = ∅ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-f u)
      exact ⟨n, by linarith⟩
    rw [hempty, measure_empty] at hten
    have hpos : (0 : ENNReal) < ENNReal.ofReal (1 - ε) := ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨n, hn⟩ := (hten.eventually (gt_mem_nhds hpos)).exists
    refine ⟨-(n : ℝ), fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    simp only [Set.mem_setOf_eq] at hy
    have : P {u | f u ≤ y} ≤ P {u | f u ≤ -(n : ℝ)} := by
      apply measure_mono
      intro u hu
      simp only [Set.mem_setOf_eq] at hu ⊢
      linarith
    exact absurd (hy.trans this) (not_le.mpr hn)
  have hVaR : DataDrivenRO.KS.VaR P ε v ≤ T := by
    unfold DataDrivenRO.KS.VaR MultistageStochastic.valueAtRisk
    exact csInf_le hbdd hmem
  exact hVaR

namespace DataDrivenRO.KS

theorem var_le_worst_case_bound {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ productRegion uhat Γ) (v : Fin d → ℝ)
    (lam : ℝ) (hlam : 0 < lam) :
    VaR P ε v ≤ boundKS uhat Γ ε v lam := by
  obtain ⟨Q, hprob, hQ, rfl⟩ := hP
  haveI : ∀ i, IsProbabilityMeasure (Q i) := hprob
  have hsupp : ∀ i, ∃ a b : ℝ, Q i (Set.Icc a b)ᶜ = 0 := fun i => ⟨_, _, (hQ i).2.1⟩
  have h1 := ns_bound Q hsupp ε hε0 hε1 v lam hlam
  have hint : ∀ i, Integrable (fun x => Real.exp (v i * x / lam)) (Q i) := by
    intro i
    have := D3de75af.integrable_exp_lin (Q i) (hsupp i) (v i / lam)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hEC : ∀ i, ∫ x, Real.exp (v i * x / lam) ∂(Q i) ≤ max
      (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
      (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam)) := by
    intro i
    rcases le_total 0 (v i) with h | h
    · have hg : Monotone (fun x : ℝ => Real.exp (v i * x / lam)) := fun a b hab =>
        Real.exp_le_exp.2 (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab h) hlam.le)
      exact (ec2_mono uhat Γ hN hΓ0 hΓ1 hmono i (Q i) (hQ i) _ hg).trans (le_max_right _ _)
    · have hg : Antitone (fun x : ℝ => Real.exp (v i * x / lam)) := fun a b hab =>
        Real.exp_le_exp.2 (div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hab h) hlam.le)
      exact (ec2_anti uhat Γ hN hΓ0 hΓ1 hmono i (Q i) (hQ i) _ hg).trans (le_max_left _ _)
  have hpos : ∀ i, 0 < ∫ x, Real.exp (v i * x / lam) ∂(Q i) := fun i => integral_exp_pos (hint i)
  have h2 : ∑ i, Real.log (∫ x, Real.exp (v i * x / lam) ∂(Q i)) ≤ ∑ i, Real.log (max
      (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
      (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam))) :=
    Finset.sum_le_sum (fun i _ => Real.log_le_log (hpos i) (hEC i))
  have h3 := mul_le_mul_of_nonneg_left h2 hlam.le
  unfold boundKS
  linarith

end DataDrivenRO.KS

open DataDrivenRO.KS in
theorem ks5_sol_3059 {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((UI uhat Γ ε).Nonempty ∧ Convex ℝ (UI uhat Γ ε) ∧ IsCompact (UI uhat Γ ε)) ∧
    ∀ v : Fin d → ℝ,
      (∀ P ∈ productRegion uhat Γ,
        VaR P ε v ≤ RobustMDP.Shared.supportFunction (UI uhat Γ ε) v) ∧
      IsGLB (boundKS uhat Γ ε v '' Set.Ioi 0)
        (RobustMDP.Shared.supportFunction (UI uhat Γ ε) v) := by
  refine ⟨⟨?_, UI_convex uhat Γ ε hN hΓ0 hΓ1, UI_isCompact uhat Γ hN hΓ0 hΓ1 ε⟩, fun v => ?_⟩
  · refine ⟨fun i => ∑ j, uhat i j * mix N Γ 0 j, fun _ => 0, fun _ => mix N Γ 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact ⟨le_refl _, zero_le_one⟩
    · intro i; exact mix_mem_simplex N hN Γ hΓ0 hΓ1 ⟨le_refl _, zero_le_one⟩
    · intro i; rfl
    · intro i j hj; exact hj
    · simp only [relEntropy_self, Finset.sum_const_zero]
      apply Real.log_nonneg
      rw [one_div]
      exact (one_le_inv₀ hε0).2 hε1.le
  · have hg := strong_duality uhat Γ hN hΓ0 hΓ1 ε hε0 hε1 v
    refine ⟨fun P hP => ?_, hg⟩
    apply hg.2
    rintro _ ⟨lam, hlam, rfl⟩
    exact var_le_worst_case_bound uhat Γ hN hΓ0 hΓ1 hmono ε hε0 hε1 P hP v lam hlam


-- New lemmas for the full Theorem 5

set_option autoImplicit false

open MeasureTheory

namespace KSFullAux1e

open DataDrivenRO.KSFull

lemma beta_facts {d : ℕ} (hd : 0 < d) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < marginalLevel d α ∧ marginalLevel d α < 1 ∧ (1 - marginalLevel d α) ^ d = 1 - α := by
  unfold marginalLevel
  have h1 : 0 < 1 - α := by linarith
  have h2 : 1 - α < 1 := by linarith
  have hd' : (0:ℝ) < 1 / (d:ℝ) := by positivity
  have hlt : (1 - α) ^ (1 / (d:ℝ)) < 1 := Real.rpow_lt_one h1.le h2 hd'
  have hpos : 0 < (1 - α) ^ (1 / (d:ℝ)) := Real.rpow_pos_of_pos h1 _
  refine ⟨by linarith, by linarith, ?_⟩
  rw [sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul h1.le,
    one_div_mul_cancel (by exact_mod_cast hd.ne'), Real.rpow_one]

lemma measurableSet_sort_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {s : Fin N → ℝ | Tuple.sort s = σ} := by
  have : {s : Fin N → ℝ | Tuple.sort s = σ} =
      ⋂ i : Fin N, ⋂ j : Fin N, ({s : Fin N → ℝ | i ≤ j → s (σ i) ≤ s (σ j)} ∩
        {s | i < j → s (σ i) = s (σ j) → σ i < σ j}) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [eq_comm, Tuple.eq_sort_iff]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨fun hij => h1 hij, h2 i j⟩
    · intro h
      exact ⟨fun i j hij => (h i j).1 hij, fun i j hij => (h i j).2 hij⟩
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  refine MeasurableSet.inter ?_ ?_
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
    · simp only [hij, false_implies, Set.setOf_true, MeasurableSet.univ]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp only [hij, hs, true_implies, implies_true, Set.setOf_true, MeasurableSet.univ]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))).compl
    · simp only [hij, false_implies, Set.setOf_true, MeasurableSet.univ]

lemma ord_eq_sum {N : ℕ} (s : Fin N → ℝ) (r : Fin N) :
    RobustSAA.Univariate.ord s r = ∑ σ : Equiv.Perm (Fin N),
      {s' : Fin N → ℝ | Tuple.sort s' = σ}.indicator (fun s' => s' (σ r)) s := by
  rw [Finset.sum_eq_single (Tuple.sort s)]
  · simp [RobustSAA.Univariate.ord, Set.indicator]
  · intro σ _ hσ
    have : Tuple.sort s ≠ σ := fun h => hσ h.symm
    simp [Set.indicator, this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma measurable_ord {N : ℕ} (r : Fin N) :
    Measurable (fun s : Fin N → ℝ => RobustSAA.Univariate.ord s r) := by
  have : (fun s : Fin N → ℝ => RobustSAA.Univariate.ord s r) = fun s => ∑ σ : Equiv.Perm (Fin N),
      {s' : Fin N → ℝ | Tuple.sort s' = σ}.indicator (fun s' => s' (σ r)) s :=
    funext (fun s => ord_eq_sum s r)
  rw [this]
  exact Finset.measurable_sum _ fun σ _ =>
    (measurable_pi_apply (σ r)).indicator (measurableSet_sort_eq σ)

lemma ord_mono {N : ℕ} (s : Fin N → ℝ) : Monotone (RobustSAA.Univariate.ord s) :=
  Tuple.monotone_sort s

lemma ord_mem {N : ℕ} (s : Fin N → ℝ) (r : Fin N) : ∃ j, RobustSAA.Univariate.ord s r = s j :=
  ⟨_, rfl⟩

lemma ord_comp {N : ℕ} (s : Fin N → ℝ) (G : ℝ → ℝ)
    (h : Monotone (fun r => G (RobustSAA.Univariate.ord s r))) :
    RobustSAA.Univariate.ord (fun r => G (s r)) = fun r => G (RobustSAA.Univariate.ord s r) := by
  unfold RobustSAA.Univariate.ord
  exact ((Tuple.comp_sort_eq_comp_iff_monotone (f := fun r => G (s r))
    (σ := Tuple.sort s)).2 h).symm

lemma coe_fin_bounds {N : ℕ} (r : Fin N) : (0:ℝ) ≤ (r : ℝ) ∧ (r : ℝ) + 1 ≤ N := by
  constructor
  · positivity
  · have := Nat.succ_le_of_lt r.isLt
    exact_mod_cast this

lemma stat_term_le {N : ℕ} (s : Fin N → ℝ) (r : Fin N) :
    max (((r : ℝ) + 1) / N - RobustSAA.Univariate.ord s r)
      (RobustSAA.Univariate.ord s r - (r : ℝ) / N) ≤ uniformStatistic s := by
  unfold uniformStatistic
  exact le_ciSup (f := fun r : Fin N => max (((r : ℝ) + 1) / N - RobustSAA.Univariate.ord s r)
    (RobustSAA.Univariate.ord s r - (r : ℝ) / N)) (Finite.bddAbove_range _) r

lemma stat_ge {N : ℕ} (hN : 0 < N) (s : Fin N → ℝ) : 1 / (2 * (N:ℝ)) ≤ uniformStatistic s := by
  have h := stat_term_le s ⟨0, hN⟩
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have h0 : (((⟨0, hN⟩ : Fin N) : ℕ) : ℝ) = 0 := by simp
  rw [h0] at h
  simp only [zero_add, zero_div, sub_zero] at h
  have e : (1:ℝ) / N = 1 / (2 * N) + 1 / (2 * N) := by field_simp; ring
  have : 1 / (2 * (N:ℝ)) ≤ max (1 / N - RobustSAA.Univariate.ord s ⟨0, hN⟩)
      (RobustSAA.Univariate.ord s ⟨0, hN⟩) := by
    rcases le_total (RobustSAA.Univariate.ord s ⟨0, hN⟩) (1 / (2 * N)) with hx | hx
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right hx
  linarith

lemma stat_le_box {N : ℕ} (hN : 0 < N) (s : Fin N → ℝ) (δ : ℝ)
    (hs : ∀ r, s r ∈ Set.Icc δ (1 - δ)) : uniformStatistic s ≤ 1 - δ := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  unfold uniformStatistic
  refine ciSup_le fun r => ?_
  obtain ⟨j, hj⟩ := ord_mem s r
  have hx := hs j
  rw [hj]
  obtain ⟨h0, h1⟩ := coe_fin_bounds r
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have a1 : ((r:ℝ) + 1) / N ≤ 1 := by rw [div_le_one hN']; exact h1
  have a2 : 0 ≤ (r:ℝ) / N := div_nonneg h0 hN'.le
  exact max_le (by linarith [hx.1]) (by linarith [hx.2])

lemma measurable_stat {N : ℕ} : Measurable (fun s : Fin N → ℝ => uniformStatistic s) := by
  unfold uniformStatistic
  refine Measurable.iSup fun r => ?_
  exact Measurable.max (measurable_const.sub (measurable_ord r))
    ((measurable_ord r).sub measurable_const)

lemma uniform01_prob : IsProbabilityMeasure uniform01 :=
  ⟨by simp [uniform01]⟩

lemma uniform01_eq : uniform01 = volume.restrict (Set.Ioo (0:ℝ) 1) := by
  unfold uniform01
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm

lemma box_measure {N : ℕ} (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    uniformSampleLaw N (Set.univ.pi fun _ => Set.Icc δ (1 - δ)) =
      ENNReal.ofReal ((1 - 2 * δ) ^ N) := by
  haveI := uniform01_prob
  unfold uniformSampleLaw
  rw [Measure.pi_pi]
  have : uniform01 (Set.Icc δ (1 - δ)) = ENNReal.ofReal (1 - 2 * δ) := by
    unfold uniform01
    rw [Measure.restrict_apply measurableSet_Icc,
      Set.inter_eq_left.2 (Set.Icc_subset_Icc h0 (by linarith)), Real.volume_Icc]
    congr 1; ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by linarith)]

lemma le_measure_le_of_forall {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (a : ℝ) (c : ENNReal)
    (h : ∀ n : ℕ, c ≤ μ {x | f x ≤ a + 1 / ((n:ℝ) + 1)}) : c ≤ μ {x | f x ≤ a} := by
  have hset : {x | f x ≤ a} = ⋂ n : ℕ, {x | f x ≤ a + 1 / ((n:ℝ) + 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx n
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    · intro hx
      by_contra hlt
      push_neg at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      have := hx n
      linarith
  rw [hset, Antitone.measure_iInter]
  · exact le_iInf h
  · intro m n hmn x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hc : (m:ℝ) ≤ n := Nat.cast_le.2 hmn
    have : 1 / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · intro n; exact (measurableSet_le hf measurable_const).nullMeasurableSet
  · exact ⟨0, measure_ne_top _ _⟩

lemma gamma_facts {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < criticalValue N β ∧ criticalValue N β < 1 ∧
    IsLeast {t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}} (criticalValue N β) := by
  haveI := uniform01_prob
  haveI : IsProbabilityMeasure (uniformSampleLaw N) := by
    unfold uniformSampleLaw; infer_instance
  have hΓ : criticalValue N β = sInf {t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}} := rfl
  rw [hΓ]
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hδ0 : 0 < β / (2 * N) := by positivity
  have hδ1 : β / (2 * N) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hmem : 1 - β / (2 * N) ∈ {t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}} := by
    show ENNReal.ofReal (1 - β) ≤ _
    calc ENNReal.ofReal (1 - β) ≤ ENNReal.ofReal ((1 - 2 * (β / (2 * N))) ^ N) := by
          apply ENNReal.ofReal_le_ofReal
          have h2 := one_add_mul_le_pow (a := -(2 * (β / (2 * N)))) (by linarith) N
          have e1 : (1 - 2 * (β / (2 * N))) = 1 + -(2 * (β / (2 * N))) := by ring
          have e2 : (1:ℝ) + N * -(2 * (β / (2 * N))) = 1 - β := by field_simp; ring
          rw [e1]; linarith
      _ = uniformSampleLaw N (Set.univ.pi fun _ => Set.Icc (β / (2 * N)) (1 - β / (2 * N))) :=
          (box_measure _ hδ0.le hδ1).symm
      _ ≤ _ := measure_mono (fun s hs => stat_le_box hN s _ (fun r => hs r (Set.mem_univ r)))
  have hlow : ∀ t ∈ {t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}}, 1 / (2 * (N:ℝ)) ≤ t := by
    intro t ht
    have hpos : 0 < ENNReal.ofReal (1 - β) := ENNReal.ofReal_pos.2 (by linarith)
    have hne0 : uniformSampleLaw N {s | uniformStatistic s ≤ t} ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hpos ht)
    obtain ⟨s, hs⟩ := (Set.nonempty_iff_ne_empty (s := {s : Fin N → ℝ | uniformStatistic s ≤ t})).2 (fun h => hne0 (by rw [h, measure_empty]))
    exact le_trans (stat_ge hN s) hs
  have hne : ({t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}}).Nonempty := ⟨_, hmem⟩
  have hbdd : BddBelow {t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}} := ⟨_, hlow⟩
  refine ⟨lt_of_lt_of_le (by positivity) (le_csInf hne hlow),
    lt_of_le_of_lt (csInf_le hbdd hmem) (by linarith), ?_, fun t ht => csInf_le hbdd ht⟩
  show ENNReal.ofReal (1 - β) ≤ _
  refine le_measure_le_of_forall (uniformSampleLaw N) (fun s => uniformStatistic s)
    measurable_stat _ _ fun n => ?_
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hne
    (lt_add_of_pos_right (sInf _) (by positivity : (0:ℝ) < 1 / ((n:ℝ) + 1)))
  exact le_trans ht (measure_mono fun s hs => le_trans hs htlt.le)

/-- The lower quantile function of a law on `ℝ`. -/
noncomputable def qfun (Q : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x | u ≤ ProbabilityTheory.cdf Q x}

section quantile

variable (Q : Measure ℝ) [IsProbabilityMeasure Q]

lemma q_nonempty {u : ℝ} (hu1 : u < 1) : {x | u ≤ ProbabilityTheory.cdf Q x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((ProbabilityTheory.tendsto_cdf_atTop (μ := Q)).eventually
    (eventually_gt_nhds hu1)).exists
  exact ⟨x, hx.le⟩

lemma q_bdd {u : ℝ} (hu0 : 0 < u) : BddBelow {x | u ≤ ProbabilityTheory.cdf Q x} := by
  obtain ⟨x0, hx0⟩ := ((ProbabilityTheory.tendsto_cdf_atBot (μ := Q)).eventually
    (eventually_lt_nhds hu0)).exists_forall_of_atBot
  refine ⟨x0, fun x hx => ?_⟩
  by_contra h
  push_neg at h
  have := hx0 x h.le
  simp only [Set.mem_setOf_eq] at hx
  linarith

lemma q_spec {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : u ≤ ProbabilityTheory.cdf Q (qfun Q u) := by
  have hc := ((ProbabilityTheory.cdf Q).right_continuous (qfun Q u)).mono Set.Ioi_subset_Ici_self
  refine ge_of_tendsto hc ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨x, hx, hxy⟩ := exists_lt_of_csInf_lt (q_nonempty Q hu1) hy
  exact le_trans hx ((ProbabilityTheory.cdf Q).mono hxy.le)

lemma q_le_iff {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (x : ℝ) :
    qfun Q u ≤ x ↔ u ≤ ProbabilityTheory.cdf Q x := by
  constructor
  · intro h; exact le_trans (q_spec Q hu0 hu1) ((ProbabilityTheory.cdf Q).mono h)
  · intro h; exact csInf_le (q_bdd Q hu0) h

lemma q_monoOn : MonotoneOn (qfun Q) (Set.Ioo 0 1) := by
  intro u hu v hv huv
  exact csInf_le_csInf (q_bdd Q hu.1) (q_nonempty Q hv.2) (fun x hx => le_trans huv hx)

lemma q_Iio {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Q (Set.Iio (qfun Q u)) ≤ ENNReal.ofReal u := by
  have hU : Set.Iio (qfun Q u) = ⋃ n : ℕ, Set.Iic (qfun Q u - 1 / ((n:ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  rw [hU, Monotone.measure_iUnion]
  · refine iSup_le fun n => ?_
    rw [← ProbabilityTheory.ofReal_cdf (μ := Q)]
    apply ENNReal.ofReal_le_ofReal
    by_contra h
    push_neg at h
    have h1 := (q_le_iff Q hu0 hu1 _).2 h.le
    have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  · intro m n hmn x hx
    simp only [Set.mem_Iic] at hx ⊢
    have hc : (m:ℝ) ≤ n := Nat.cast_le.2 hmn
    have : 1 / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith

lemma q_aemeas : AEMeasurable (qfun Q) uniform01 := by
  rw [uniform01_eq]
  exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (q_monoOn Q)

lemma q_map : uniform01.map (qfun Q) = Q := by
  haveI := uniform01_prob
  haveI : IsProbabilityMeasure (uniform01.map (qfun Q)) := Measure.isProbabilityMeasure_map (q_aemeas Q)
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply_of_aemeasurable (q_aemeas Q) measurableSet_Iic, uniform01_eq,
    Measure.restrict_apply' measurableSet_Ioo, ← ProbabilityTheory.ofReal_cdf (μ := Q) x]
  have hset : qfun Q ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 =
      Set.Ioo 0 1 ∩ Set.Iic (ProbabilityTheory.cdf Q x) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h, h0, h1⟩; exact ⟨⟨h0, h1⟩, (q_le_iff Q h0 h1 x).1 h⟩
    · rintro ⟨⟨h0, h1⟩, h⟩; exact ⟨(q_le_iff Q h0 h1 x).2 h, h0, h1⟩
  rw [hset]
  rcases (ProbabilityTheory.cdf_le_one (μ := Q) x).lt_or_eq with hlt | heq
  · have e : Set.Ioo (0:ℝ) 1 ∩ Set.Iic (ProbabilityTheory.cdf Q x) =
        Set.Ioc 0 (ProbabilityTheory.cdf Q x) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
      · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩
    rw [e, Real.volume_Ioc, sub_zero]
  · rw [heq]
    have e : Set.Ioo (0:ℝ) 1 ∩ Set.Iic 1 = Set.Ioo 0 1 := Set.inter_eq_left.2 (fun u hu => le_of_lt hu.2)
    rw [e, Real.volume_Ioo, sub_zero]

end quantile

lemma measurable_Iic_meas (Q : Measure ℝ) : Measurable (fun x : ℝ => Q (Set.Iic x)) :=
  Monotone.measurable fun _ _ hab => measure_mono (Set.Iic_subset_Iic.2 hab)

lemma measurable_Iio_meas (Q : Measure ℝ) : Measurable (fun x : ℝ => Q (Set.Iio x)) :=
  Monotone.measurable fun _ _ hab => measure_mono (Set.Iio_subset_Iio hab)

lemma acc_measurable {N : ℕ} (Q : Measure ℝ) (Γ : ℝ) :
    MeasurableSet (marginalAcceptance (N := N) Q Γ) := by
  have : marginalAcceptance (N := N) Q Γ = ⋂ r : Fin N,
      ({s | ENNReal.ofReal (((r : ℝ) + 1) / N - Γ) ≤
          Q (Set.Iic (RobustSAA.Univariate.ord s r))} ∩
        {s | Q (Set.Iio (RobustSAA.Univariate.ord s r)) ≤ ENNReal.ofReal ((r : ℝ) / N + Γ)}) := by
    ext s
    simp only [marginalAcceptance, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [this]
  exact MeasurableSet.iInter fun r =>
    (measurableSet_le measurable_const ((measurable_Iic_meas Q).comp (measurable_ord r))).inter
      (measurableSet_le ((measurable_Iio_meas Q).comp (measurable_ord r)) measurable_const)

lemma acc_bound {N : ℕ} (Q : Measure ℝ) [IsProbabilityMeasure Q] (Γ : ℝ) (c : ENNReal)
    (hΓ : c ≤ uniformSampleLaw N {s | uniformStatistic s ≤ Γ}) :
    c ≤ Measure.pi (fun _ : Fin N => Q) (marginalAcceptance Q Γ) := by
  haveI := uniform01_prob
  have hmap : Measure.pi (fun _ : Fin N => Q) =
      (uniformSampleLaw N).map (fun s r => qfun Q (s r)) := by
    unfold uniformSampleLaw
    rw [Measure.pi_map_pi (fun _ => q_aemeas Q), q_map Q]
  have hae : AEMeasurable (fun s : Fin N → ℝ => fun r => qfun Q (s r)) (uniformSampleLaw N) := by
    unfold uniformSampleLaw
    exact aemeasurable_pi_lambda _ fun r =>
      (q_aemeas Q).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ r)
  rw [hmap, Measure.map_apply_of_aemeasurable hae (acc_measurable Q Γ)]
  refine le_trans hΓ (measure_mono_ae ?_)
  have hall : ∀ᵐ s ∂(uniformSampleLaw N), ∀ r, s r ∈ Set.Ioo (0:ℝ) 1 := by
    rw [ae_all_iff]
    intro r
    unfold uniformSampleLaw
    have h0 : ∀ᵐ x ∂uniform01, x ∈ Set.Ioo (0:ℝ) 1 := by
      rw [uniform01_eq]; exact ae_restrict_mem measurableSet_Ioo
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => uniform01) r).ae (p := fun x => x ∈ Set.Ioo (0:ℝ) 1) h0
  filter_upwards [hall] with s hs
  intro hstat
  change uniformStatistic s ≤ Γ at hstat
  change (fun r => qfun Q (s r)) ∈ marginalAcceptance Q Γ
  have hord_mem : ∀ r, RobustSAA.Univariate.ord s r ∈ Set.Ioo (0:ℝ) 1 := fun r => by
    obtain ⟨j, hj⟩ := ord_mem s r
    rw [hj]; exact hs j
  have hmono : Monotone (fun r => qfun Q (RobustSAA.Univariate.ord s r)) :=
    fun a b hab => q_monoOn Q (hord_mem a) (hord_mem b) (ord_mono s hab)
  simp only [marginalAcceptance, Set.mem_setOf_eq]
  rw [ord_comp s (qfun Q) hmono]
  intro r
  obtain ⟨h0, h1⟩ := hord_mem r
  have ht := le_trans (stat_term_le s r) hstat
  have ha := le_trans (le_max_left _ _) ht
  have hb := le_trans (le_max_right _ _) ht
  have hspec := q_spec Q h0 h1
  constructor
  · rw [← ProbabilityTheory.ofReal_cdf (μ := Q)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · exact le_trans (q_Iio Q h0 h1) (ENNReal.ofReal_le_ofReal (by linarith))

lemma pi_transpose {d N : ℕ} (m : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (m i)] :
    (Measure.pi fun _ : Fin N => Measure.pi m).map (fun S i r => S r i) =
      Measure.pi fun i => Measure.pi fun _ : Fin N => m i := by
  have h1 := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : Fin N) (i : Fin d) => m i)
  have h2 := Measure.infinitePi_map_curry (X := ℝ) (fun (i : Fin d) (_ : Fin N) => m i)
  have h3 := Measure.map_infinitePi_infinitePi_of_inj (P := fun p : Fin N × Fin d => m p.2)
    (f := Prod.swap) Prod.swap_injective
  simp only [Measure.infinitePi_eq_pi] at h1 h2 h3
  have h3' : (Measure.pi fun q : Fin d × Fin N => m q.1) =
      (Measure.pi fun p : Fin N × Fin d => m p.2).map (fun ω q => ω q.swap) := h3.symm
  rw [← h1, ← h2, h3', Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma pi_cols {d N : ℕ} (m : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (m i)]
    (A : Fin d → Set (Fin N → ℝ)) (hA : ∀ i, MeasurableSet (A i)) :
    (Measure.pi fun _ : Fin N => Measure.pi m) (⋂ i, {S | (fun r => S r i) ∈ A i}) =
      ∏ i, (Measure.pi fun _ : Fin N => m i) (A i) := by
  have hT : Measurable (fun (S : Fin N → Fin d → ℝ) (i : Fin d) (r : Fin N) => S r i) := by
    fun_prop
  have hpre : (⋂ i, {S : Fin N → Fin d → ℝ | (fun r => S r i) ∈ A i}) =
      (fun (S : Fin N → Fin d → ℝ) (i : Fin d) (r : Fin N) => S r i) ⁻¹' (Set.univ.pi A) := by
    ext S; simp
  rw [hpre, ← Measure.map_apply hT (MeasurableSet.univ_pi hA), pi_transpose, Measure.pi_pi]

lemma pstar_pi {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (hind : ProbabilityTheory.iIndepFun (fun i : Fin d => fun u : Fin d → ℝ => u i) P) :
    P = Measure.pi (marginal P) := by
  have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).1 hind
  have h2 : (fun (ω : Fin d → ℝ) (i : Fin d) => ω i) = id := rfl
  rw [h2, Measure.map_id] at h
  exact h

lemma padded_bounds {d N : ℕ} (lo hi : Fin d → ℝ) (hbox : lo ≤ hi) (S : Fin N → Fin d → ℝ)
    (hS : S ∈ supportedSamples lo hi) (i : Fin d) (j : Fin (N + 2)) :
    lo i ≤ paddedOrder lo hi S i j ∧ paddedOrder lo hi S i j ≤ hi i := by
  unfold paddedOrder
  split_ifs with h1 h2
  · exact ⟨le_rfl, hbox i⟩
  · obtain ⟨r, hr⟩ := ord_mem (fun r => S r i) ⟨j.val - 1, by omega⟩
    rw [hr]
    exact ⟨(hS r).1 i, (hS r).2 i⟩
  · exact ⟨hbox i, le_rfl⟩

lemma padded_mono {d N : ℕ} (lo hi : Fin d → ℝ) (hbox : lo ≤ hi) (S : Fin N → Fin d → ℝ)
    (hS : S ∈ supportedSamples lo hi) (i : Fin d) : Monotone (paddedOrder lo hi S i) := by
  intro a b hab
  have hb := padded_bounds lo hi hbox S hS i
  have hab' : a.val ≤ b.val := hab
  by_cases ha0 : a.val = 0
  · have : paddedOrder lo hi S i a = lo i := by unfold paddedOrder; rw [dif_pos ha0]
    rw [this]; exact (hb b).1
  by_cases hbN : N < b.val
  · have : paddedOrder lo hi S i b = hi i := by
      unfold paddedOrder
      rw [dif_neg (show ¬ b.val = 0 by omega), dif_neg (show ¬ b.val ≤ N by omega)]
    rw [this]; exact (hb a).2
  have haN : a.val ≤ N := by omega
  have hb0 : ¬ b.val = 0 := by omega
  have hbN' : b.val ≤ N := by omega
  unfold paddedOrder
  rw [dif_neg ha0, dif_pos haN, dif_neg hb0, dif_pos hbN']
  apply ord_mono
  exact Nat.sub_le_sub_right hab' 1

theorem main_of
    (hKS : ∀ {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ),
      0 < N → 0 < Γ → Γ < 1 → (∀ i, Monotone (uhat i)) → ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ((DataDrivenRO.KS.UI uhat Γ ε).Nonempty ∧ Convex ℝ (DataDrivenRO.KS.UI uhat Γ ε) ∧
        IsCompact (DataDrivenRO.KS.UI uhat Γ ε)) ∧
      ∀ v : Fin d → ℝ,
        (∀ P ∈ DataDrivenRO.KS.productRegion uhat Γ,
          DataDrivenRO.KS.VaR P ε v ≤
            RobustMDP.Shared.supportFunction (DataDrivenRO.KS.UI uhat Γ ε) v) ∧
        IsGLB (DataDrivenRO.KS.boundKS uhat Γ ε v '' Set.Ioi 0)
          (RobustMDP.Shared.supportFunction (DataDrivenRO.KS.UI uhat Γ ε) v))
    (hG : ∀ {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] (ε : ℝ), 0 < ε → ε < 1 →
      ∀ U : Set (Fin d → ℝ), U.Nonempty → Convex ℝ U → IsCompact U →
      (∀ v, DataDrivenRO.Guarantee.VaR P ε v ≤ RobustMDP.Shared.supportFunction U v) →
        DataDrivenRO.Guarantee.ImpliesGuarantee P U ε)
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (hind : ProbabilityTheory.iIndepFun (fun i : Fin d => fun u : Fin d → ℝ => u i) Pstar)
    (lo hi : Fin d → ℝ) (hbox : lo ≤ hi)
    (hsupp : Pstar (Set.Icc lo hi)ᶜ = 0)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let β := marginalLevel d α
    let Γ := criticalValue N β
    (0 < β ∧ β < 1 ∧ (1 - β) ^ d = 1 - α) ∧
    (0 < Γ ∧ Γ < 1 ∧
      IsLeast {t : ℝ | ENNReal.ofReal (1 - β) ≤
        uniformSampleLaw N {s | uniformStatistic s ≤ t}} Γ) ∧
    (∀ Q : Measure ℝ, IsProbabilityMeasure Q →
      MeasurableSet (marginalAcceptance (N := N) Q Γ) ∧
      ENNReal.ofReal (1 - β) ≤
        Measure.pi (fun _ : Fin N => Q) (marginalAcceptance Q Γ)) ∧
    (∃ E : Set (Fin N → Fin d → ℝ), E = goodEvent Pstar lo hi α ∧
      MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ sampleLaw Pstar N E ∧
      ∀ S ∈ E, S ∈ supportedSamples lo hi ∧ Pstar ∈ confidenceRegion lo hi α S ∧
        DataDrivenRO.Guarantee.SimultaneouslyImpliesGuarantee Pstar (uncertaintySet lo hi α S)) ∧
    (∀ S ∈ supportedSamples (N := N) lo hi, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      (uncertaintySet lo hi α S ε).Nonempty ∧
      Convex ℝ (uncertaintySet lo hi α S ε) ∧
      IsCompact (uncertaintySet lo hi α S ε) ∧
      ∀ v : Fin d → ℝ,
        IsGLB ((fun lam => DataDrivenRO.KS.boundKS (paddedOrder lo hi S) Γ ε v lam) '' Set.Ioi 0)
          (RobustMDP.Shared.supportFunction (uncertaintySet lo hi α S ε) v)) := by
  intro β Γ
  have hβ : 0 < β ∧ β < 1 ∧ (1 - β) ^ d = 1 - α := beta_facts hd hα0 hα1
  have hΓ : 0 < Γ ∧ Γ < 1 ∧ IsLeast {t : ℝ | ENNReal.ofReal (1 - β) ≤
      uniformSampleLaw N {s | uniformStatistic s ≤ t}} Γ := gamma_facts hN hβ.1 hβ.2.1
  have hacc : ∀ Q : Measure ℝ, IsProbabilityMeasure Q →
      MeasurableSet (marginalAcceptance (N := N) Q Γ) ∧
      ENNReal.ofReal (1 - β) ≤ Measure.pi (fun _ : Fin N => Q) (marginalAcceptance Q Γ) := by
    intro Q hQ
    exact ⟨acc_measurable Q Γ, acc_bound Q Γ _ hΓ.2.2.1⟩
  have hm : ∀ i, IsProbabilityMeasure (marginal Pstar i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hP := pstar_pi Pstar hind
  have hsupp_meas : MeasurableSet (supportedSamples (N := N) lo hi) := by
    have : supportedSamples (N := N) lo hi =
        ⋂ r, (fun S : Fin N → Fin d → ℝ => S r) ⁻¹' Set.Icc lo hi := by
      ext S; simp only [supportedSamples, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact MeasurableSet.iInter fun r => measurableSet_Icc.preimage (measurable_pi_apply r)
  have hcol : ∀ i, Measurable (fun S : Fin N → Fin d → ℝ => fun r => S r i) := fun i => by
    fun_prop
  have hE : goodEvent (N := N) Pstar lo hi α = supportedSamples lo hi ∩
      ⋂ i, {S | (fun r => S r i) ∈ marginalAcceptance (marginal Pstar i) Γ} := by
    ext S
    simp only [goodEvent, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  have hnull : sampleLaw Pstar N (supportedSamples lo hi)ᶜ = 0 := by
    have : (supportedSamples (N := N) lo hi)ᶜ =
        ⋃ r, (fun S : Fin N → Fin d → ℝ => S r) ⁻¹' (Set.Icc lo hi)ᶜ := by
      ext S
      simp only [supportedSamples, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion,
        Set.mem_preimage, not_forall]
    rw [this]
    exact measure_iUnion_null fun r => Measure.pi_eval_preimage_null _ hsupp
  have hlaw : sampleLaw Pstar N = Measure.pi (fun _ : Fin N => Measure.pi (marginal Pstar)) := by
    show Measure.pi (fun _ : Fin N => Pstar) = _
    rw [← hP]
  refine ⟨hβ, hΓ, hacc, ⟨goodEvent Pstar lo hi α, rfl, ?_, ?_, ?_⟩, ?_⟩
  · rw [hE]
    exact hsupp_meas.inter (MeasurableSet.iInter fun i => (acc_measurable _ Γ).preimage (hcol i))
  · rw [hE, Set.inter_comm, measure_inter_conull hnull, hlaw,
      pi_cols (marginal Pstar) _ (fun i => acc_measurable _ Γ)]
    calc ENNReal.ofReal (1 - α) = ∏ _i : Fin d, ENNReal.ofReal (1 - β) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← ENNReal.ofReal_pow (by linarith [hβ.2.1]), hβ.2.2]
      _ ≤ _ := Finset.prod_le_prod' fun i _ => (hacc _ (hm i)).2
  · intro S hS
    obtain ⟨hSs, hSacc⟩ := hS
    have hmono := padded_mono lo hi hbox S hSs
    have hreg : Pstar ∈ confidenceRegion lo hi α S := by
      simp only [confidenceRegion, DataDrivenRO.KS.productRegion, Set.mem_setOf_eq]
      refine ⟨marginal Pstar, hm, fun i => ?_, hP⟩
      simp only [DataDrivenRO.KS.ksRegion, Set.mem_setOf_eq]
      refine ⟨hm i, ?_, fun j => ?_⟩
      · have h0 : paddedOrder lo hi S i 0 = lo i := by
          unfold paddedOrder; simp
        have h1 : paddedOrder lo hi S i (Fin.last (N + 1)) = hi i := by
          unfold paddedOrder; simp
        rw [h0, h1, marginal, Measure.map_apply (measurable_pi_apply i) measurableSet_Icc.compl]
        refine measure_mono_null ?_ hsupp
        intro u hu hu'
        exact hu ⟨hu'.1 i, hu'.2 i⟩
      · have hj : paddedOrder lo hi S i (DataDrivenRO.KS.obsIdx j) =
            RobustSAA.Univariate.ord (fun r => S r i) j := by
          unfold paddedOrder DataDrivenRO.KS.obsIdx
          have h1 : ¬ ((j : ℕ) + 1 = 0) := by omega
          have h2 : (j : ℕ) + 1 ≤ N := j.isLt
          rw [dif_neg h1, dif_pos h2]
          congr 1
        rw [hj]
        have := hSacc i
        simp only [marginalAcceptance, Set.mem_setOf_eq] at this
        exact this j
    refine ⟨hSs, hreg, fun ε hε => ?_⟩
    obtain ⟨⟨hne, hcv, hcp⟩, hv⟩ :=
      hKS (paddedOrder lo hi S) Γ hN hΓ.1 hΓ.2.1 hmono ε hε.1 hε.2
    exact hG Pstar ε hε.1 hε.2 _ hne hcv hcp (fun v => (hv v).1 Pstar hreg)
  · intro S hS ε hε
    obtain ⟨⟨hne, hcv, hcp⟩, hv⟩ :=
      hKS (paddedOrder lo hi S) Γ hN hΓ.1 hΓ.2.1 (padded_mono lo hi hbox S hS) ε hε.1 hε.2
    exact ⟨hne, hcv, hcp, fun v => (hv v).2⟩

end KSFullAux1e


-- Guarantee theorem 1 (copied)

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace DDROG5d

lemma bdd_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) {α : ℝ} (hα : 0 < α) :
    BddBelow {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} := by
  have hanti : Antitone (fun n : ℕ => {ω | Y ω ≤ -(n:ℝ)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hinter : (⋂ n : ℕ, {ω | Y ω ≤ -(n:ℝ)}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (-Y ω)
    exact ⟨n, by linarith⟩
  have ht := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (measurableSet_le hY measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  have hpos : (0:ENNReal) < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
  refine ⟨-(N:ℝ), fun y hy => ?_⟩
  by_contra hlt
  push_neg at hlt
  have : P {ω | Y ω ≤ y} ≤ P {ω | Y ω ≤ -(N:ℝ)} :=
    measure_mono fun ω hω => by simp only [mem_ofPred_eq] at hω ⊢; linarith
  exact absurd (le_trans (show ENNReal.ofReal α ≤ P {ω | Y ω ≤ y} from hy) this)
    (not_le.mpr hN)

lemma ne_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) {α : ℝ} (hα : α < 1) :
    {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}}.Nonempty := by
  have hmono : Monotone (fun n : ℕ => {ω | Y ω ≤ (n:ℝ)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hunion : (⋃ n : ℕ, {ω | Y ω ≤ (n:ℝ)}) = univ := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (Y ω)
    exact ⟨n, hn⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hunion, measure_univ] at ht
  have hlt : ENNReal.ofReal α < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hα
  obtain ⟨N, hN⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  exact ⟨N, hN.le⟩

lemma le_of_var_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) {α : ℝ} (hα1 : α < 1) {t : ℝ}
    (ht : MultistageStochastic.valueAtRisk P Y α ≤ t) :
    ENNReal.ofReal α ≤ P {ω | Y ω ≤ t} := by
  have hS : MultistageStochastic.valueAtRisk P Y α =
      sInf {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} := rfl
  have hmem : ∀ n : ℕ, ENNReal.ofReal α ≤ P {ω | Y ω ≤ t + 1/((n:ℝ)+1)} := by
    intro n
    have hlt : sInf {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} < t + 1/((n:ℝ)+1) := by
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
    obtain ⟨y, hyS, hy⟩ := exists_lt_of_csInf_lt (ne_set P Y hα1) hlt
    exact le_trans (show ENNReal.ofReal α ≤ P {ω | Y ω ≤ y} from hyS)
      (measure_mono fun ω hω => by simp only [mem_ofPred_eq] at hω ⊢; linarith)
  have hanti : Antitone (fun n : ℕ => {ω | Y ω ≤ t + 1/((n:ℝ)+1)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hmn' : (m:ℝ) ≤ n := by exact_mod_cast hmn
    have : 1/((n:ℝ)+1) ≤ 1/((m:ℝ)+1) := by gcongr
    linarith
  have hinter : (⋂ n : ℕ, {ω | Y ω ≤ t + 1/((n:ℝ)+1)}) = {ω | Y ω ≤ t} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
      have := h n
      linarith
    · intro h n
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
  have htend := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (measurableSet_le hY measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter] at htend
  exact ge_of_tendsto' htend (fun n => hmem n)

lemma dot_cont {d : ℕ} (v : Fin d → ℝ) : Continuous (fun u : Fin d → ℝ => u ⬝ᵥ v) := by
  simp only [dotProduct]; fun_prop

lemma dual_repr {d : ℕ} (φ : StrongDual ℝ (Fin d → ℝ)) :
    ∃ w : Fin d → ℝ, ∀ u : Fin d → ℝ, u ⬝ᵥ w = -φ u := by
  refine ⟨fun i => -φ (Pi.single i 1), fun u => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single u]
  rw [map_sum, ← Finset.sum_neg_distrib]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (u i) : Fin d → ℝ) = u i • Pi.single i 1 := by
    ext j; by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  rw [this, map_smul, smul_eq_mul]
  ring

end DDROG5d

open MeasureTheory DataDrivenRO.Guarantee in
theorem guar1_sol_5d39 {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ U : Set (Fin d → ℝ), U.Nonempty → Convex ℝ U → IsCompact U →
      (∀ v, VaR P ε v ≤ RobustMDP.Shared.supportFunction U v) → ImpliesGuarantee P U ε) ∧
    (∀ U : Set (Fin d → ℝ), U.Nonempty →
      (∃ v, BddAbove ((fun u => u ⬝ᵥ v) '' U) ∧
        RobustMDP.Shared.supportFunction U v < VaR P ε v) →
      ∃ f : (Fin d → ℝ) → (Fin 1 → ℝ) → ℝ, IsBiaffine f ∧ ∃ xstar : Fin 1 → ℝ,
        (∀ u ∈ U, f u xstar ≤ 0) ∧ P {u | f u xstar ≤ 0} < ENNReal.ofReal (1 - ε)) := by
  have hα1 : 1 - ε < 1 := by linarith
  have hα0 : 0 < 1 - ε := by linarith
  constructor
  · intro U hne hconv _hcomp hvar k f hconc xstar hfeas
    have hg : ConcaveOn ℝ univ (fun u => f u xstar) := hconc xstar
    have hgc : Continuous (fun u => f u xstar) :=
      continuousOn_univ.mp (hg.continuousOn isOpen_univ)
    have hAconv : Convex ℝ {x ∈ (univ : Set (Fin d → ℝ)) | 0 < f x xstar} := hg.convex_gt 0
    have hAopen : IsOpen {x ∈ (univ : Set (Fin d → ℝ)) | 0 < f x xstar} := by
      simpa only [mem_univ, true_and, Set.sep_univ] using isOpen_lt continuous_const hgc
    have hdisj : Disjoint {x ∈ (univ : Set (Fin d → ℝ)) | 0 < f x xstar} U := by
      rw [Set.disjoint_left]
      rintro a ⟨_, ha⟩ hU
      exact absurd (hfeas a hU) (not_le.mpr ha)
    obtain ⟨φ, s, hA, hB⟩ := geometric_hahn_banach_open hAconv hAopen hconv hdisj
    obtain ⟨w, hw⟩ := DDROG5d.dual_repr φ
    have hσ : RobustMDP.Shared.supportFunction U w ≤ -s := by
      apply csSup_le (hne.image _)
      rintro _ ⟨b, hb, rfl⟩
      have := hB b hb
      have h2 := hw b
      simp only [dotProduct] at h2
      linarith
    have hv := DDROG5d.le_of_var_le P (fun u => u ⬝ᵥ w) (DDROG5d.dot_cont w).measurable hα1
      ((hvar w).trans hσ)
    refine le_trans hv (measure_mono fun u hu => ?_)
    simp only [mem_ofPred_eq] at hu ⊢
    by_contra hpos
    push_neg at hpos
    have := hA u ⟨mem_univ _, hpos⟩
    have h2 := hw u
    linarith
  · rintro U _hne ⟨v, hbdd, hlt⟩
    refine ⟨fun u x => u ⬝ᵥ v - x 0, ?_, fun _ => RobustMDP.Shared.supportFunction U v, ?_, ?_⟩
    · refine ⟨0, v, fun _ => -1, 0, fun u x => ?_⟩
      have h1 : (fun _ : Fin 1 => (-1:ℝ)) ⬝ᵥ x = -x 0 := by simp [dotProduct]
      rw [Matrix.zero_mulVec, dotProduct_zero, dotProduct_comm v u, h1]
      ring
    · intro u hu
      have : u ⬝ᵥ v ≤ sSup ((fun u => u ⬝ᵥ v) '' U) := le_csSup hbdd (mem_image_of_mem _ hu)
      show u ⬝ᵥ v - RobustMDP.Shared.supportFunction U v ≤ 0
      have heq : RobustMDP.Shared.supportFunction U v = sSup ((fun u => u ⬝ᵥ v) '' U) := rfl
      linarith
    · by_contra h
      push_neg at h
      have hset : {u : Fin d → ℝ | u ⬝ᵥ v - RobustMDP.Shared.supportFunction U v ≤ 0} =
          {u | (fun u => u ⬝ᵥ v) u ≤ RobustMDP.Shared.supportFunction U v} := by
        ext u; simp only [mem_ofPred_eq, sub_nonpos]
      rw [hset] at h
      have : VaR P ε v ≤ RobustMDP.Shared.supportFunction U v :=
        csInf_le (DDROG5d.bdd_set P (fun u => u ⬝ᵥ v) (DDROG5d.dot_cont v).measurable hα0) h
      linarith


open MeasureTheory DataDrivenRO DataDrivenRO.KSFull in
theorem solution {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (hind : ProbabilityTheory.iIndepFun (fun i : Fin d => fun u : Fin d → ℝ => u i) Pstar)
    (lo hi : Fin d → ℝ) (hbox : lo ≤ hi)
    (hsupp : Pstar (Set.Icc lo hi)ᶜ = 0)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let β := marginalLevel d α
    let Γ := criticalValue N β
    (0 < β ∧ β < 1 ∧ (1 - β) ^ d = 1 - α) ∧
    (0 < Γ ∧ Γ < 1 ∧
      IsLeast {t : ℝ | ENNReal.ofReal (1 - β) ≤
        uniformSampleLaw N {s | uniformStatistic s ≤ t}} Γ) ∧
    (∀ Q : Measure ℝ, IsProbabilityMeasure Q →
      MeasurableSet (marginalAcceptance (N := N) Q Γ) ∧
      ENNReal.ofReal (1 - β) ≤
        Measure.pi (fun _ : Fin N => Q) (marginalAcceptance Q Γ)) ∧
    (∃ E : Set (Fin N → Fin d → ℝ), E = goodEvent Pstar lo hi α ∧
      MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ sampleLaw Pstar N E ∧
      ∀ S ∈ E, S ∈ supportedSamples lo hi ∧ Pstar ∈ confidenceRegion lo hi α S ∧
        Guarantee.SimultaneouslyImpliesGuarantee Pstar (uncertaintySet lo hi α S)) ∧
    (∀ S ∈ supportedSamples (N := N) lo hi, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      (uncertaintySet lo hi α S ε).Nonempty ∧
      Convex ℝ (uncertaintySet lo hi α S ε) ∧
      IsCompact (uncertaintySet lo hi α S ε) ∧
      ∀ v : Fin d → ℝ,
        IsGLB ((fun lam => KS.boundKS (paddedOrder lo hi S) Γ ε v lam) '' Set.Ioi 0)
          (RobustMDP.Shared.supportFunction (uncertaintySet lo hi α S ε) v)) := by
  exact KSFullAux1e.main_of
    (fun uhat Γ hN h0 h1 hm ε he0 he1 => ks5_sol_3059 uhat Γ hN h0 h1 hm ε he0 he1)
    (fun P _ ε h0 h1 => (guar1_sol_5d39 P ε h0 h1).1) hd hN Pstar hind lo hi hbox hsupp α hα0 hα1
