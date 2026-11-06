-- Prove2me | solution 1 for DROOptimal.Predictor.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:32:52.011209+00:00
-- url     : https://prove2.me/submissions/0b2e5d88-5838-4b38-a52c-32a0f685e656

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

theorem eq15_aux {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (γ : ↥X → Fin d → ℝ)
    (r : ℝ) (hr : 0 < r) (x : ↥X) (ℙ'₀ ℙ₀ : Δ d) (h14 : relEntropy ℙ'₀ ℙ₀ ≤ (r : EReal))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ℙ₂ : Δ d, (∀ i, 0 < (ℙ₂ : Fin d → ℝ) i) ∧ relEntropy ℙ'₀ ℙ₂ < (r : EReal) ∧
      cost γ x ℙ₀ < cost γ x ℙ₂ + ε := by
  classical
  -- unpack h14
  have hcond : ∀ i, (ℙ₀ : Fin d → ℝ) i = 0 → (ℙ'₀ : Fin d → ℝ) i = 0 := by
    by_contra h
    simp only [relEntropy, h, if_false, top_le_iff] at h14
    exact EReal.coe_ne_top _ h14
  have hsum : (∑ i, (ℙ'₀ : Fin d → ℝ) i * Real.log ((ℙ'₀ : Fin d → ℝ) i / (ℙ₀ : Fin d → ℝ) i)) ≤ r := by
    rw [relEntropy, if_pos hcond] at h14
    exact_mod_cast h14
  -- d ≥ 1
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have := ℙ'₀.2.2
      simp at this
    · exact h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- uniform distribution
  let u : Fin d → ℝ := fun _ => 1 / (d : ℝ)
  have hu : u ∈ stdSimplex ℝ (Fin d) := by
    refine ⟨fun _ => by positivity, ?_⟩
    simp [u, Finset.card_univ]
    field_simp
  -- parameters
  set η : ℝ := (1 - Real.exp (-r)) / 2 with hη
  have hexp : Real.exp (-r) < 1 := by have := Real.exp_lt_exp.mpr (show -r < 0 by linarith); simpa using this
  have hexp0 : 0 < Real.exp (-r) := Real.exp_pos _
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η < 1 := by rw [hη]; linarith
  set L : ℝ := -Real.log (1 - η) with hL
  have hLr : L < r := by
    rw [hL, neg_lt]
    have : Real.exp (-r) < 1 - η := by rw [hη]; linarith
    have := Real.log_lt_log hexp0 this
    rwa [Real.log_exp] at this
  let m : Fin d → ℝ := (1 - η) • (ℙ'₀ : Fin d → ℝ) + η • u
  have hm : m ∈ stdSimplex ℝ (Fin d) :=
    convex_stdSimplex ℝ (Fin d) ℙ'₀.2 hu (by linarith) hη0.le (by ring)
  set K : ℝ := |cost γ x ℙ₀ - cost γ x ⟨m, hm⟩| with hK
  set lam : ℝ := min 1 (ε / (2 * (K + 1))) with hlam
  have hK0 : 0 ≤ K := abs_nonneg _
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  let q : Fin d → ℝ := (1 - lam) • (ℙ₀ : Fin d → ℝ) + lam • m
  have hq : q ∈ stdSimplex ℝ (Fin d) :=
    convex_stdSimplex ℝ (Fin d) ℙ₀.2 hm (by linarith) hlam0.le (by ring)
  have hP0nn : ∀ i, 0 ≤ (ℙ₀ : Fin d → ℝ) i := fun i => ℙ₀.2.1 i
  have hP'nn : ∀ i, 0 ≤ (ℙ'₀ : Fin d → ℝ) i := fun i => ℙ'₀.2.1 i
  have hmpos : ∀ i, 0 < m i := by
    intro i
    have := hP'nn i
    simp only [m, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 < η * (1 / (d : ℝ)) := by positivity
    nlinarith
  have hmge : ∀ i, (1 - η) * (ℙ'₀ : Fin d → ℝ) i ≤ m i := by
    intro i
    simp only [m, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 < η * (1 / (d : ℝ)) := by positivity
    linarith
  have hqpos : ∀ i, 0 < q i := by
    intro i
    simp only [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hP0nn i
    have := hmpos i
    have : 0 ≤ 1 - lam := by linarith
    have : 0 < lam * m i := mul_pos hlam0 (hmpos i)
    nlinarith
  refine ⟨⟨q, hq⟩, hqpos, ?_, ?_⟩
  · -- relative entropy bound
    have hcondq : ∀ i, (q : Fin d → ℝ) i = 0 → (ℙ'₀ : Fin d → ℝ) i = 0 :=
      fun i h => absurd h (hqpos i).ne'
    simp only [relEntropy]
    rw [if_pos (show ∀ i, ((⟨q, hq⟩ : Δ d) : Fin d → ℝ) i = 0 → (ℙ'₀ : Fin d → ℝ) i = 0 from hcondq)]
    show ((∑ i, (ℙ'₀ : Fin d → ℝ) i * Real.log ((ℙ'₀ : Fin d → ℝ) i / q i) : ℝ) : EReal) < r
    have hterm : ∀ i, (ℙ'₀ : Fin d → ℝ) i * Real.log ((ℙ'₀ : Fin d → ℝ) i / q i) ≤
        (1 - lam) * ((ℙ'₀ : Fin d → ℝ) i * Real.log ((ℙ'₀ : Fin d → ℝ) i / (ℙ₀ : Fin d → ℝ) i))
          + lam * ((ℙ'₀ : Fin d → ℝ) i * L) := by
      intro i
      rcases (hP'nn i).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hP0pos : 0 < (ℙ₀ : Fin d → ℝ) i := by
          rcases (hP0nn i).eq_or_lt with h | h
          · exact absurd (hcond i h.symm) hpos.ne'
          · exact h
        set p := (ℙ'₀ : Fin d → ℝ) i
        set a := (ℙ₀ : Fin d → ℝ) i
        have hmi := hmpos i
        -- concavity of log
        have hconc : (1 - lam) * Real.log a + lam * Real.log (m i) ≤ Real.log (q i) := by
          have := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hP0pos)
            (Set.mem_Ioi.mpr hmi) (by linarith : 0 ≤ 1 - lam) hlam0.le (by ring)
          simpa [q, smul_eq_mul] using this
        have hlogm : Real.log (1 - η) + Real.log p ≤ Real.log (m i) := by
          rw [← Real.log_mul (by linarith) hpos.ne']
          exact Real.log_le_log (by have := mul_pos (by linarith : (0:ℝ) < 1 - η) hpos; linarith)
            (hmge i)
        rw [Real.log_div hpos.ne' (hqpos i).ne', Real.log_div hpos.ne' hP0pos.ne']
        have : Real.log p - Real.log (q i) ≤
            (1 - lam) * (Real.log p - Real.log a) + lam * L := by
          rw [hL]; nlinarith
        have := mul_le_mul_of_nonneg_left this hpos.le
        nlinarith
    have hsumq := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    have hs1 : ∑ i, (ℙ'₀ : Fin d → ℝ) i = 1 := ℙ'₀.2.2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul] at hsumq
    simp only [hs1, one_mul] at hsumq
    have : (1 - lam) * (∑ i, (ℙ'₀ : Fin d → ℝ) i *
        Real.log ((ℙ'₀ : Fin d → ℝ) i / (ℙ₀ : Fin d → ℝ) i)) + lam * L < r := by
      have h1 : (1 - lam) * (∑ i, (ℙ'₀ : Fin d → ℝ) i *
          Real.log ((ℙ'₀ : Fin d → ℝ) i / (ℙ₀ : Fin d → ℝ) i)) ≤ (1 - lam) * r :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
      have h2 : lam * L < lam * r := mul_lt_mul_of_pos_left hLr hlam0
      linarith
    exact_mod_cast lt_of_le_of_lt hsumq this
  · -- cost bound
    have hcq : cost γ x ⟨q, hq⟩ = (1 - lam) * cost γ x ℙ₀ + lam * cost γ x ⟨m, hm⟩ := by
      simp only [cost]
      show ∑ i, ((1 - lam) • (ℙ₀ : Fin d → ℝ) + lam • m) i * γ x i =
        (1 - lam) * ∑ i, (ℙ₀ : Fin d → ℝ) i * γ x i + lam * ∑ i, m i * γ x i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcq]
    have hdiff : cost γ x ℙ₀ - cost γ x ⟨m, hm⟩ ≤ K := le_abs_self _
    have hl2 : lam ≤ ε / (2 * (K + 1)) := min_le_right _ _
    have : lam * (K + 1) ≤ ε / 2 := by
      calc lam * (K + 1) ≤ ε / (2 * (K + 1)) * (K + 1) :=
            mul_le_mul_of_nonneg_right hl2 (by linarith)
        _ = ε / 2 := by have : K + 1 ≠ 0 := by linarith
                        field_simp
    nlinarith
end DROOptimal.Predictor

open DROOptimal.Predictor

theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) (x : ↥X) (ℙ'₀ ℙ₀ : Δ d) (h14 : relEntropy ℙ'₀ ℙ₀ ≤ (r : EReal))
    (hOpt : drPredictor γ r x ℙ'₀ = cost γ x ℙ₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ℙ₂ : Δ d, (∀ i, 0 < (ℙ₂ : Fin d → ℝ) i) ∧ relEntropy ℙ'₀ ℙ₂ < (r : EReal) ∧
      cost γ x ℙ₀ < cost γ x ℙ₂ + ε :=
  eq15_aux γ r hr x ℙ'₀ ℙ₀ h14 ε hε
