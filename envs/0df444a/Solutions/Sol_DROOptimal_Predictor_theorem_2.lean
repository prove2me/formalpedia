-- Prove2me | solution 1 for DROOptimal.Predictor.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:42:04.103225+00:00
-- url     : https://prove2.me/submissions/e2a90ced-45f9-43eb-b8bc-b9c07865dc6f

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

open DROOptimal.Predictor

namespace DROm4Thm2

/-- Π_t f(ω_t) = Π_i f(i)^{n_i(ω)}. -/
lemma prod_eq_prod_pow {d T : ℕ} (f : Fin d → ℝ) (ω : Fin T → Fin d) :
    ∏ t, f (ω t) = ∏ i, f i ^ (Finset.univ.filter (fun t => ω t = i)).card := by
  rw [← Finset.prod_fiberwise Finset.univ ω (fun t => f (ω t))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])

lemma sum_prod_eq {d T : ℕ} (q : Fin d → ℝ) :
    ∑ ω : Fin T → Fin d, ∏ t, q (ω t) = (∑ i, q i) ^ T := by
  have := Finset.prod_univ_sum (t := fun (_ : Fin T) => (Finset.univ : Finset (Fin d)))
    (f := fun _ i => q i)
  simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at this
  exact this.symm

lemma pointwise {d T : ℕ} (hT : 1 ≤ T) (ℙ : Δ d) (s : ℝ) (ω : Fin T → Fin d)
    (h : empiricalVec ω ∈ stdSimplex ℝ (Fin d))
    (hs : (s : EReal) ≤ relEntropy ⟨empiricalVec ω, h⟩ ℙ) :
    ∏ t, (ℙ : Fin d → ℝ) (ω t) ≤
      Real.exp (-((T : ℝ) * s)) * ∏ t, empiricalVec ω (ω t) := by
  classical
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set n : Fin d → ℕ := fun i => (Finset.univ.filter (fun t => ω t = i)).card with hn
  have hQ : ∀ i, empiricalVec ω i = (n i : ℝ) / T := fun i => rfl
  rw [prod_eq_prod_pow, prod_eq_prod_pow]
  unfold relEntropy at hs
  split_ifs at hs with hc
  · -- finite entropy
    have hs' : s ≤ ∑ i, empiricalVec ω i * Real.log (empiricalVec ω i / (ℙ : Fin d → ℝ) i) := by
      exact_mod_cast hs
    have key : ∀ i, (ℙ : Fin d → ℝ) i ^ n i = empiricalVec ω i ^ n i *
        Real.exp (-((T : ℝ) * (empiricalVec ω i *
          Real.log (empiricalVec ω i / (ℙ : Fin d → ℝ) i)))) := by
      intro i
      rcases Nat.eq_zero_or_pos (n i) with h0 | hpos
      · have : empiricalVec ω i = 0 := by rw [hQ, h0]; simp
        change (ℙ : Fin d → ℝ) i ^ n i = _
        rw [h0, this]; simp
      · have hQpos : 0 < empiricalVec ω i := by
          rw [hQ]; exact div_pos (by exact_mod_cast hpos) hTpos
        have hPpos : 0 < (ℙ : Fin d → ℝ) i := by
          rcases (ℙ.2.1 i).lt_or_eq with hlt | heq
          · exact hlt
          · exact absurd (hc i heq.symm) hQpos.ne'
        have hTQ : (T : ℝ) * empiricalVec ω i = n i := by
          rw [hQ]; field_simp
        have : -((T : ℝ) * (empiricalVec ω i *
            Real.log (empiricalVec ω i / (ℙ : Fin d → ℝ) i))) =
            (n i : ℝ) * Real.log ((ℙ : Fin d → ℝ) i / empiricalVec ω i) := by
          rw [← mul_assoc, hTQ, Real.log_div hPpos.ne' hQpos.ne',
            Real.log_div hQpos.ne' hPpos.ne']
          ring
        rw [this, Real.exp_nat_mul, Real.exp_log (div_pos hPpos hQpos), ← mul_pow,
          mul_div_cancel₀ _ hQpos.ne']
    rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, ← Real.exp_sum,
      mul_comm]
    apply mul_le_mul_of_nonneg_right _
      (Finset.prod_nonneg (fun i _ => pow_nonneg (h.1 i) _))
    apply Real.exp_le_exp.mpr
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hs' hTpos.le]
  · -- infinite entropy: some i with ℙ i = 0 < Q i
    push Not at hc
    obtain ⟨i, hPi, hQi⟩ := hc
    have hni : n i ≠ 0 := by
      intro h0; apply hQi; change empiricalVec ω i = 0; rw [hQ]; simp [h0]
    have : ∏ j, (ℙ : Fin d → ℝ) j ^ n j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hPi]; exact zero_pow hni)
    rw [this]
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun j _ => pow_nonneg (h.1 j) _))

end DROm4Thm2

open DROm4Thm2 in
theorem solution {d : ℕ} (ℙ : Δ d) (D : Set (Δ d)) (hD : MeasurableSet D)
    (T : ℕ) (hT : 1 ≤ T) (s : ℝ)
    (hs : (s : EReal) ≤ ⨅ ℙ' ∈ D, relEntropy ℙ' ℙ) :
    empProb ℙ T D ≤ ((T : ℝ) + 1) ^ d * Real.exp (-((T : ℝ) * s)) := by
  classical
  let cnt : (Fin T → Fin d) → (Fin d → Fin (T + 1)) := fun ω i =>
    ⟨(Finset.univ.filter (fun t => ω t = i)).card,
      Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩
  have hTnn : (0 : ℝ) ≤ T := by positivity
  have inner : ∀ k : Fin d → Fin (T + 1),
      ∑ ω ∈ Finset.univ.filter (fun ω => cnt ω = k),
        (if EmpiricalIn ω D then ∏ t, (ℙ : Fin d → ℝ) (ω t) else 0) ≤
        Real.exp (-((T : ℝ) * s)) := by
    intro k
    by_cases hex : ∃ ω0, cnt ω0 = k ∧ EmpiricalIn ω0 D
    · obtain ⟨ω0, hk0, h0, hD0⟩ := hex
      have hemp : ∀ ω, cnt ω = k → empiricalVec ω = empiricalVec ω0 := by
        intro ω hk
        funext i
        have := congrArg (fun f : Fin d → Fin (T + 1) => ((f i : Fin (T + 1)) : ℕ))
          (hk.trans hk0.symm)
        simp only [cnt] at this
        unfold empiricalVec
        rw [this]
      calc ∑ ω ∈ Finset.univ.filter (fun ω => cnt ω = k),
            (if EmpiricalIn ω D then ∏ t, (ℙ : Fin d → ℝ) (ω t) else 0)
          ≤ ∑ ω ∈ Finset.univ.filter (fun ω => cnt ω = k),
              Real.exp (-((T : ℝ) * s)) * ∏ t, empiricalVec ω0 (ω t) := by
            apply Finset.sum_le_sum
            intro ω hω
            have hk : cnt ω = k := (Finset.mem_filter.mp hω).2
            split_ifs with hE
            · obtain ⟨h, hDω⟩ := hE
              have := pointwise hT ℙ s ω h (hs.trans (iInf₂_le _ hDω))
              rw [hemp ω hk] at this
              exact this
            · exact mul_nonneg (Real.exp_pos _).le
                (Finset.prod_nonneg (fun t _ => h0.1 _))
        _ ≤ ∑ ω : Fin T → Fin d, Real.exp (-((T : ℝ) * s)) * ∏ t, empiricalVec ω0 (ω t) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ω _ _ => mul_nonneg (Real.exp_pos _).le
                (Finset.prod_nonneg (fun t _ => h0.1 _)))
        _ = Real.exp (-((T : ℝ) * s)) := by
            rw [← Finset.mul_sum, sum_prod_eq, h0.2, one_pow, mul_one]
    · push Not at hex
      rw [Finset.sum_eq_zero]
      · exact (Real.exp_pos _).le
      · intro ω hω
        rw [if_neg (hex ω (Finset.mem_filter.mp hω).2)]
  unfold empProb pathProb
  rw [← Finset.sum_fiberwise Finset.univ cnt]
  calc ∑ k : Fin d → Fin (T + 1), ∑ ω ∈ Finset.univ.filter (fun ω => cnt ω = k),
        (if EmpiricalIn ω D then ∏ t, (ℙ : Fin d → ℝ) (ω t) else 0)
      ≤ ∑ _k : Fin d → Fin (T + 1), Real.exp (-((T : ℝ) * s)) :=
        Finset.sum_le_sum (fun k _ => inner k)
    _ = ((T : ℝ) + 1) ^ d * Real.exp (-((T : ℝ) * s)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
