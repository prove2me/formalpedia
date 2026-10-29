-- Prove2me | solution 1 for CloseGaps.DPA.lemma_7
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:10:58.691266+00:00
-- url     : https://prove2.me/submissions/09671d0d-d1f8-40cf-bc8f-1c34f6c40b99

import Mathlib
import Definitions.Def_CloseGaps_DPA_RevenueEvents

open MeasureTheory Set CloseGaps.DPA
open scoped Classical

theorem s225cg_kappa : (⌊kappaU 3 1⌋₊ : ℝ) ≠ kappaU 3 1 := by
  have hk : kappaU 3 1 = (3:ℝ) ^ (1/10 : ℝ) * Real.log 3 := by
    simp [kappaU]
  have h1 : 1 < (3:ℝ) ^ (1/10 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have h2 : (3:ℝ) ^ (1/10 : ℝ) < 1.3 := by
    by_contra h
    push Not at h
    have : (1.3:ℝ) ^ 10 ≤ ((3:ℝ) ^ (1/10 : ℝ)) ^ 10 := pow_le_pow_left₀ (by norm_num) h 10
    rw [← Real.rpow_natCast ((3:ℝ) ^ (1/10 : ℝ)) 10, ← Real.rpow_mul (by norm_num)] at this
    norm_num at this
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have h4 : Real.log 3 < 1.5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have e1 := Real.add_one_le_exp (0.75 : ℝ)
    have : Real.exp 1.5 = Real.exp 0.75 * Real.exp 0.75 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  rw [hk]
  have hlo : 1 < (3:ℝ) ^ (1/10 : ℝ) * Real.log 3 := by nlinarith
  have hhi : (3:ℝ) ^ (1/10 : ℝ) * Real.log 3 < 2 := by nlinarith
  have hf : ⌊(3:ℝ) ^ (1/10 : ℝ) * Real.log 3⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]; constructor <;> push_cast <;> linarith
  rw [hf]; push_cast; linarith

theorem s225cg_none (a : Market) (lam : ℝ → ℝ) (x : ℝ) (E : Noise) :
    ∀ i, uStage a lam 3 x E i = none := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simp only [uStage, if_true]
      unfold makeStage
      simp only
      split_ifs with hc
      · exact absurd hc.1 s225cg_kappa
      · rfl
    · simp only [uStage, if_neg h.ne', ih, Option.bind_none]

theorem s225cg_class : InClass ⟨1, 1, 2, 2⟩ ⟨0, 1⟩ (1/2) 1 (fun p => 1 - p) := by
  have hd : deriv (fun z : ℝ => z * (1 - z)) = fun z => 1 - 2 * z := by
    ext z
    have : HasDerivAt (fun z : ℝ => z * (1 - z)) (1 * (1 - z) + z * (0 - 1)) z :=
      (hasDerivAt_id' z).mul ((hasDerivAt_const z 1).sub (hasDerivAt_id' z))
    rw [this.deriv]; ring
  have hd2 : deriv (fun z : ℝ => 1 - 2 * z) = fun _ => -2 := by
    ext z
    have : HasDerivAt (fun z : ℝ => 1 - 2 * z) (0 - 2 * 1) z :=
      (hasDerivAt_const z 1).sub ((hasDerivAt_id' z).const_mul 2)
    rw [this.deriv]; norm_num
  refine ⟨⟨?_, ?_, ?_, fun z => 1 - z, ?_, ?_, ?_⟩, ?_⟩
  · intro p _ q _ hpq; simp only; linarith
  · intro p hp
    simp only [Set.mem_Icc] at hp
    exact ⟨by linarith, by rw [abs_le]; constructor <;> linarith⟩
  · intro p hp q hq
    simp only [Set.mem_Icc] at hp hq
    constructor
    · rw [show (1 - p) - (1 - q) = -(p - q) by ring, abs_neg, one_mul]
    · rw [show p * (1 - p) - q * (1 - q) = (p - q) * (1 - p - q) by ring, abs_mul, one_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith)
  · intro p _; simp
  · intro q _ z _
    rw [show (1 - q) - (1 - z) = -(q - z) by ring, abs_neg, one_mul]
  · intro q _
    refine ⟨by fun_prop, ?_, ?_, ?_⟩
    · rw [hd]; fun_prop
    · rw [hd, hd2]
    · rw [hd, hd2]
  · have hu : uOpt ⟨0, 1⟩ (fun p => 1 - p) = 1/2 := by
      show sSup {p ∈ Set.Icc (0:ℝ) 1 | ∀ q ∈ Set.Icc (0:ℝ) 1, q * (1 - q) ≤ p * (1 - p)} = 1/2
      have : {p ∈ Set.Icc (0:ℝ) 1 | ∀ q ∈ Set.Icc (0:ℝ) 1, q * (1 - q) ≤ p * (1 - p)} = {1/2} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
        constructor
        · rintro ⟨-, h⟩
          have := h (1/2) ⟨by norm_num, by norm_num⟩
          nlinarith [sq_nonneg (p - 1/2)]
        · rintro rfl
          exact ⟨⟨by norm_num, by norm_num⟩, fun q _ => by nlinarith [sq_nonneg (q - 1/2)]⟩
      rw [this, csSup_singleton]
    have hc : cOpt ⟨0, 1⟩ (1/2) 1 (fun p => 1 - p) = 1/2 := by
      show sSup {p ∈ Set.Icc (0:ℝ) 1 | ∀ q ∈ Set.Icc (0:ℝ) 1,
          |1 - p - 1/2/1| ≤ |1 - q - 1/2/1|} = 1/2
      have : {p ∈ Set.Icc (0:ℝ) 1 | ∀ q ∈ Set.Icc (0:ℝ) 1,
          |1 - p - 1/2/1| ≤ |1 - q - 1/2/1|} = {1/2} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
        constructor
        · rintro ⟨-, h⟩
          have := h (1/2) ⟨by norm_num, by norm_num⟩
          norm_num at this
          linarith
        · rintro rfl
          exact ⟨⟨by norm_num, by norm_num⟩, fun q _ => by norm_num⟩
      rw [this, csSup_singleton]
    show max _ _ ∈ _
    rw [hu, hc]; norm_num

theorem solution : ¬ (∀ (c : Coefficients) (hc : c.Positive) (x : ℝ) (hx : 0 < x),
    ∃ C : ℝ, 0 < C ∧
    ∀ a : Market, a.Valid → a.hi - a.lo = 1 →
    ∃ π : ℝ → PriceRule, ∀ n : ℝ, 3 ≤ n →
    ∀ lam : ℝ → ℝ, InClass c a x 1 lam →
    ∃ N : StageCounts, Experiment a lam n x (π n) N ∧
      ∀ l ∈ Icc 1 N.Nu,
        n * dOpt a x 1 lam * lam (dOpt a x 1 lam) * (1 - timeU n l - timeC n N.Nc) *
          probability (B a lam n x N l) - C * n * tauU n 1 * Real.log n ≤
            ∫ E, revenue7 a lam n x N l E ∂clockLaw) := by
  intro H
  obtain ⟨C, -, hall⟩ := H ⟨1, 1, 2, 2⟩ (by norm_num [Coefficients.Positive]) (1/2) (by norm_num)
  obtain ⟨π, hπ⟩ := hall ⟨0, 1⟩ (by norm_num [Market.Valid]) (by norm_num)
  obtain ⟨N, hE, -⟩ := hπ 3 le_rfl (fun p => 1 - p) s225cg_class
  have hexp : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1:ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos
  have : IsProbabilityMeasure clockLaw := by unfold clockLaw; infer_instance
  obtain ⟨E, hE1, -⟩ := hE.2.1.exists
  obtain ⟨⟨-, ⟨s, hs, -⟩, -⟩, -⟩ := hE1
  rw [s225cg_none] at hs
  exact absurd hs (by simp)
