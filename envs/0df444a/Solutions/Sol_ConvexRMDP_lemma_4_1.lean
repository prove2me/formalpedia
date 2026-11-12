-- Prove2me | solution 1 for ConvexRMDP.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:06:56.169312+00:00
-- url     : https://prove2.me/submissions/c0935f03-e631-4bfd-a6a4-01ce425e5e93

import Definitions.Def_ConvexRMDP_kl

open ConvexRMDP

theorem solution {A : Type*} [Fintype A] (b : ℝ) (hb : 0 < b) (q₀ : A → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ A) (y : A → ℝ) :
    IsGreatest {t | ∃ q ∈ stdSimplex ℝ A, AbsCont q q₀ ∧ t = ∑ a, q a * y a - kl q q₀ / b}
      (Real.log (∑ a, q₀ a * Real.exp (b * y a)) / b) := by
  let Z : ℝ := ∑ a : A, q₀ a * Real.exp (b * y a)
  have hex_pos : ∃ a₀ : A, 0 < q₀ a₀ := by
    by_contra h
    push Not at h
    have hzero : ∀ a : A, q₀ a = 0 := fun a => le_antisymm (h a) (hq₀.1 a)
    have hsum0 : (∑ a : A, q₀ a) = 0 := Finset.sum_eq_zero fun a _ => hzero a
    linarith [hq₀.2]
  obtain ⟨a₀, ha₀⟩ := hex_pos
  have hZ_pos : 0 < Z := by
    refine lt_of_lt_of_le (mul_pos ha₀ (Real.exp_pos (b * y a₀))) ?_
    exact Finset.single_le_sum (fun a _ => mul_nonneg (hq₀.1 a) (Real.exp_pos (b * y a)).le)
      (Finset.mem_univ a₀)
  have hZ_ne : Z ≠ 0 := hZ_pos.ne'
  let qStar : A → ℝ := fun a => q₀ a * Real.exp (b * y a) / Z
  have hqStar_mem : qStar ∈ stdSimplex ℝ A := by
    refine ⟨fun a => div_nonneg (mul_nonneg (hq₀.1 a) (Real.exp_pos _).le) hZ_pos.le, ?_⟩
    dsimp [qStar]
    rw [← Finset.sum_div]
    exact div_self hZ_ne
  have hqStar_abs : AbsCont qStar q₀ := by
    intro a ha0
    simp [qStar, ha0]
  refine ⟨⟨qStar, hqStar_mem, hqStar_abs, ?_⟩, ?_⟩
  · have hterm : ∀ a : A,
        qStar a * y a - (qStar a * Real.log (qStar a / q₀ a)) / b =
          qStar a * (Real.log Z / b) := by
      intro a
      by_cases ha0 : q₀ a = 0
      · have hq0 : qStar a = 0 := by simp [qStar, ha0]
        simp [hq0]
      · have hdiv : qStar a / q₀ a = Real.exp (b * y a) / Z := by
          dsimp [qStar]
          field_simp [ha0, hZ_ne]
        rw [hdiv, Real.log_div (Real.exp_ne_zero _) hZ_ne, Real.log_exp]
        field_simp [hb.ne']
        ring
    have hsum_eq : ∑ a : A, qStar a * y a - kl qStar q₀ / b =
        ∑ a : A, (qStar a * y a - (qStar a * Real.log (qStar a / q₀ a)) / b) := by
      unfold kl
      rw [Finset.sum_div, Finset.sum_sub_distrib]
    rw [hsum_eq, Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_mul, hqStar_mem.2, one_mul]
  · rintro _ ⟨q, hq, habs, rfl⟩
    have hpoint : ∀ a : A,
        q a * (b * y a - Real.log Z) - q a * Real.log (q a / q₀ a) ≤ qStar a - q a := by
      intro a
      by_cases hqa0 : q a = 0
      · simp [hqa0, hqStar_mem.1 a]
      · have hqa_pos : 0 < q a := lt_of_le_of_ne (hq.1 a) (Ne.symm hqa0)
        have hq0a_ne : q₀ a ≠ 0 := fun h0 => hqa0 (habs a h0)
        have hq0a_pos : 0 < q₀ a := lt_of_le_of_ne (hq₀.1 a) (Ne.symm hq0a_ne)
        have hqStar_pos : 0 < qStar a :=
          div_pos (mul_pos hq0a_pos (Real.exp_pos _)) hZ_pos
        have hprod : (qStar a / q a) * (q a / q₀ a) = Real.exp (b * y a) / Z := by
          rw [div_mul_div_cancel₀ hqa_pos.ne']
          dsimp [qStar]
          field_simp [hq0a_pos.ne', hZ_ne]
        have hlog_sum : Real.log (qStar a / q a) + Real.log (q a / q₀ a) =
            b * y a - Real.log Z := by
          have h1 := congrArg Real.log hprod
          rw [Real.log_mul (div_pos hqStar_pos hqa_pos).ne' (div_pos hqa_pos hq0a_pos).ne',
            Real.log_div (Real.exp_ne_zero _) hZ_ne, Real.log_exp] at h1
          exact h1
        have hrew : q a * (b * y a - Real.log Z) - q a * Real.log (q a / q₀ a) =
            q a * Real.log (qStar a / q a) := by
          linarith [show q a * (Real.log (qStar a / q a) + Real.log (q a / q₀ a)) =
              q a * (b * y a - Real.log Z) by rw [hlog_sum]]
        rw [hrew]
        have hlog_le : Real.log (qStar a / q a) ≤ qStar a / q a - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hqStar_pos hqa_pos)
        calc q a * Real.log (qStar a / q a)
            ≤ q a * (qStar a / q a - 1) := mul_le_mul_of_nonneg_left hlog_le (hq.1 a)
          _ = qStar a - q a := by field_simp [hqa_pos.ne']
    have hsum_le : ∑ a : A, (q a * (b * y a - Real.log Z) - q a * Real.log (q a / q₀ a)) ≤
        ∑ a : A, (qStar a - q a) :=
      Finset.sum_le_sum fun a _ => hpoint a
    have hrhs0 : ∑ a : A, (qStar a - q a) = 0 := by
      rw [Finset.sum_sub_distrib, hqStar_mem.2, hq.2, sub_self]
    have hlhs : ∑ a : A, (q a * (b * y a - Real.log Z) - q a * Real.log (q a / q₀ a)) =
        b * (∑ a : A, q a * y a) - Real.log Z - kl q q₀ := by
      unfold kl
      have h1 : ∑ a : A, q a * (b * y a - Real.log Z) =
          b * (∑ a : A, q a * y a) - (∑ a : A, q a) * Real.log Z := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [Finset.sum_sub_distrib, h1, hq.2, one_mul]
    have hineq : b * (∑ a : A, q a * y a) - kl q q₀ ≤ Real.log Z := by
      linarith
    have hdiv_eq : ∑ a : A, q a * y a - kl q q₀ / b =
        (b * (∑ a : A, q a * y a) - kl q q₀) / b := by
      field_simp [hb.ne']
    rw [hdiv_eq]
    exact div_le_div_of_nonneg_right hineq hb.le
