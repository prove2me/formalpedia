-- Prove2me | solution 1 for BesbesZeevi.Nonparametric.fact1_JD_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:04:37.65634+00:00
-- url     : https://prove2.me/submissions/a56ddd4d-2239-4b7f-8d1a-ab484a039e20

import Mathlib
import Definitions.Def_BesbesZeevi_Nonparametric_Model

open MeasureTheory

open BesbesZeevi.Nonparametric in
theorem solution (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    0 < L.m * min T (x / L.M) ∧
      ∀ lam : ℝ → ℝ, L.Mem P lam → L.m * min T (x / L.M) ≤ JD P lam x T := by
  have hM := L.M_pos
  have hm := L.m_pos
  have hT'pos : 0 < min T (x / L.M) := lt_min hT (div_pos hx hM)
  refine ⟨mul_pos hm hT'pos, ?_⟩
  intro lam hlam
  set T' := min T (x / L.M) with hT'def
  obtain ⟨ps, hps, hrev⟩ := hlam.min_revenue
  let q : ℝ → ℝ := fun s => if s ≤ T' then ps else P.pinf
  have hT'mem : T' ∈ Set.Icc (0:ℝ) T := ⟨hT'pos.le, min_le_left _ _⟩
  have hlamq : (fun s => lam (q s)) = Set.indicator {s | s ≤ T'} (fun _ => lam ps) := by
    funext s
    simp only [q, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> simp [hlam.off]
  have hrevq : (fun s => q s * lam (q s)) = Set.indicator {s | s ≤ T'} (fun _ => ps * lam ps) := by
    funext s
    simp only [q, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> simp [hlam.off]
  have hlamM : lam ps ≤ L.M := (le_abs_self _).trans (hlam.bounded ps hps)
  have hfeas : FeasiblePath P lam x T q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
    · intro s _
      by_cases h : s ≤ T'
      · left; simp [q, h, hps]
      · right; simp [q, h]
    · rw [hlamq]
      constructor <;>
      · exact (integrable_const (lam ps)).indicator measurableSet_Iic
    · rw [hlamq, intervalIntegral.integral_indicator hT'mem]
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      calc T' * lam ps ≤ (x / L.M) * L.M := by
            apply mul_le_mul (min_le_right _ _) hlamM (hlam.nonneg _) (div_pos hx hM).le
        _ = x := by field_simp
  have hbdd : BddAbove (pathRevenue lam T '' {p | FeasiblePath P lam x T p}) := by
    refine ⟨P.pu * L.M * |T - 0|, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hs' : s ∈ Set.Icc 0 T := by
      rw [Set.uIoc_of_le hT.le] at hs
      exact ⟨hs.1.le, hs.2⟩
    rcases hp.2.1 s hs' with h | h
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |p s| ≤ P.pu := by
        rw [abs_of_pos (lt_of_lt_of_le P.pl_pos h.1)]; exact h.2
      exact mul_le_mul h1 (hlam.bounded _ h) (abs_nonneg _) (P.pl_pos.trans P.pl_lt_pu).le
    · rw [h, hlam.off]; simp
      exact mul_nonneg (P.pl_pos.trans P.pl_lt_pu).le hM.le
  have hmem : pathRevenue lam T q ∈ pathRevenue lam T '' {p | FeasiblePath P lam x T p} :=
    ⟨q, hfeas, rfl⟩
  have hval : pathRevenue lam T q = T' * (ps * lam ps) := by
    unfold pathRevenue
    rw [hrevq, intervalIntegral.integral_indicator hT'mem]
    simp
    ring
  calc L.m * T' ≤ T' * (ps * lam ps) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hrev hT'pos.le
    _ = pathRevenue lam T q := hval.symm
    _ ≤ JD P lam x T := le_csSup hbdd hmem
