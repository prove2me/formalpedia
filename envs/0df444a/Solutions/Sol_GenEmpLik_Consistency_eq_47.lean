-- Prove2me | solution 1 for GenEmpLik.Consistency.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:59:41.586531+00:00
-- url     : https://prove2.me/submissions/fe9c57bb-96db-4213-87e6-02b05fbebcf6

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_VarianceRegularization_Expansion_empMean

set_option autoImplicit false

theorem conj_exps (ε : ℝ) (hε : 0 < ε) :
    (max 2 (1 + 1 / ε)).HolderConjugate (min 2 (1 + ε)) := by
  rw [Real.holderConjugate_iff]
  rcases le_total ε 1 with h | h
  · have h1 : 2 ≤ 1 + 1 / ε := by
      have : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
      linarith
    have h2 : 1 + ε ≤ 2 := by linarith
    rw [max_eq_right h1, min_eq_right h2]
    refine ⟨by linarith [show (0:ℝ) < 1 / ε by positivity], ?_⟩
    field_simp
    ring
  · have h1 : 1 + 1 / ε ≤ 2 := by
      have : 1 / ε ≤ 1 := by rw [div_le_iff₀ hε]; linarith
      linarith
    have h2 : 2 ≤ 1 + ε := by linarith
    rw [max_eq_left h1, min_eq_left h2]
    refine ⟨by norm_num, ?_⟩
    norm_num

theorem solution (f : ℝ → EReal) (ρ ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 0 < n)
    (z : Fin n → ℝ) (m : ℝ)
    (w : Fin n → ℝ) (hw : w ∈ PhiDivRobust.Counterpart.probUncertaintySet f
      (fun _ : Fin n => (1 : ℝ) / n) (ρ / n)) :
    |∑ i, w i * z i - m| ≤
        (1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| * |z i|
          + |VarianceRegularization.Expansion.empMean z - m| ∧
      (1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| * |z i|
          + |VarianceRegularization.Expansion.empMean z - m| ≤
        ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| ^ max 2 (1 + 1 / ε)) ^ (1 / max 2 (1 + 1 / ε))
          * ((1 / (n : ℝ)) * ∑ i, |z i| ^ min 2 (1 + ε)) ^ (1 / min 2 (1 + ε))
          + |VarianceRegularization.Expansion.empMean z - m| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hconj := conj_exps ε hε
  set r := max 2 (1 + 1 / ε) with hr
  set q := min 2 (1 + ε) with hq
  have hrq : 1 / r + 1 / q = 1 := by
    have := hconj.inv_add_inv_eq_one
    simpa [one_div] using this
  refine ⟨?_, ?_⟩
  · have key : ∑ i, w i * z i - m =
        (1 / (n : ℝ)) * ∑ i, ((n : ℝ) * w i - 1) * z i +
          (VarianceRegularization.Expansion.empMean z - m) := by
      unfold VarianceRegularization.Expansion.empMean
      simp only [sub_mul, Finset.sum_sub_distrib, one_mul, ← Finset.mul_sum]
      have : ∑ i, (n : ℝ) * w i * z i = (n : ℝ) * ∑ i, w i * z i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      field_simp
      ring
    rw [key]
    refine (abs_add_le _ _).trans ?_
    gcongr
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => (abs_mul _ _).le
  · refine add_le_add_left ?_ _
    have hH := Real.inner_le_Lp_mul_Lq Finset.univ (fun i => |(n : ℝ) * w i - 1|) (fun i => |z i|) hconj
    simp only [abs_abs] at hH
    have e1 : ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) =
        (1 / (n : ℝ)) ^ (1 / r) * (∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) :=
      Real.mul_rpow (by positivity) (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    have e2 : ((1 / (n : ℝ)) * ∑ i, |z i| ^ q) ^ (1 / q) =
        (1 / (n : ℝ)) ^ (1 / q) * (∑ i, |z i| ^ q) ^ (1 / q) :=
      Real.mul_rpow (by positivity) (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    have e3 : (1 / (n : ℝ)) ^ (1 / r) * (1 / (n : ℝ)) ^ (1 / q) = 1 / (n : ℝ) := by
      rw [← Real.rpow_add (by positivity), hrq, Real.rpow_one]
    rw [e1, e2]
    calc (1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| * |z i|
        ≤ (1 / (n : ℝ)) * ((∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) * (∑ i, |z i| ^ q) ^ (1 / q)) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
      _ = ((1 / (n : ℝ)) ^ (1 / r) * (1 / (n : ℝ)) ^ (1 / q)) *
            ((∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) * (∑ i, |z i| ^ q) ^ (1 / q)) := by rw [e3]
      _ = _ := by ring
