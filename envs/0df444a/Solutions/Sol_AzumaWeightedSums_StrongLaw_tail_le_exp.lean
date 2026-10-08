-- Prove2me | solution 1 for AzumaWeightedSums.StrongLaw.tail_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:38:47.180871+00:00
-- url     : https://prove2.me/submissions/d8257787-0f5b-4259-91da-923464643a02

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG

set_option autoImplicit false

namespace AzumaTailAux2eeb

open MeasureTheory ProbabilityTheory

lemma exp_mul_le_cosh_add {s x : ℝ} (hx : |x| ≤ 1) :
    Real.exp (s * x) ≤ Real.cosh s + x * Real.sinh s := by
  have h1 : -1 ≤ x := by linarith [neg_abs_le x]
  have h2 : x ≤ 1 := by linarith [le_abs_self x]
  have ha : 0 ≤ (1 + x) / 2 := by linarith
  have hb : 0 ≤ (1 - x) / 2 := by linarith
  have hab : (1 + x) / 2 + (1 - x) / 2 = 1 := by ring
  have := convexOn_exp.2 (Set.mem_univ s) (Set.mem_univ (-s)) ha hb hab
  simp only [smul_eq_mul] at this
  rw [show (1 + x) / 2 * s + (1 - x) / 2 * -s = s * x by ring] at this
  rw [Real.cosh_eq, Real.sinh_eq]
  linear_combination this

lemma norm_exp_le {t S B : ℝ} (h : |S| ≤ B) :
    ‖Real.exp (t * S)‖ ≤ Real.exp (|t| * B) := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg t))

theorem mgf_step {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1) (c : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (fun ω => ∑ j ∈ Finset.Icc 1 n, c j * x j ω) ∧
      (∀ᵐ ω ∂μ, |∑ j ∈ Finset.Icc 1 n, c j * x j ω| ≤ ∑ j ∈ Finset.Icc 1 n, |c j|) ∧
      ∫ ω, Real.exp (t * ∑ j ∈ Finset.Icc 1 n, c j * x j ω) ∂μ
        ≤ Real.exp ((∑ j ∈ Finset.Icc 1 n, c j ^ 2) * t ^ 2 / 2) := by
  induction n with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt, zero_lt_one,
      Finset.sum_empty]
    refine ⟨stronglyMeasurable_const, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨hm, hb, hi⟩ := ih
    have hsplit : ∀ ω, ∑ j ∈ Finset.Icc 1 (n+1), c j * x j ω
        = (∑ j ∈ Finset.Icc 1 n, c j * x j ω) + c (n+1) * x (n+1) ω :=
      fun ω => Finset.sum_Icc_succ_top (by omega) _
    have hsplit2 : ∑ j ∈ Finset.Icc 1 (n+1), c j ^ 2
        = ∑ j ∈ Finset.Icc 1 n, c j ^ 2 + c (n+1) ^ 2 := Finset.sum_Icc_succ_top (by omega) _
    have hsplit3 : ∑ j ∈ Finset.Icc 1 (n+1), |c j|
        = ∑ j ∈ Finset.Icc 1 n, |c j| + |c (n+1)| := Finset.sum_Icc_succ_top (by omega) _
    obtain ⟨hxm, hxi, hxc⟩ := hx (n+1) (by omega)
    simp only [Nat.add_sub_cancel] at hxc
    have hxb := hbd (n+1) (by omega)
    set S : Ω → ℝ := fun ω => ∑ j ∈ Finset.Icc 1 n, c j * x j ω with hS
    set B := ∑ j ∈ Finset.Icc 1 n, |c j| with hB
    refine ⟨?_, ?_, ?_⟩
    · have : (fun ω => ∑ j ∈ Finset.Icc 1 (n+1), c j * x j ω)
          = fun ω => S ω + c (n+1) * x (n+1) ω := funext hsplit
      rw [this]
      exact (hm.mono (ℱ.mono (Nat.le_succ n))).add (hxm.const_mul _)
    · filter_upwards [hb, hxb] with ω h1 h2
      rw [hsplit, hsplit3]
      calc |S ω + c (n+1) * x (n+1) ω| ≤ |S ω| + |c (n+1) * x (n+1) ω| := abs_add_le _ _
        _ ≤ B + |c (n+1)| := add_le_add h1
            (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2)
    · have hfm : StronglyMeasurable[ℱ n] (fun ω => Real.exp (t * S ω)) :=
        Real.continuous_exp.comp_stronglyMeasurable (hm.const_mul t)
      have hfb : ∀ᵐ ω ∂μ, ‖Real.exp (t * S ω)‖ ≤ Real.exp (|t| * B) := by
        filter_upwards [hb] with ω h1 using norm_exp_le h1
      have hfi : Integrable (fun ω => Real.exp (t * S ω)) μ :=
        Integrable.of_bound (hfm.mono (ℱ.le n)).aestronglyMeasurable _ hfb
      have hxm0 : StronglyMeasurable (x (n+1)) := hxm.mono (ℱ.le (n+1))
      set s := t * c (n+1) with hs
      have hg1 : Integrable (fun ω => Real.exp (t * S ω) * Real.exp (s * x (n+1) ω)) μ := by
        refine Integrable.of_bound ((hfm.mono (ℱ.le n)).aestronglyMeasurable.mul
          (Real.continuous_exp.comp_stronglyMeasurable (hxm0.const_mul s)).aestronglyMeasurable)
          (Real.exp (|t| * B) * Real.exp (|s| * 1)) ?_
        filter_upwards [hfb, hxb] with ω h1 h2
        rw [norm_mul]
        exact mul_le_mul h1 (norm_exp_le h2) (norm_nonneg _) (Real.exp_pos _).le
      have hfx : Integrable (fun ω => Real.exp (t * S ω) * x (n+1) ω) μ := by
        refine Integrable.of_bound ((hfm.mono (ℱ.le n)).aestronglyMeasurable.mul
          hxm0.aestronglyMeasurable) (Real.exp (|t| * B) * 1) ?_
        filter_upwards [hfb, hxb] with ω h1 h2
        rw [norm_mul, Real.norm_eq_abs (x (n+1) ω)]
        exact mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
      have h0 : ∫ ω, Real.exp (t * S ω) * x (n+1) ω ∂μ = 0 := by
        have h := condExp_stronglyMeasurable_mul_of_bound (ℱ.le n) hfm hxi _ hfb
        calc ∫ ω, Real.exp (t * S ω) * x (n+1) ω ∂μ
            = ∫ ω, (μ[(fun ω => Real.exp (t * S ω)) * x (n+1) | ℱ n]) ω ∂μ :=
              (integral_condExp (ℱ.le n)).symm
          _ = ∫ ω, (0:ℝ) ∂μ := by
              refine integral_congr_ae (h.trans ?_)
              filter_upwards [hxc] with ω hω
              simp [Pi.mul_apply, hω]
          _ = 0 := by simp
      have heq : (fun ω => Real.exp (t * ∑ j ∈ Finset.Icc 1 (n+1), c j * x j ω))
          = fun ω => Real.exp (t * S ω) * Real.exp (s * x (n+1) ω) := by
        funext ω
        rw [hsplit, ← Real.exp_add]
        congr 1
        rw [hs]; ring
      rw [heq]
      calc ∫ ω, Real.exp (t * S ω) * Real.exp (s * x (n+1) ω) ∂μ
          ≤ ∫ ω, Real.exp (t * S ω) * (Real.cosh s + x (n+1) ω * Real.sinh s) ∂μ := by
            refine integral_mono_ae hg1 ?_ ?_
            · have : (fun ω => Real.exp (t * S ω) * (Real.cosh s + x (n+1) ω * Real.sinh s))
                  = fun ω => Real.cosh s * Real.exp (t * S ω)
                    + Real.sinh s * (Real.exp (t * S ω) * x (n+1) ω) := by
                funext ω; ring
              rw [this]
              exact (hfi.const_mul _).add (hfx.const_mul _)
            · filter_upwards [hxb] with ω h2
              exact mul_le_mul_of_nonneg_left (exp_mul_le_cosh_add h2) (Real.exp_pos _).le
        _ = Real.cosh s * ∫ ω, Real.exp (t * S ω) ∂μ := by
            have : (fun ω => Real.exp (t * S ω) * (Real.cosh s + x (n+1) ω * Real.sinh s))
                = fun ω => Real.cosh s * Real.exp (t * S ω)
                  + Real.sinh s * (Real.exp (t * S ω) * x (n+1) ω) := by
              funext ω; ring
            rw [this, integral_add (hfi.const_mul _) (hfx.const_mul _), integral_const_mul,
              integral_const_mul, h0]
            ring
        _ ≤ Real.exp (s ^ 2 / 2) * Real.exp ((∑ j ∈ Finset.Icc 1 n, c j ^ 2) * t ^ 2 / 2) :=
            mul_le_mul (Real.cosh_le_exp_half_sq s) hi
              (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
        _ = Real.exp ((∑ j ∈ Finset.Icc 1 (n+1), c j ^ 2) * t ^ 2 / 2) := by
            rw [← Real.exp_add, hsplit2, hs]
            congr 1
            ring

end AzumaTailAux2eeb

open MeasureTheory in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (N : ℕ) (c : ℕ → ℝ) (hc : 0 < ∑ j ∈ Finset.Icc 1 N, c j ^ 2)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ.real {ω | lam < ∑ j ∈ Finset.Icc 1 N, c j * x j ω}
      ≤ Real.exp (-lam ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N, c j ^ 2)) := by
  let cV : NNReal := ⟨∑ j ∈ Finset.Icc 1 N, c j ^ 2, hc.le⟩
  have hsub : ProbabilityTheory.HasSubgaussianMGF
      (fun ω => ∑ j ∈ Finset.Icc 1 N, c j * x j ω) cV μ := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · obtain ⟨h1, h2, -⟩ := AzumaTailAux2eeb.mgf_step ℱ x hx hbd c t N
      refine Integrable.of_bound
        (Real.continuous_exp.comp_stronglyMeasurable
          ((h1.mono (ℱ.le N)).const_mul t)).aestronglyMeasurable
        (Real.exp (|t| * ∑ j ∈ Finset.Icc 1 N, |c j|)) ?_
      filter_upwards [h2] with ω h using AzumaTailAux2eeb.norm_exp_le h
    · obtain ⟨-, -, h3⟩ := AzumaTailAux2eeb.mgf_step ℱ x hx hbd c t N
      exact h3
  calc μ.real {ω | lam < ∑ j ∈ Finset.Icc 1 N, c j * x j ω}
      ≤ μ.real {ω | lam ≤ ∑ j ∈ Finset.Icc 1 N, c j * x j ω} :=
        measureReal_mono (fun ω (h : lam < _) => show lam ≤ _ from le_of_lt h)
    _ ≤ Real.exp (-lam ^ 2 / (2 * cV)) := hsub.measure_ge_le hlam
    _ = Real.exp (-lam ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N, c j ^ 2)) := rfl
