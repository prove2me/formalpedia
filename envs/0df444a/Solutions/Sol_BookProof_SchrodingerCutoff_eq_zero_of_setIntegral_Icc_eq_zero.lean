-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.eq_zero_of_setIntegral_Icc_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:01:23.694452+00:00
-- url     : https://prove2.me/submissions/9658c9cf-8d2f-4162-a6e7-de1e29a4e1e3

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.eq_zero_of_setIntegral_Icc_eq_zero
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x)
    (h : ∀ n : ℕ, ∫ x in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), f x = 0) :
    f = 0 := by
  have key : ∀ n : ℕ, ∀ᵐ x, x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) → f x = 0 := by
    intro n
    have hres := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => h0 x) hf.integrableOn_Icc).mp (h n)
    exact (ae_restrict_iff' measurableSet_Icc).mp hres
  have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) → f x = 0 :=
    ae_all_iff.mpr key
  have hae : f =ᵐ[volume] 0 := by
    filter_upwards [hall] with x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact hx n ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  exact (Continuous.ae_eq_iff_eq volume hf continuous_const).mp hae
