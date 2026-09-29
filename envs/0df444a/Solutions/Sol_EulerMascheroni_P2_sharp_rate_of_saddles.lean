-- Prove2me | solution 1 for EulerMascheroni.P2.sharp_rate_of_saddles
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:09:29.177436+00:00
-- url     : https://prove2.me/submissions/96630c2b-fd58-45b4-9e87-e4c0f8370799

import Theorems.Thm_EulerMascheroni_P2_relative_asymptotic
import Theorems.Thm_EulerMascheroni_P2_model_rate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Filter Topology
open EulerMascheroni.P2

/-- The sharp, zero-safe error rate follows from saddle limits and recurring
noncancellation of the explicit phase. Both outstanding analytic inputs are explicit. -/
theorem solution (h : SaddleLimits)
    (hphase : ∃ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ |Real.sin (phase (n+1))|) :
    SharpRate := by
  obtain ⟨w, hw, heq⟩ := relative_asymptotic h
  let A : ℕ → ℝ := fun n => fModel (n+1) / qModel (n+1)
  have hspos (n : ℕ) : 0 < scale (n+1) := by unfold scale; positivity
  have hA (n : ℕ) : 0 < A n := by
    dsimp [A]
    have hs := hspos n
    unfold fModel qModel
    positivity
  have ht : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun n : ℕ => scale (n+1)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/5)).comp ht
  have hg : Tendsto (fun n => Real.log (A n) / scale (n+1)) atTop (nhds (-rate)) :=
    model_rate
  have haw : Tendsto (fun n => |w n|) atTop (nhds 0) := by simpa using hw.abs
  have hew : ∀ᶠ n in atTop, |w n| < 1/4 :=
    haw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))
  intro ε hε
  have hε2 : (0 : ℝ) < ε/2 := by linarith
  have hlu : ∀ᶠ n in atTop, Real.log (A n) / scale (n+1) < -rate + ε/2 :=
    hg.eventually (gt_mem_nhds (by linarith))
  have hll : ∀ᶠ n in atTop, -rate-ε/2 < Real.log (A n) / scale (n+1) :=
    hg.eventually (lt_mem_nhds (by linarith))
  have hgain : ∀ᶠ n in atTop, Real.log 4 < (ε/2) * scale (n+1) := by
    filter_upwards [hs.eventually (eventually_gt_atTop (Real.log 4 / (ε/2)))] with n hn
    exact (div_lt_iff₀ hε2).mp hn |>.trans_eq (mul_comm _ _)
  constructor
  · filter_upwards [heq, hew, hlu, hgain] with n hn hwn hgn hgain_n
    have hgn' := (div_lt_iff₀ (hspos n)).mp hgn
    have hsine := Real.abs_sin_le_one (phase (n+1))
    have hpert : |Real.sin (phase (n+1)) + w n| ≤ 4 := by
      have := abs_add_le (Real.sin (phase (n+1))) (w n)
      linarith
    change Real.eulerMascheroniConstant - (P (n+1) : ℝ) / (Q (n+1) : ℝ) =
      A n * (Real.sin (phase (n+1)) + w n) at hn
    rw [hn, abs_mul, abs_of_pos (hA n)]
    calc
      A n * |Real.sin (phase (n+1)) + w n| ≤ 4 * A n := by nlinarith [hA n]
      _ = Real.exp (Real.log (4 * A n)) :=
        (Real.exp_log (mul_pos (by norm_num) (hA n))).symm
      _ ≤ Real.exp ((-rate+ε) * scale (n+1)) := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_mul (by norm_num) (hA n).ne']
        nlinarith
  · apply (hphase.and_eventually (heq.and (hew.and (hll.and hgain)))).mono
    intro n hn
    rcases hn with ⟨hpn, hen, hwn, hgn, hgain_n⟩
    have hgn' := (lt_div_iff₀ (hspos n)).mp hgn
    have hpert : (1/4 : ℝ) ≤ |Real.sin (phase (n+1)) + w n| := by
      have hab : |Real.sin (phase (n+1))| ≤
          |Real.sin (phase (n+1)) + w n| + |w n| := by
        simpa using abs_sub_le (Real.sin (phase (n+1)) + w n) 0 (w n)
      linarith
    change Real.eulerMascheroniConstant - (P (n+1) : ℝ) / (Q (n+1) : ℝ) =
      A n * (Real.sin (phase (n+1)) + w n) at hen
    rw [hen, abs_mul, abs_of_pos (hA n)]
    calc
      Real.exp ((-rate-ε) * scale (n+1)) ≤ Real.exp (Real.log (A n / 4)) := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_div (hA n).ne' (by norm_num)]
        nlinarith
      _ = A n / 4 := Real.exp_log (div_pos (hA n) (by norm_num))
      _ ≤ A n * |Real.sin (phase (n+1)) + w n| := by nlinarith [hA n]

#print axioms solution
