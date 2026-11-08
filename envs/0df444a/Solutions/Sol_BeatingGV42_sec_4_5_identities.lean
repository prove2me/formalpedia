-- Prove2me | solution 1 for BeatingGV42.sec_4_5_identities
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:31:56.345608+00:00
-- url     : https://prove2.me/submissions/9c17d797-54a1-4eb4-8ef0-549e8942987f

import Mathlib
import Definitions.Def_BeatingGV42_Hq
import Definitions.Def_BeatingGV42_Psi
import Definitions.Def_BeatingGV42_rateR
import Definitions.Def_BeatingGV42_aGV
import Definitions.Def_BeatingGV42_Fgap

set_option autoImplicit false

open BeatingGV42 in
theorem solution (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    rateR 49 42 (aGV δ) = 1 - Hq 42 δ ∧
    (∀ a : ℝ, Psi 49 42 a (1 / 49) δ =
      Real.binEntropy δ + δ * Real.log 41 - (7 / 6 - a) * Real.log 49) ∧
    Psi 49 42 (aGV δ) (1 / 49) δ = 0 ∧
    HasDerivAt (fun t => Psi 49 42 (aGV δ) t δ) (49 * (49 / 48 * (1 - δ) - aGV δ)) (1 / 49) ∧
    49 * (49 / 48 * (1 - δ) - aGV δ) = 49 / Real.log 49 * Fgap δ := by
  have h7 : Real.sqrt (49 : ℝ) = 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hL49 : Real.log 49 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hL42 : Real.log 42 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hinv : Real.log (1 / 49 : ℝ) = -Real.log 49 := by rw [one_div, Real.log_inv]
  have h48 : Real.log (1 - 1 / 49 : ℝ) = Real.log 48 - Real.log 49 := by
    rw [show (1 : ℝ) - 1 / 49 = 48 / 49 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  have h41 : Real.log (((42 : ℝ) - 1) / ((49 : ℝ) - 1)) = Real.log 41 - Real.log 48 := by
    rw [show (42 : ℝ) - 1 = 41 by norm_num, show (49 : ℝ) - 1 = 48 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have hq41 : ((((42 : ℕ) : ℤ) - 1 : ℤ) : ℝ) = 41 := by norm_num
  have hPsi : ∀ a : ℝ, Psi 49 42 a (1 / 49) δ =
      Real.binEntropy δ + δ * Real.log 41 - (7 / 6 - a) * Real.log 49 := by
    intro a
    unfold Psi kappa
    simp only [Nat.cast_ofNat]
    rw [h7, hinv, h48, h41]
    ring
  refine ⟨?_, hPsi, ?_, ?_, ?_⟩
  · unfold rateR aGV Hq Real.qaryEntropy
    rw [hq41]
    simp only [Nat.cast_ofNat]
    rw [h7]
    field_simp <;> ring
  · rw [hPsi]
    unfold aGV
    field_simp <;> ring
  · show HasDerivAt (fun t => Real.binEntropy δ - (aGV δ + δ - 1) * Real.log t -
        (1 - δ) * Real.log (1 - t) - kappa 49 +
        δ * Real.log ((((42 : ℕ) : ℝ) - 1) / (((49 : ℕ) : ℝ) - 1))) _ _
    have hlog1 : HasDerivAt Real.log (1 / 49 : ℝ)⁻¹ (1 / 49) :=
      Real.hasDerivAt_log (by norm_num)
    have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - 1 / 49)) (1 / 49) :=
      ((hasDerivAt_id' (1 / 49 : ℝ)).const_sub 1).log (by norm_num)
    have hall := ((((hasDerivAt_const (1 / 49 : ℝ) (Real.binEntropy δ)).sub
      (hlog1.const_mul (aGV δ + δ - 1))).sub (hlog2.const_mul (1 - δ))).sub
      (hasDerivAt_const (1 / 49 : ℝ) (kappa 49))).add
      (hasDerivAt_const (1 / 49 : ℝ) (δ * Real.log ((((42 : ℕ) : ℝ) - 1) / (((49 : ℕ) : ℝ) - 1))))
    exact hall.congr_deriv (by ring)
  · unfold aGV Fgap
    field_simp <;> ring
