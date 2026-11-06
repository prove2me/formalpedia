-- Prove2me | solution 1 for BianchiIX.stableCorrectedPhase_directional_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:27:27.368776+00:00
-- url     : https://prove2.me/submissions/227fba3f-d81a-45a7-a5a0-02ac31d633d0

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Theorems.Thm_BianchiIX_stableCorrectedPhase_coefficient_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_fderiv_apply_const {f : E → F} {gamma : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (gamma t))
    (hg : HasDerivAt gamma v t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ f (gamma s) w)
      (fderiv ℝ (fderiv ℝ f) (gamma t) v w) t := by
  have H := (hf.hasFDerivAt.comp_hasDerivAt t hg).clm_apply (hasDerivAt_const t w)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_pos {m w : ℝ} (hm : -1 < m) : 0 < stableWeakRadius m w :=
  phaseNorm_pos (by linarith : 0 < m + 1)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_sq (m w : ℝ) :
    stableWeakRadius m w ^ 2 = (m + 1) ^ 2 + w ^ 2 := phaseNorm_sq _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionA {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionA (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  convert! (hasDerivAt_id m).div (((hasDerivAt_id m).pow 2).sub_const 1) hd using 1
  dsimp
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionC {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionC (2 / (m + 1) ^ 2) m := by
  have hd : m + 1 ≠ 0 := by linarith
  convert! (hasDerivAt_const m (-2 : ℝ)).div ((hasDerivAt_id m).add_const 1) hd using 1
  simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableWeakRadius {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => stableWeakRadius (m s) (w s))
      (((m t + 1) * m' + w t * w') / stableWeakRadius (m t) (w t)) t := by
  have hn : (m t + 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have h : 0 < m t + 1 := by linarith
    positivity
  convert! ((((hm.add_const 1).pow 2).add (hw.pow 2)).sqrt hn) using 1
  dsimp [stableWeakRadius, phaseNorm]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectedPhase {m u w : ℝ → ℝ} {m' u' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hpos : 1 < m t) :
    HasDerivAt (fun s => stableCorrectedPhase (m s) (u s) (w s))
      (stableCorrectedGradient (m t) (u t) (w t) 0 * m' +
        stableCorrectedGradient (m t) (u t) (w t) 1 * u' +
        stableCorrectedGradient (m t) (u t) (w t) 2 * w') t := by
  have hS := hasDerivAt_stableWeakRadius hm hw (by linarith)
  have hA := (hasDerivAt_stableCorrectionA hpos).comp t hm
  have hC := (hasDerivAt_stableCorrectionC (by linarith : -1 < m t)).comp t hm
  convert! ((hS.sub_const 1).add (hA.mul (hu.pow 2))).add ((hC.mul hu).mul hw) using 1
  dsimp [stableCorrectedGradient]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_stableCorrectedPhase (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableCorrectedPhase stableWeakRadius phaseNorm stableCorrectionA stableCorrectionC
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableCorrectionADeriv {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionADeriv (stableCorrectionASecond m) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  apply (((((hasDerivAt_id m).pow 2).add_const 1).neg).div
    ((((hasDerivAt_id m).pow 2).sub_const 1).pow 2) (pow_ne_zero 2 hd)).congr_deriv
  dsimp [stableCorrectionASecond]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableCorrectionCDeriv {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionCDeriv (stableCorrectionCSecond m) m := by
  have hd : m + 1 ≠ 0 := by linarith
  apply ((hasDerivAt_const m (2 : ℝ)).div (((hasDerivAt_id m).add_const 1).pow 2)
    (pow_ne_zero 2 hd)).congr_deriv
  dsimp [stableCorrectionCSecond]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableWeakSlopes {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => (m s + 1) / stableWeakRadius (m s) (w s))
      ((w t) ^ 2 / stableWeakRadius (m t) (w t) ^ 3 * m' -
        (m t + 1) * w t / stableWeakRadius (m t) (w t) ^ 3 * w') t ∧
    HasDerivAt (fun s => w s / stableWeakRadius (m s) (w s))
      (-(m t + 1) * w t / stableWeakRadius (m t) (w t) ^ 3 * m' +
        (m t + 1) ^ 2 / stableWeakRadius (m t) (w t) ^ 3 * w') t := by
  have hs := hasDerivAt_stableWeakRadius hm hw hpos
  have hn := ne_of_gt (stableWeakRadius_pos (w := w t) hpos)
  have hsq := stableWeakRadius_sq (m t) (w t)
  constructor
  · apply ((hm.add_const 1).div hs hn).congr_deriv
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z * m') hsq]
  · apply (hw.div hs hn).congr_deriv
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z * w') hsq]

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.stableCorrectedPhase_fderiv {y : Fin 3 → ℝ} (hm : 1 < y 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y v =
      stableCorrectedGradient (y 0) (y 1) (y 2) 0 * v 0 +
      stableCorrectedGradient (y 0) (y 1) (y 2) 1 * v 1 +
      stableCorrectedGradient (y 0) (y 1) (y 2) 2 * v 2 := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_stableCorrectedPhase 1 (y := y + (0 : ℝ) • v) (by simpa using hm)
  have H := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hl
  have G := hasDerivAt_stableCorrectedPhase (hasDerivAt_pi.mp hl 0)
    (hasDerivAt_pi.mp hl 1) (hasDerivAt_pi.mp hl 2) (by simpa using hm)
  simpa using H.unique G

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableCorrectedGradient_apply {gamma : ℝ → (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {t : ℝ}
    (h : HasDerivAt gamma v t) (hm : 1 < gamma t 0) (r : Fin 3 → ℝ) :
    HasDerivAt (fun s => stableCorrectedGradient (gamma s 0) (gamma s 1) (gamma s 2) 0 * r 0 +
      stableCorrectedGradient (gamma s 0) (gamma s 1) (gamma s 2) 1 * r 1 +
      stableCorrectedGradient (gamma s 0) (gamma s 1) (gamma s 2) 2 * r 2)
      (stableCorrectedHessian (gamma t 0) (gamma t 1) (gamma t 2) v r) t := by
  have hM := hasDerivAt_pi.mp h 0
  have hU := hasDerivAt_pi.mp h 1
  have hW := hasDerivAt_pi.mp h 2
  have hs := hasDerivAt_stableWeakSlopes hM hW (by linarith)
  have ha := (hasDerivAt_stableCorrectionA hm).comp t hM
  have hc := (hasDerivAt_stableCorrectionC (by linarith : -1 < gamma t 0)).comp t hM
  have ha1 := (hasDerivAt_stableCorrectionADeriv hm).comp t hM
  have hc1 := (hasDerivAt_stableCorrectionCDeriv (by linarith : -1 < gamma t 0)).comp t hM
  have h0 := (hs.1.add (ha1.mul (hU.pow 2))).add ((hc1.mul hU).mul hW)
  have h1 := ((ha.const_mul 2).mul hU).add (hc.mul hW)
  have h2 := hs.2.add (hc.mul hU)
  have H := ((h0.mul_const (r 0)).add (h1.mul_const (r 1))).add (h2.mul_const (r 2))
  convert! H using 1
  · funext s
    dsimp [stableCorrectedGradient, stableCorrectionADeriv, stableCorrectionCDeriv]
    ring
  · dsimp [stableCorrectedHessian, stableCorrectionADeriv, stableCorrectionCDeriv]
    ring

end
end

section
noncomputable section
open BianchiIX
open scoped Topology

private theorem BianchiIX.stableCorrectedPhase_fderiv2 {y : Fin 3 → ℝ} (hm : 1 < y 0) (v r : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2))) y v r =
      stableCorrectedHessian (y 0) (y 1) (y 2) v r := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_stableCorrectedPhase 2 (y := y + (0 : ℝ) • v) (by simpa using hm)
  have hD := (hreg.fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have H := hasDerivAt_fderiv_apply_const hD hl r
  have heq : (fun s : ℝ => fderiv ℝ (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) (y + s • v) r)
      =ᶠ[𝓝 0] (fun s => stableCorrectedGradient ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) 0 * r 0 +
        stableCorrectedGradient ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) 1 * r 1 +
        stableCorrectedGradient ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) 2 * r 2) := by
    have hnear : ∀ᶠ s : ℝ in 𝓝 0, 1 < (y + s • v) 0 :=
      ((hasDerivAt_pi.mp hl 0).continuousAt.eventually (isOpen_Ioi.mem_nhds (by simpa using hm)))
    filter_upwards [hnear] with s hs
    exact stableCorrectedPhase_fderiv hs r
  have G := hasDerivAt_stableCorrectedGradient_apply hl (by simpa using hm) r
  simpa using (H.congr_of_eventuallyEq heq.symm).unique G

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectionA_partial_fractions {m : ℝ} (hm : 1 < m) :
    stableCorrectionA m = (1 / (m - 1) + 1 / (m + 1)) / 2 ∧
      stableCorrectionADeriv m = -(1 / (m - 1) ^ 2 + 1 / (m + 1) ^ 2) / 2 ∧
      stableCorrectionASecond m = 1 / (m - 1) ^ 3 + 1 / (m + 1) ^ 3 := by
  have h1 : m - 1 ≠ 0 := by linarith
  have h2 : m + 1 ≠ 0 := by linarith
  have h3 : m ^ 2 - 1 ≠ 0 := by nlinarith
  dsimp [stableCorrectionA, stableCorrectionADeriv, stableCorrectionASecond]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrection_coefficients_bounds {m : ℝ} (hm : 2 ≤ m) :
    |stableCorrectionA m| ≤ 2 / (m + 1) ∧
      |stableCorrectionADeriv m| ≤ 5 / (m + 1) ^ 2 ∧
      |stableCorrectionASecond m| ≤ 28 / (m + 1) ^ 3 ∧
      |stableCorrectionC m| = 2 / (m + 1) ∧
      |stableCorrectionCDeriv m| = 2 / (m + 1) ^ 2 ∧
      |stableCorrectionCSecond m| = 4 / (m + 1) ^ 3 := by
  have hL : 0 < m + 1 := by linarith
  have hD : 0 < m - 1 := by linarith
  have hp (n : ℕ) : 1 / (m - 1) ^ n ≤ 3 ^ n / (m + 1) ^ n := by
    apply (div_le_div_iff₀ (pow_pos hD n) (pow_pos hL n)).mpr
    simpa only [one_mul, mul_pow] using
      pow_le_pow_left₀ hL.le (show m + 1 ≤ 3 * (m - 1) by linarith) n
  obtain ⟨h0, h1, h2⟩ := stableCorrectionA_partial_fractions (by linarith : 1 < m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, abs_of_nonneg (by positivity)]
    have H := hp 1
    norm_num only [pow_one] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · rw [h1, neg_div, abs_neg, abs_of_nonneg (by positivity)]
    have H := hp 2
    norm_num only [Nat.reducePow] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · rw [h2, abs_of_nonneg (by positivity)]
    have H := hp 3
    norm_num only [Nat.reducePow] at H
    simp only [div_eq_mul_inv, one_mul] at H ⊢
    linarith only [H]
  · simp [stableCorrectionC, abs_div, abs_of_pos hL]
  · rw [stableCorrectionCDeriv, abs_of_nonneg (by positivity)]
  · simp [stableCorrectionCSecond, abs_div, abs_of_pos hL]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_coefficient_bounds {m w : ℝ} (hm : -1 < m) :
    |(m + 1) / stableWeakRadius m w - 1| ≤ w ^ 2 / (m + 1) ^ 2 ∧
      |w / stableWeakRadius m w| ≤ |w| / (m + 1) ∧
      |w ^ 2 / stableWeakRadius m w ^ 3| ≤ w ^ 2 / (m + 1) ^ 3 ∧
      |-(m + 1) * w / stableWeakRadius m w ^ 3| ≤ |w| / (m + 1) ^ 2 ∧
      |(m + 1) ^ 2 / stableWeakRadius m w ^ 3| ≤ 1 / (m + 1) := by
  have hL : 0 < m + 1 := by linarith
  have hS := stableWeakRadius_pos (w := w) hm
  have hLS : m + 1 ≤ stableWeakRadius m w := phaseNorm_ge hL.le
  have h3 := pow_le_pow_left₀ hL.le hLS 3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have H := phaseNorm_ratio_defect (b := w) hL
    change 1 - (m + 1) / stableWeakRadius m w =
      w ^ 2 * (1 / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))) at H
    rw [abs_sub_comm, H, abs_of_nonneg (by positivity), mul_one_div]
    apply div_le_div_of_nonneg_left (sq_nonneg w) (pow_pos hL 2)
    have H0 := mul_le_mul hLS (show m + 1 ≤ stableWeakRadius m w + (m + 1) by linarith)
      hL.le hS.le
    nlinarith only [H0]
  · rw [abs_div, abs_of_pos hS]
    exact div_le_div_of_nonneg_left (abs_nonneg w) hL hLS
  · rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (sq_nonneg w) (pow_pos hL 3) h3
  · rw [abs_div, abs_mul, abs_neg, abs_of_pos hL, abs_of_pos (pow_pos hS 3)]
    calc
      _ ≤ (m + 1) * |w| / (m + 1) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3) h3
      _ = |w| / (m + 1) ^ 2 := by field_simp
  · rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (m + 1) ^ 2 / (m + 1) ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hL 3) h3
      _ = 1 / (m + 1) := by field_simp

end
end

theorem solution {y : Fin 3 → ℝ} (hm : 2 ≤ y 0) :
    let b := |y 1| + |y 2|
    let L := y 0 + 1
    let P := fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)
    (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ P y v - v 0| ≤ 8 / L ^ 2 * b ^ 2 * ‖v‖) ∧
    (∀ v, v 0 = 0 → |fderiv ℝ P y v| ≤ 9 / L * b * ‖v‖) ∧
    (∀ v r, v 1 = 0 → v 2 = 0 → r 1 = 0 → r 2 = 0 →
      |fderiv ℝ (fderiv ℝ P) y v r| ≤ 33 / L ^ 3 * b ^ 2 * ‖v‖ * ‖r‖) ∧
    (∀ v r, v 1 = 0 → v 2 = 0 → r 0 = 0 →
      |fderiv ℝ (fderiv ℝ P) y v r| ≤ 15 / L ^ 2 * b * ‖v‖ * ‖r‖) ∧
    (∀ v r, v 0 = 0 → r 0 = 0 →
      |fderiv ℝ (fderiv ℝ P) y v r| ≤ 9 / L * ‖v‖ * ‖r‖) := by
  have hm1 : 1 < y 0 := by linarith
  have hL : 0 < y 0 + 1 := by linarith
  obtain ⟨h0, h1, h2, h00, h01, h02⟩ := stableCorrectedPhase_coefficient_bounds (u := y 1) (w := y 2) hm
  obtain ⟨ha, _, _, hc, _, _⟩ := stableCorrection_coefficients_bounds hm
  have h22 := (stableWeakRadius_coefficient_bounds (m := y 0) (w := y 2) (by linarith)).2.2.2.2
  have hv (v : Fin 3 → ℝ) (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hmul {a B : ℝ} (h : |a| ≤ B) (v : Fin 3 → ℝ) (i : Fin 3) :
      |a * v i| ≤ B * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul h (hv v i) (abs_nonneg _) ((abs_nonneg a).trans h)
  have hprod {a B : ℝ} (h : |a| ≤ B) (v r : Fin 3 → ℝ) (i j : Fin 3) :
      |a * v i * r j| ≤ B * ‖v‖ * ‖r‖ := by
    have hB : 0 ≤ B := (abs_nonneg a).trans h
    rw [abs_mul]
    exact mul_le_mul (hmul h v i) (hv r j) (abs_nonneg _) (by positivity)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv1 hv2
    rw [stableCorrectedPhase_fderiv hm1]
    simp only [hv1, hv2, mul_zero, add_zero]
    rw [show stableCorrectedGradient (y 0) (y 1) (y 2) 0 * v 0 - v 0 =
      (stableCorrectedGradient (y 0) (y 1) (y 2) 0 - 1) * v 0 by ring]
    exact hmul h0 v 0
  · intro v hv0
    rw [stableCorrectedPhase_fderiv hm1]
    simp only [hv0, mul_zero, zero_add]
    have H := abs_add_le (stableCorrectedGradient (y 0) (y 1) (y 2) 1 * v 1)
      (stableCorrectedGradient (y 0) (y 1) (y 2) 2 * v 2)
    have H1 := hmul h1 v 1
    have H2 := hmul h2 v 2
    simp only [div_eq_mul_inv] at H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · intro v r hv1 hv2 hr1 hr2
    rw [stableCorrectedPhase_fderiv2 hm1]
    simp only [stableCorrectedHessian, hv1, hv2, hr1, hr2, mul_zero, zero_mul, add_zero]
    exact hprod h00 v r 0 0
  · intro v r hv1 hv2 hr0
    rw [stableCorrectedPhase_fderiv2 hm1]
    simp only [stableCorrectedHessian, hv1, hv2, hr0, mul_zero, zero_mul, add_zero, zero_add, ← mul_assoc]
    have H1 := hprod h01 v r 0 1
    have H2 := hprod h02 v r 0 2
    have H := abs_add_le
      ((2 * stableCorrectionADeriv (y 0) * y 1 + stableCorrectionCDeriv (y 0) * y 2) * v 0 * r 1)
      ((-(y 0 + 1) * y 2 / stableWeakRadius (y 0) (y 2) ^ 3 + stableCorrectionCDeriv (y 0) * y 1) * v 0 * r 2)
    simp only [div_eq_mul_inv] at H H1 H2 ⊢
    nlinarith only [H, H1, H2]
  · intro v r hv0 hr0
    rw [stableCorrectedPhase_fderiv2 hm1]
    simp only [stableCorrectedHessian, hv0, hr0, mul_zero, zero_mul, add_zero, zero_add, mul_add, ← mul_assoc]
    have ha2 : |2 * stableCorrectionA (y 0)| ≤ 4 / (y 0 + 1) := by
      norm_num [abs_mul]
      simp only [div_eq_mul_inv] at ha ⊢
      linarith only [ha]
    have H1 := hprod ha2 v r 1 1
    have H2 := hprod hc.le v r 1 2
    have H3 := hprod hc.le v r 2 1
    have H4 := hprod h22 v r 2 2
    have htri (a b c d : ℝ) : |a + (b + c) + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a (b + c), abs_add_le b c, abs_add_le (a + (b + c)) d]
    have H := htri (2 * stableCorrectionA (y 0) * v 1 * r 1)
      (stableCorrectionC (y 0) * v 1 * r 2) (stableCorrectionC (y 0) * v 2 * r 1)
      ((y 0 + 1) ^ 2 / stableWeakRadius (y 0) (y 2) ^ 3 * v 2 * r 2)
    simp only [div_eq_mul_inv] at H H1 H2 H3 H4 ⊢
    nlinarith only [H, H1, H2, H3, H4]
