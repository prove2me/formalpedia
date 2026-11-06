-- Prove2me | solution 1 for BianchiIX.exitSingle_terminal_geometry
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:59:44.429404+00:00
-- url     : https://prove2.me/submissions/447c9e3c-07dc-4490-bb3c-3ab13e6a1e79

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_wall_split (m u v w : ℝ) :
    axisCycleDenom m u v w = (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) := by
  unfold axisCycleDenom curvature
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_boundary_denom {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 ≤ R ^ 2) :
    (2 - exitTailGap R v) ^ 2 + v ^ 2 = (R - 2) ^ 2 + 4 * v ^ 2 / (R + exitTailGap R v) := by
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hp : R + exitTailGap R v ≠ 0 := (add_pos_of_pos_of_nonneg hR ht0).ne'
  have ht := exitTailGap_sq hv
  field_simp
  nlinarith only [ht, congrArg (fun x => R * x) ht, congrArg (fun x => exitTailGap R v * x) ht]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_wall_error (m u v w : ℝ) :
    |axisCycleDenom m u v w - ((m + 1) ^ 2 + v ^ 2)| ≤
      (|u| + |w|) ^ 2 + 2 * |v| * (|u| + |w|) := by
  rw [axisCycleDenom_wall_split]
  have H := abs_sub ((u - w) ^ 2) (2 * v * (u + w))
  simp only [abs_of_nonneg (sq_nonneg (u - w)), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H
  have HS : (u - w) ^ 2 ≤ (|u| + |w|) ^ 2 := by
    have HD := abs_sub u w
    nlinarith only [sq_abs (u - w), (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr HD]
  have HM := mul_le_mul_of_nonneg_left (abs_add_le u w) (by positivity : 0 ≤ 2 * |v|)
  rw [show (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) - ((m + 1) ^ 2 + v ^ 2) =
    (u - w) ^ 2 - 2 * v * (u + w) by ring]
  exact H.trans (add_le_add HS HM)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycleDenom_terminal_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    399 / 100 * α ^ 2 < axisCycleDenom (1 - exitTailGap R v) u v w ∧
      axisCycleDenom (1 - exitTailGap R v) u v w < 401 / 100 * α ^ 2 := by
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hR0 : 0 < R := by linarith only [hRlo]
  have hv1 : v ≤ 1 := by linarith only [hv.2, hα.2]
  have ht := exitTailGap_compact hRlo ⟨hv.1, hv1⟩
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRlo, hv.1, hv1]
  have hp : 0 < R + exitTailGap R v := by linarith only [hRlo, ht.1]
  have hp3 : 3 ≤ R + exitTailGap R v := by linarith only [hRc.1, hB, hα.1, ht.1]
  have Hfrac : 4 * v ^ 2 / (R + exitTailGap R v) ≤ 4 / 3 * v ^ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hp3 (sq_nonneg v)]
  have Hfrac0 : 0 ≤ 4 * v ^ 2 / (R + exitTailGap R v) := by positivity
  have hρlo : 19999 / 10000 * α ≤ R - 2 := by linarith only [hRc.1, hB]
  have hρhi : R - 2 ≤ 20001 / 10000 * α := by linarith only [hRc.2, hB]
  have hρ0 : 0 ≤ R - 2 := by linarith only [hρlo, hα.1]
  have hρsqlo := (sq_le_sq₀ (by positivity) hρ0).mpr hρlo
  have hρsqhi := (sq_le_sq₀ hρ0 (by positivity)).mpr hρhi
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have herr := axisCycleDenom_wall_error (1 - exitTailGap R v) u v w
  rw [abs_of_nonneg hv.1] at herr
  have HE : (|u| + |w|) ^ 2 + 2 * v * (|u| + |w|) ≤
      (α / 10000) ^ 2 + 2 * (α / 100) * (α / 10000) := by
    gcongr <;> linarith only [hw, hB, hv.2]
  have Hb := abs_le.mp (herr.trans HE)
  have Hboundary := exitCycle_boundary_denom hR0 hvR
  constructor <;> nlinarith only [Hb.1, Hb.2, Hboundary, Hfrac0, Hfrac, hρsqlo, hρsqhi, hvsq, sq_pos_of_pos hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_terminal_offset {α B R v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    199 / 100 * α < exitTailGap R v - 2 ∧ exitTailGap R v - 2 < 201 / 100 * α := by
  have hα0 : 0 < α := hα.1
  have hRc := abs_le.mp hR
  have hRlo : 2 + 19999 / 10000 * α ≤ R := by linarith only [hRc.1, hB]
  have hR0 : 0 ≤ R := by linarith only [hRlo, hα.1]
  have hRsq := (sq_le_sq₀ (by positivity) hR0).mpr hRlo
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRsq, hvsq, hα.1, sq_nonneg α]
  have ht := exitTailGap_sq hvR
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hs : (2 + 199 / 100 * α) ^ 2 < (exitTailGap R v) ^ 2 := by
    nlinarith only [hRsq, hvsq, ht, hα.1, sq_nonneg α]
  have hlo := (sq_lt_sq₀ (by positivity) ht0).mp hs
  have hhi : exitTailGap R v ≤ R := (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])
  constructor <;> linarith only [hlo, hhi, hRc.2, hB, hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitSingleBase_eq (R v : ℝ) :
    exitSingleBase R v = axisCycleDenom (1 - exitTailGap R v) 0 v 0 := by
  dsimp only [exitSingleBase, axisCycleDenom, curvature]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitSingleDenom_eq (R u v w : ℝ) :
    axisCycleDenom (1 - exitTailGap R v) u v w = exitSingleBase R v + exitSingleDefect u v w := by
  rw [axisCycleDenom_wall_split]
  dsimp only [exitSingleBase, exitSingleDefect]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitSingleNumerator_eq {R v : ℝ} (hv : v ^ 2 ≤ R ^ 2) (u w : ℝ) :
    exitSingleBase R v + exitSingleDefect u v w - 4 * (2 - exitTailGap R v) =
      R ^ 2 - 4 + exitSingleDefect u v w := by
  have H := exitTailGap_sq hv
  dsimp only [exitSingleBase]
  nlinarith only [H]

end
end

private theorem BianchiIX.exitSingleDefect_bound {b u v w : ℝ} (hv : 0 ≤ v) (hw : |u| + |w| ≤ b) :
    |exitSingleDefect u v w| ≤ 2 * b * (v + b) := by
  have hb : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have Hsub : |u - w| ≤ b := (abs_sub u w).trans hw
  have Hadd : |u + w| ≤ b := (abs_add_le u w).trans hw
  calc
    |exitSingleDefect u v w| ≤ |(u - w) ^ 2| + |2 * v * (u + w)| := abs_sub _ _
    _ = |u - w| ^ 2 + 2 * v * |u + w| := by
      rw [abs_pow, abs_mul, abs_mul, abs_of_nonneg hv]; norm_num
    _ ≤ b ^ 2 + 2 * v * b := by gcongr
    _ ≤ 2 * b * (v + b) := by nlinarith only [sq_nonneg b]


theorem solution {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    2 < R ∧ R ≤ 5 ∧ 2 < exitTailGap R v ∧ exitTailGap R v ≤ 5 ∧
      v ^ 2 < R ^ 2 ∧ α ^ 2 ≤ exitSingleBase R v ∧
      |exitSingleDefect u v w| ≤ α ^ 2 / 1000 ∧
      |R ^ 2 - 4 + exitSingleDefect u v w| ≤ 22 * α ∧
      0 < exitSingleBase R v + exitSingleDefect u v w ∧
      0 < R ^ 2 - 4 + exitSingleDefect u v w := by
  have hα0 := hα.1
  have hv0 := hv.1
  have hvhi := hv.2
  have hb0 : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have HR := abs_le.mp hR
  have HRlo : 2 < R := by linarith only [HR.1, hα.1]
  have HRhi : R ≤ 5 := by linarith only [HR.2, hα.2]
  have HG := exitTailGap_terminal_offset hα (le_refl (α / 10000)) hR hv
  have HGlo : 2 < exitTailGap R v := by linarith only [HG.1, hα.1]
  have HGhi : exitTailGap R v ≤ 5 := by linarith only [HG.2, hα.2]
  have HvR : v ^ 2 < R ^ 2 := by
    have Hv : v ≤ 1 / 100 := hv.2.trans (by linarith only [hα.2])
    nlinarith only [Hv, hv.1, HRlo, sq_nonneg (v - 1 / 100)]
  have HH₀ := exitCycleDenom_terminal_bounds (u := 0) (w := 0) hα
    (le_refl (α / 10000)) hR (by simpa using (by positivity : 0 ≤ α / 10000)) hv
  rw [← exitSingleBase_eq] at HH₀
  have HHlo : α ^ 2 ≤ exitSingleBase R v := by nlinarith only [HH₀.1, sq_nonneg α]
  have HT := exitSingleDefect_bound hv.1 hw
  have HTsmall : |exitSingleDefect u v w| ≤ α ^ 2 / 1000 := by
    have HT' : 2 * b * (v + b) ≤ 2 * (α / 10000) * (α / 100 + α / 10000) := by gcongr
    nlinarith only [HT, HT', sq_nonneg α]
  have HN₀lo : 0 ≤ R ^ 2 - 4 := by nlinarith only [HRlo]
  have HN₀hi : R ^ 2 - 4 ≤ 21 * α := by
    have Hdiff : R - 2 ≤ 3 * α := by linarith only [HR.2, hα.1]
    have Hsum : R + 2 ≤ 7 := by linarith only [HRhi]
    nlinarith only [mul_le_mul Hdiff Hsum (by linarith only [HRlo] : 0 ≤ R + 2)
      (by positivity : 0 ≤ 3 * α)]
  have HN : |R ^ 2 - 4 + exitSingleDefect u v w| ≤ 22 * α := by
    have H := abs_add_le (R ^ 2 - 4) (exitSingleDefect u v w)
    rw [abs_of_nonneg HN₀lo] at H
    nlinarith only [H, HN₀hi, HTsmall, hα.1, hα.2]
  have HH := exitCycleDenom_terminal_bounds hα (le_refl (α / 10000)) hR (hw.trans hb) hv
  rw [exitSingleDenom_eq] at HH
  have HHpos : 0 < exitSingleBase R v + exitSingleDefect u v w :=
    lt_trans (by positivity) HH.1
  have HNpos : 0 < R ^ 2 - 4 + exitSingleDefect u v w := by
    have H := exitSingleNumerator_eq HvR.le u w
    linarith only [H, HHpos, HGlo]
  exact ⟨HRlo, HRhi, HGlo, HGhi, HvR, HHlo, HTsmall, HN, HHpos, HNpos⟩
