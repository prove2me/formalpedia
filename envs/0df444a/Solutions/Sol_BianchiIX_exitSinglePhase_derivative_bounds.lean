-- Prove2me | solution 1 for BianchiIX.exitSinglePhase_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:02:47.263346+00:00
-- url     : https://prove2.me/submissions/82640040-18cf-4be8-9004-b510937d92c3

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exitSingleError_scalar_bounds
import Theorems.Thm_BianchiIX_exitSinglePhase_differential
import Theorems.Thm_BianchiIX_exitSingle_terminal_geometry
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

private theorem BianchiIX.exitSingleSquare_eq {R v : ℝ} (hH : exitSingleBase R v ≠ 0) (u w : ℝ) :
    R ^ 2 + exitSingleError R u v w =
      4 + (exitSingleBase R v + exitSingleDefect u v w) *
        (R ^ 2 - 4 + exitSingleDefect u v w) / exitSingleBase R v := by
  dsimp only [exitSingleError]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

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

end
end

private theorem BianchiIX.exitSingle_terminal_error_bounds {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    2 < Real.sqrt (R ^ 2 + exitSingleError R u v w) ∧
      |exitSingleError R u v w| ≤ 46 * b * (v + b) / α ∧
      |exitSingleErrorRadial R u v w| ≤ 900 * b * (v + b) / α ^ 2 ∧
      |exitSingleErrorWallFactor R u v w| ≤ 24 / α := by
  have hα0 := hα.1
  obtain ⟨HR, HRhi, HG, HGhi, Hsq, HH, HT, HN, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hb hR hw hv
  have HH₀ : 0 < exitSingleBase R v := lt_of_lt_of_le (sq_pos_of_pos hα0) HH
  have HG0 : 0 < exitTailGap R v := lt_trans (by norm_num) HG
  have HR0 : 0 ≤ R := by linarith only [HR]
  have Hoffset := exitTailGap_terminal_offset hα (le_refl (α / 10000)) hR hv
  have HGdiff : exitTailGap R v - 2 ≤ 3 * α := by linarith only [Hoffset.2, hα.1]
  have HL : |exitSingleBaseRadial R v| ≤ 20 * α := by
    rw [exitSingleBaseRadial, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 2 * (3 * α) * 5 / 2 := by gcongr
      _ ≤ _ := by linarith only [hα.1]
  have HE := exitSingleError_scalar_bounds hα ⟨HR0, HRhi⟩ HH HT HN HL
    (exitSingleDefect_bound hv.1 hw)
  have HS : 4 < R ^ 2 + exitSingleError R u v w := by
    rw [exitSingleSquare_eq HH₀.ne']
    linarith only [div_pos (mul_pos HHpos HNpos) HH₀]
  refine ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num; exact HS), ?_, ?_, HE.2.2.2⟩
  · have H := HE.1
    change |exitSingleError R u v w| ≤ 23 * (2 * b * (v + b)) / α at H
    convert H using 1; ring
  · have H := HE.2.2.1
    change |exitSingleErrorRadial R u v w| ≤ 450 * (2 * b * (v + b)) / α ^ 2 at H
    convert H using 1; ring


/-- Ordinary fixed-height derivatives, including signed and zero old walls, with the radial cancellation. -/
theorem solution {α b v : ℝ} {Y : ExitTailState}
    (hα : 0 < α ∧ α ≤ 1) (hb : b ≤ α / 10000)
    (hR : |Y 0 - (2 + 2 * α)| ≤ α / 10000) (hw : |Y 1| + |Y 2| ≤ b)
    (hv : 0 ≤ v ∧ v ≤ α / 100) :
    let f := fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)
    ContDiffAt ℝ 2 f Y ∧
      |fderiv ℝ f Y (Pi.single 0 1) - 1 / 2| ≤ 1024 * b * (v + b) / α ^ 2 ∧
      |fderiv ℝ f Y (Pi.single 1 1)| + |fderiv ℝ f Y (Pi.single 2 1)| ≤ 1024 * (v + b) / α := by
  intro f
  have hα0 := hα.1
  have hv0 := hv.1
  have hb0 : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  obtain ⟨HR, HRhi, HG, HGhi, Hsq, HH, HT, HN, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hb hR hw hv
  have HH₀ : 0 < exitSingleBase (Y 0) v := lt_of_lt_of_le (sq_pos_of_pos hα0) HH
  obtain ⟨HX, HE, HER, HEW⟩ := exitSingle_terminal_error_bounds hα hb hR hw hv
  let X := Real.sqrt ((Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2))
  change 2 < X at HX
  have HX0 : 0 < X := lt_trans (by norm_num) HX
  have HS : 0 < (Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2) :=
    Real.sqrt_pos.mp HX0
  have HXsq : X ^ 2 = (Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2) := Real.sq_sqrt HS.le
  have Hdiff := exitSinglePhase_differential Hsq HH₀.ne' HS
  change ContDiffAt ℝ 2 f Y ∧ _ at Hdiff
  have Hdistance : |Y 0 - X| ≤ |exitSingleError (Y 0) (Y 1) v (Y 2)| := by
    have Heq : (Y 0 - X) * (Y 0 + X) = -exitSingleError (Y 0) (Y 1) v (Y 2) := by
      nlinarith only [HXsq]
    have Ha := congrArg abs Heq
    rw [abs_mul, abs_neg, abs_of_pos (by linarith only [HR, HX] : 0 < Y 0 + X)] at Ha
    nlinarith only [Ha, HR, HX, abs_nonneg (Y 0 - X)]
  refine ⟨Hdiff.1, ?_, ?_⟩
  · have HD := Hdiff.2 (Pi.single 0 1)
    simp at HD
    rw [HD]
    change |(2 * Y 0 + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)) / (4 * X) - 1 / 2| ≤ _
    have Hid : (2 * Y 0 + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)) / (4 * X) - 1 / 2 =
        (Y 0 - X) / (2 * X) + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2) / (4 * X) := by
      field_simp; ring
    rw [Hid]
    calc
      _ ≤ |Y 0 - X| / (2 * X) + |exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)| / (4 * X) := by
        have H := abs_add_le ((Y 0 - X) / (2 * X)) (exitSingleErrorRadial (Y 0) (Y 1) v (Y 2) / (4 * X))
        simpa only [abs_div, abs_of_pos (by positivity : 0 < 2 * X),
          abs_of_pos (by positivity : 0 < 4 * X)] using H
      _ ≤ |Y 0 - X| + |exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)| := by
        apply add_le_add <;> apply div_le_self (abs_nonneg _) <;> linarith only [HX]
      _ ≤ 46 * b * (v + b) / α + 900 * b * (v + b) / α ^ 2 := add_le_add (Hdistance.trans HE) HER
      _ ≤ 1024 * b * (v + b) / α ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hα0)).mpr
        field_simp
        nlinarith only [mul_le_mul_of_nonneg_right hα.2 (by positivity : 0 ≤ b * (v + b)),
          mul_nonneg hb0 (add_nonneg hv0 hb0)]
  · have HD1 := Hdiff.2 (Pi.single 1 1)
    have HD2 := Hdiff.2 (Pi.single 2 1)
    simp at HD1 HD2
    rw [HD1, HD2]
    have Hwall : |2 * (Y 1 - Y 2) - 2 * v| + |-(2 * (Y 1 - Y 2)) - 2 * v| ≤ 4 * (v + b) := by
      have H3 := (abs_sub (Y 1) (Y 2)).trans hw
      calc
        _ ≤ (|2 * (Y 1 - Y 2)| + |2 * v|) + (|-(2 * (Y 1 - Y 2))| + |2 * v|) :=
          add_le_add (abs_sub _ _) (abs_sub _ _)
        _ = 4 * (|Y 1 - Y 2| + v) := by
          norm_num [abs_mul, abs_of_nonneg hv0]
          ring
        _ ≤ _ := by linarith only [H3]
    change |_ * _ / (4 * X)| + |_ * _ / (4 * X)| ≤ _
    simp only [abs_div, abs_mul, abs_of_pos HX0]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      _ = |exitSingleErrorWallFactor (Y 0) (Y 1) v (Y 2)| *
          (|2 * (Y 1 - Y 2) - 2 * v| + |-(2 * (Y 1 - Y 2)) - 2 * v|) / (4 * X) := by ring
      _ ≤ (24 / α) * (4 * (v + b)) := by
        have HQ := div_le_self
          (mul_nonneg (abs_nonneg (exitSingleErrorWallFactor (Y 0) (Y 1) v (Y 2)))
            (add_nonneg (abs_nonneg (2 * (Y 1 - Y 2) - 2 * v))
              (abs_nonneg (-(2 * (Y 1 - Y 2)) - 2 * v))))
          (by linarith only [HX] : 1 ≤ 4 * X)
        exact HQ.trans (mul_le_mul HEW Hwall (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity))
      _ ≤ 1024 * (v + b) / α := by
        apply (le_div_iff₀ hα0).mpr
        field_simp
        nlinarith only [hv0, hb0]
