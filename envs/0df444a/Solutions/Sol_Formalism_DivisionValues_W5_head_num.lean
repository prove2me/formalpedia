-- Prove2me | solution 1 for Formalism.DivisionValues.W5.head_num
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:50.869844+00:00
-- url     : https://prove2.me/submissions/71a51f56-f455-4b23-9d98-83437db9c275

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_logp
import Theorems.Thm_Formalism_DivisionValues_W5_log_three_le
import Theorems.Thm_Formalism_DivisionValues_W5_log_five_le
import Theorems.Thm_Formalism_DivisionValues_W5_place_sum_over_primes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
namespace Formalism.DivisionValues.W5
theorem _root_.solution :
    Real.log 2 / 2 ^ 2 + Real.log 3 / 3 ^ 2 + Real.log 5 / 5 ^ 2 + Real.log 7 / 7 ^ 2 + Real.log 11 / 11 ^ 2 + Real.log 13 / 13 ^ 2 + Real.log 17 / 17 ^ 2 + Real.log 19 / 19 ^ 2 + Real.log 23 / 23 ^ 2 + Real.log 29 / 29 ^ 2 + Real.log 31 / 31 ^ 2 + Real.log 37 / 37 ^ 2 + Real.log 41 / 41 ^ 2 + Real.log 43 / 43 ^ 2 + Real.log 47 / 47 ^ 2 + Real.log 53 / 53 ^ 2 + Real.log 59 / 59 ^ 2 + Real.log 61 / 61 ^ 2 + Real.log 67 / 67 ^ 2 + Real.log 71 / 71 ^ 2 + Real.log 73 / 73 ^ 2 + Real.log 79 / 79 ^ 2 + Real.log 83 / 83 ^ 2 + Real.log 89 / 89 ^ 2 + Real.log 97 / 97 ^ 2 + Real.log 101 / 101 ^ 2 + Real.log 103 / 103 ^ 2 + Real.log 107 / 107 ^ 2 + Real.log 109 / 109 ^ 2 + Real.log 113 / 113 ^ 2 + Real.log 127 / 127 ^ 2 + Real.log 131 / 131 ^ 2 + Real.log 137 / 137 ^ 2 + Real.log 139 / 139 ^ 2 + Real.log 149 / 149 ^ 2 + Real.log 151 / 151 ^ 2 + Real.log 157 / 157 ^ 2 + Real.log 163 / 163 ^ 2 + Real.log 167 / 167 ^ 2 + Real.log 173 / 173 ^ 2 + Real.log 179 / 179 ^ 2 + Real.log 181 / 181 ^ 2 + Real.log 191 / 191 ^ 2 + Real.log 193 / 193 ^ 2 + Real.log 197 / 197 ^ 2 + Real.log 199 / 199 ^ 2 + Real.log 211 / 211 ^ 2 + Real.log 223 / 223 ^ 2 + Real.log 227 / 227 ^ 2 + Real.log 229 / 229 ^ 2 + Real.log 233 / 233 ^ 2 + Real.log 239 / 239 ^ 2 + (Real.log 234 + 1) / 234 / 3 ≤ 4995 / 10000 := by
  have l2 := Real.log_two_lt_d9
  have l3 := log_three_le
  have l5 := log_five_le
  have l7 := place_sum_over_primes
  have h11 : Real.log 11 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 12 := by
    exact_mod_cast logp 11 2 1 0 0 ((-1 : ℝ) / 12) (by norm_num) (by norm_num)
  have h13 : Real.log 13 ≤ 1 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 14 := by
    exact_mod_cast logp 13 1 0 0 1 ((-1 : ℝ) / 14) (by norm_num) (by norm_num)
  have h17 : Real.log 17 ≤ 1 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 18 := by
    exact_mod_cast logp 17 1 2 0 0 ((-1 : ℝ) / 18) (by norm_num) (by norm_num)
  have h19 : Real.log 19 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 20 := by
    exact_mod_cast logp 19 2 0 1 0 ((-1 : ℝ) / 20) (by norm_num) (by norm_num)
  have h23 : Real.log 23 ≤ 3 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 24 := by
    exact_mod_cast logp 23 3 1 0 0 ((-1 : ℝ) / 24) (by norm_num) (by norm_num)
  have h29 : Real.log 29 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 30 := by
    exact_mod_cast logp 29 1 1 1 0 ((-1 : ℝ) / 30) (by norm_num) (by norm_num)
  have h31 : Real.log 31 ≤ 5 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 32 := by
    exact_mod_cast logp 31 5 0 0 0 ((-1 : ℝ) / 32) (by norm_num) (by norm_num)
  have h37 : Real.log 37 ≤ 2 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 36 := by
    exact_mod_cast logp 37 2 2 0 0 ((1 : ℝ) / 36) (by norm_num) (by norm_num)
  have h41 : Real.log 41 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 42 := by
    exact_mod_cast logp 41 1 1 0 1 ((-1 : ℝ) / 42) (by norm_num) (by norm_num)
  have h43 : Real.log 43 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (1 : ℝ) / 42 := by
    exact_mod_cast logp 43 1 1 0 1 ((1 : ℝ) / 42) (by norm_num) (by norm_num)
  have h47 : Real.log 47 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 48 := by
    exact_mod_cast logp 47 4 1 0 0 ((-1 : ℝ) / 48) (by norm_num) (by norm_num)
  have h53 : Real.log 53 ≤ 1 * Real.log 2 + 3 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 54 := by
    exact_mod_cast logp 53 1 3 0 0 ((-1 : ℝ) / 54) (by norm_num) (by norm_num)
  have h59 : Real.log 59 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 60 := by
    exact_mod_cast logp 59 2 1 1 0 ((-1 : ℝ) / 60) (by norm_num) (by norm_num)
  have h61 : Real.log 61 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 60 := by
    exact_mod_cast logp 61 2 1 1 0 ((1 : ℝ) / 60) (by norm_num) (by norm_num)
  have h67 : Real.log 67 ≤ 1 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (-3 : ℝ) / 70 := by
    exact_mod_cast logp 67 1 0 1 1 ((-3 : ℝ) / 70) (by norm_num) (by norm_num)
  have h71 : Real.log 71 ≤ 3 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 72 := by
    exact_mod_cast logp 71 3 2 0 0 ((-1 : ℝ) / 72) (by norm_num) (by norm_num)
  have h73 : Real.log 73 ≤ 3 * Real.log 2 + 2 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 72 := by
    exact_mod_cast logp 73 3 2 0 0 ((1 : ℝ) / 72) (by norm_num) (by norm_num)
  have h79 : Real.log 79 ≤ 4 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 80 := by
    exact_mod_cast logp 79 4 0 1 0 ((-1 : ℝ) / 80) (by norm_num) (by norm_num)
  have h83 : Real.log 83 ≤ 2 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 84 := by
    exact_mod_cast logp 83 2 1 0 1 ((-1 : ℝ) / 84) (by norm_num) (by norm_num)
  have h89 : Real.log 89 ≤ 1 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 90 := by
    exact_mod_cast logp 89 1 2 1 0 ((-1 : ℝ) / 90) (by norm_num) (by norm_num)
  have h97 : Real.log 97 ≤ 1 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 2 * Real.log 7 + (-1 : ℝ) / 98 := by
    exact_mod_cast logp 97 1 0 0 2 ((-1 : ℝ) / 98) (by norm_num) (by norm_num)
  have h101 : Real.log 101 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 100 := by
    exact_mod_cast logp 101 2 0 2 0 ((1 : ℝ) / 100) (by norm_num) (by norm_num)
  have h103 : Real.log 103 ≤ 0 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (-2 : ℝ) / 105 := by
    exact_mod_cast logp 103 0 1 1 1 ((-2 : ℝ) / 105) (by norm_num) (by norm_num)
  have h107 : Real.log 107 ≤ 2 * Real.log 2 + 3 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 108 := by
    exact_mod_cast logp 107 2 3 0 0 ((-1 : ℝ) / 108) (by norm_num) (by norm_num)
  have h109 : Real.log 109 ≤ 2 * Real.log 2 + 3 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 108 := by
    exact_mod_cast logp 109 2 3 0 0 ((1 : ℝ) / 108) (by norm_num) (by norm_num)
  have h113 : Real.log 113 ≤ 4 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (1 : ℝ) / 112 := by
    exact_mod_cast logp 113 4 0 0 1 ((1 : ℝ) / 112) (by norm_num) (by norm_num)
  have h127 : Real.log 127 ≤ 7 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 128 := by
    exact_mod_cast logp 127 7 0 0 0 ((-1 : ℝ) / 128) (by norm_num) (by norm_num)
  have h131 : Real.log 131 ≤ 7 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (3 : ℝ) / 128 := by
    exact_mod_cast logp 131 7 0 0 0 ((3 : ℝ) / 128) (by norm_num) (by norm_num)
  have h137 : Real.log 137 ≤ 0 * Real.log 2 + 3 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (2 : ℝ) / 135 := by
    exact_mod_cast logp 137 0 3 1 0 ((2 : ℝ) / 135) (by norm_num) (by norm_num)
  have h139 : Real.log 139 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 140 := by
    exact_mod_cast logp 139 2 0 1 1 ((-1 : ℝ) / 140) (by norm_num) (by norm_num)
  have h149 : Real.log 149 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 150 := by
    exact_mod_cast logp 149 1 1 2 0 ((-1 : ℝ) / 150) (by norm_num) (by norm_num)
  have h151 : Real.log 151 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 150 := by
    exact_mod_cast logp 151 1 1 2 0 ((1 : ℝ) / 150) (by norm_num) (by norm_num)
  have h157 : Real.log 157 ≤ 5 * Real.log 2 + 0 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-3 : ℝ) / 160 := by
    exact_mod_cast logp 157 5 0 1 0 ((-3 : ℝ) / 160) (by norm_num) (by norm_num)
  have h163 : Real.log 163 ≤ 1 * Real.log 2 + 4 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 162 := by
    exact_mod_cast logp 163 1 4 0 0 ((1 : ℝ) / 162) (by norm_num) (by norm_num)
  have h167 : Real.log 167 ≤ 3 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 168 := by
    exact_mod_cast logp 167 3 1 0 1 ((-1 : ℝ) / 168) (by norm_num) (by norm_num)
  have h173 : Real.log 173 ≤ 0 * Real.log 2 + 0 * Real.log 3 + 2 * Real.log 5 + 1 * Real.log 7 + (-2 : ℝ) / 175 := by
    exact_mod_cast logp 173 0 0 2 1 ((-2 : ℝ) / 175) (by norm_num) (by norm_num)
  have h179 : Real.log 179 ≤ 2 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 180 := by
    exact_mod_cast logp 179 2 2 1 0 ((-1 : ℝ) / 180) (by norm_num) (by norm_num)
  have h181 : Real.log 181 ≤ 2 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 180 := by
    exact_mod_cast logp 181 2 2 1 0 ((1 : ℝ) / 180) (by norm_num) (by norm_num)
  have h191 : Real.log 191 ≤ 6 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 192 := by
    exact_mod_cast logp 191 6 1 0 0 ((-1 : ℝ) / 192) (by norm_num) (by norm_num)
  have h193 : Real.log 193 ≤ 6 * Real.log 2 + 1 * Real.log 3 + 0 * Real.log 5 + 0 * Real.log 7 + (1 : ℝ) / 192 := by
    exact_mod_cast logp 193 6 1 0 0 ((1 : ℝ) / 192) (by norm_num) (by norm_num)
  have h197 : Real.log 197 ≤ 2 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 2 * Real.log 7 + (1 : ℝ) / 196 := by
    exact_mod_cast logp 197 2 0 0 2 ((1 : ℝ) / 196) (by norm_num) (by norm_num)
  have h199 : Real.log 199 ≤ 3 * Real.log 2 + 0 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 200 := by
    exact_mod_cast logp 199 3 0 2 0 ((-1 : ℝ) / 200) (by norm_num) (by norm_num)
  have h211 : Real.log 211 ≤ 1 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 1 * Real.log 7 + (1 : ℝ) / 210 := by
    exact_mod_cast logp 211 1 1 1 1 ((1 : ℝ) / 210) (by norm_num) (by norm_num)
  have h223 : Real.log 223 ≤ 5 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log 5 + 1 * Real.log 7 + (-1 : ℝ) / 224 := by
    exact_mod_cast logp 223 5 0 0 1 ((-1 : ℝ) / 224) (by norm_num) (by norm_num)
  have h227 : Real.log 227 ≤ 0 * Real.log 2 + 2 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (2 : ℝ) / 225 := by
    exact_mod_cast logp 227 0 2 2 0 ((2 : ℝ) / 225) (by norm_num) (by norm_num)
  have h229 : Real.log 229 ≤ 0 * Real.log 2 + 2 * Real.log 3 + 2 * Real.log 5 + 0 * Real.log 7 + (4 : ℝ) / 225 := by
    exact_mod_cast logp 229 0 2 2 0 ((4 : ℝ) / 225) (by norm_num) (by norm_num)
  have h233 : Real.log 233 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-7 : ℝ) / 240 := by
    exact_mod_cast logp 233 4 1 1 0 ((-7 : ℝ) / 240) (by norm_num) (by norm_num)
  have h239 : Real.log 239 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-1 : ℝ) / 240 := by
    exact_mod_cast logp 239 4 1 1 0 ((-1 : ℝ) / 240) (by norm_num) (by norm_num)
  have h234 : Real.log 234 ≤ 4 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 + 0 * Real.log 7 + (-6 : ℝ) / 240 := by
    exact_mod_cast logp 234 4 1 1 0 ((-6 : ℝ) / 240) (by norm_num) (by norm_num)
  linarith
end Formalism.DivisionValues.W5
