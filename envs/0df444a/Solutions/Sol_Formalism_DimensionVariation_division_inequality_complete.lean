-- Prove2me | solution 1 for Formalism.DimensionVariation.division_inequality_complete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:18.469811+00:00
-- url     : https://prove2.me/submissions/17ce1595-038e-4155-b265-856d2c86bc0a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_divisor_inequality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : DivIneqRecord6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo logT aT logH x eps L b a rd La L' B0 Nc xe m f k N nV S tt η
    w'' b' lam0 C C0 Lpass Eb logOm pq w eE δ q1 q2 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13
    z14 z15 z16 z17 z18 z19 z20 z21 zb z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35
    hC hCC hnV hnVN hL' hCL y1 y2 y5 y6
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ L := by rw [z3]; exact Real.rpow_nonneg hx0.le _
  have hLa0 : 0 ≤ La := by
    rw [z9, z5, z4, Real.log_mul (by positivity) (by linarith),
      Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have := Real.log_nonneg z1
    have := Real.log_nonneg z6
    linarith
  have hC0 : 0 ≤ C0 := le_trans hC hCC
  have hfN : 0 ≤ f * N ^ 2 := by positivity
  refine Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo
    (recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C)
    (recordA TT aT logT f m N S η b' La C) (∑ j, recordX logH f nV L' C j) logT
    (fun j => sizeB ν logOm f m N L La C j) aT
    (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) logH
    x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' 1 lam0 C0 Lpass Eb (m * (C * f * nV ^ 2 * L'))
    (C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La) logOm
    (fun _ => C * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) pq w eE δ
    q1 q2 rfl (fun j => le_refl _) ?_ (le_refl _) q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
    z16 z17 z18 z19 z20 z21 le_rfl z23 z24 z25 z26 (by simpa using z27) z28 z29 z30 z31 z32 z33 z34 z35
    hC0 y1 y2 ?_ ?_ ?_ y5 y6
  · unfold recordX
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, z13]
  · intro j
    have a1 : 0 ≤ f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L := by positivity
    have a2 : f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L ≤
        f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L := by nlinarith
    exact mul_le_mul hCC a2 a1 hC0
  · have a1 : nV ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hnV hnVN 2
    have a2 : f * nV ^ 2 ≤ f * N ^ 2 := mul_le_mul_of_nonneg_left a1 (by linarith)
    have a3 : f * nV ^ 2 * (C * L') ≤ f * N ^ 2 * (C0 * La) :=
      mul_le_mul a2 hCL (mul_nonneg hC hL') hfN
    have a4 := mul_le_mul_of_nonneg_left a3 (by linarith : (0 : ℝ) ≤ m)
    calc m * (C * f * nV ^ 2 * L') = m * (f * nV ^ 2 * (C * L')) := by ring
      _ ≤ m * (f * N ^ 2 * (C0 * La)) := a4
      _ = C0 * m * f * N ^ 2 * La := by ring
  · have a1 : 0 ≤ ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC a1) hLa0
end Formalism.DimensionVariation
