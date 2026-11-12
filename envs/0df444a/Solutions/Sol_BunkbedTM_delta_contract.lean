-- Prove2me | solution 1 for BunkbedTM.delta_contract
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T16:28:22.423401+00:00
-- url     : https://prove2.me/submissions/f2ce6d95-5aec-48f7-97fa-7de360c8d785

import Definitions.Def_BunkbedTransferClasses

/-!
# Contracting the 47 x 47 profile pairs onto the 15 classes

`Σ_j Σ_m δ(π_j, π_m) W(π_j) W(π_m) = Σ_{k<15} ck k * wk k`, where
`δ = [0@0 ↔ 9@1] - [0@0 ↔ 9@0]`. Each of the 47 rows of `δ` is evaluated by `decide` on
`glueConn`, and the level-1 sum is grouped by the 15 classes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

open Bunkbed Bunkbed.Hyper Bunkbed.TM Finset

namespace BunkbedTMContract

/-- The level-1 sum of one row of `δ`. -/
private def rowVal (j : Fin 47) (x y z u : Rat) : Rat :=
  ∑ m : Fin 47, ((if glueConn (stFinal j) (stFinal m) 1 then (1 : ℚ) else 0)
    - (if glueConn (stFinal j) (stFinal m) 0 then (1 : ℚ) else 0)) * wFinal m x y z u

private theorem wkEq0 (x y z u : Rat) : wk0 x y z u = wF7 x y z u + wF22 x y z u + wF35 x y z u := by
  simp only [wk0, wk0_p0, wk0_p1, wk0_p2, wk0_p3, wF7, wF22, wF35]; try ring
private theorem wkEq1 (x y z u : Rat) : wk1 x y z u = wF5 x y z u + wF20 x y z u + wF33 x y z u := by
  simp only [wk1, wk1_p0, wk1_p1, wk1_p2, wk1_p3, wF5, wF20, wF33]; try ring
private theorem wkEq2 (x y z u : Rat) : wk2 x y z u = wF1 x y z u + wF16 x y z u := by
  simp only [wk2, wk2_p0, wk2_p1, wk2_p2, wF1, wF16]; try ring
private theorem wkEq3 (x y z u : Rat) : wk3 x y z u = wF0 x y z u + wF15 x y z u := by
  simp only [wk3, wk3_p0, wk3_p1, wk3_p2, wF0, wF15]; try ring
private theorem wkEq4 (x y z u : Rat) : wk4 x y z u = wF6 x y z u + wF21 x y z u + wF34 x y z u := by
  simp only [wk4, wk4_p0, wk4_p1, wk4_p2, wF6, wF21, wF34]; try ring
private theorem wkEq5 (x y z u : Rat) : wk5 x y z u = wF4 x y z u + wF29 x y z u := by
  simp only [wk5, wk5_p0, wk5_p1, wF4, wF29]; try ring
private theorem wkEq6 (x y z u : Rat) : wk6 x y z u = wF3 x y z u + wF27 x y z u + wF45 x y z u := by
  simp only [wk6, wk6_p0, wk6_p1, wk6_p2, wk6_p3, wF3, wF27, wF45]; try ring
private theorem wkEq7 (x y z u : Rat) : wk7 x y z u = wF2 x y z u + wF25 x y z u + wF43 x y z u := by
  simp only [wk7, wk7_p0, wk7_p1, wk7_p2, wk7_p3, wF2, wF25, wF43]; try ring
private theorem wkEq8 (x y z u : Rat) : wk8 x y z u = wF14 x y z u + wF19 x y z u + wF32 x y z u := by
  simp only [wk8, wF14, wF19, wF32]; try ring
private theorem wkEq9 (x y z u : Rat) : wk9 x y z u = wF13 x y z u + wF26 x y z u + wF38 x y z u + wF44 x y z u := by
  simp only [wk9, wk9_p0, wk9_p1, wF13, wF26, wF38, wF44]; try ring
private theorem wkEq10 (x y z u : Rat) : wk10 x y z u = wF11 x y z u + wF18 x y z u + wF31 x y z u := by
  simp only [wk10, wk10_p0, wk10_p1, wk10_p2, wk10_p3, wF11, wF18, wF31]; try ring
private theorem wkEq11 (x y z u : Rat) : wk11 x y z u = wF8 x y z u + wF17 x y z u + wF30 x y z u := by
  simp only [wk11, wk11_p0, wk11_p1, wk11_p2, wk11_p3, wF8, wF17, wF30]; try ring
private theorem wkEq12 (x y z u : Rat) : wk12 x y z u = wF10 x y z u + wF28 x y z u + wF39 x y z u + wF41 x y z u := by
  simp only [wk12, wk12_p0, wk12_p1, wk12_p2, wF10, wF28, wF39, wF41]; try ring
private theorem wkEq13 (x y z u : Rat) : wk13 x y z u = wF12 x y z u + wF23 x y z u + wF36 x y z u + wF42 x y z u := by
  simp only [wk13, wk13_p0, wk13_p1, wk13_p2, wk13_p3, wk13_p4, wF12, wF23, wF36, wF42]; try ring
private theorem wkEq14 (x y z u : Rat) : wk14 x y z u = wF9 x y z u + wF24 x y z u + wF37 x y z u + wF40 x y z u + wF46 x y z u := by
  simp only [wk14, wk14_p0, wk14_p1, wk14_p2, wk14_p3, wk14_p4, wF9, wF24, wF37, wF40, wF46]; try ring
private theorem ckEq0 (x y z u : Rat) : ck0 x y z u = wF1 x y z u + wF3 x y z u - wF6 x y z u - wF10 x y z u + wF11 x y z u - wF13 x y z u + wF31 x y z u + wF33 x y z u + wF34 x y z u + wF37 x y z u + wF38 x y z u + wF39 x y z u - wF41 x y z u - wF44 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck0, ck0_p0, ck0_p1, ck0_p2, ck0_p3, ck0_p4, ck0_p5, wF1, wF3, wF6, wF10, wF11, wF13, wF31, wF33, wF34, wF37, wF38, wF39, wF41, wF44, wF45, wF46]; try ring
private theorem ckEq1 (x y z u : Rat) : ck1 x y z u = -wF0 x y z u - wF2 x y z u - wF4 x y z u - wF6 x y z u - wF8 x y z u - wF10 x y z u - wF13 x y z u - wF14 x y z u - wF30 x y z u - wF32 x y z u - wF35 x y z u - wF36 x y z u - wF41 x y z u - wF43 x y z u - wF44 x y z u - wF46 x y z u := by
  simp only [ck1, ck1_p0, ck1_p1, ck1_p2, ck1_p3, ck1_p4, wF0, wF2, wF4, wF6, wF8, wF10, wF13, wF14, wF30, wF32, wF35, wF36, wF41, wF43, wF44, wF46]; try ring
private theorem ckEq2 (x y z u : Rat) : ck2 x y z u = -wF0 x y z u - wF2 x y z u - wF4 x y z u - wF6 x y z u - wF7 x y z u - wF8 x y z u - wF10 x y z u - wF12 x y z u - wF13 x y z u - wF14 x y z u - wF30 x y z u - wF32 x y z u - wF34 x y z u - wF35 x y z u - wF36 x y z u - wF38 x y z u - wF39 x y z u - wF41 x y z u - wF42 x y z u - wF43 x y z u - wF44 x y z u - wF46 x y z u := by
  simp only [ck2, ck2_p0, ck2_p1, ck2_p2, ck2_p3, ck2_p4, wF0, wF2, wF4, wF6, wF7, wF8, wF10, wF12, wF13, wF14, wF30, wF32, wF34, wF35, wF36, wF38, wF39, wF41, wF42, wF43, wF44, wF46]; try ring
private theorem ckEq3 (x y z u : Rat) : ck3 x y z u = wF1 x y z u + wF3 x y z u + wF5 x y z u + wF9 x y z u + wF11 x y z u + wF31 x y z u + wF33 x y z u + wF37 x y z u + wF40 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck3, ck3_p0, ck3_p1, ck3_p2, ck3_p3, ck3_p4, ck3_p5, wF1, wF3, wF5, wF9, wF11, wF31, wF33, wF37, wF40, wF45, wF46]; try ring
private theorem ckEq4 (x y z u : Rat) : ck4 x y z u = wF1 x y z u + wF3 x y z u + wF5 x y z u + wF7 x y z u + wF9 x y z u + wF11 x y z u + wF12 x y z u + wF31 x y z u - wF35 x y z u - wF36 x y z u + wF40 x y z u + wF42 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck4, ck4_p0, ck4_p1, ck4_p2, ck4_p3, ck4_p4, ck4_p5, wF1, wF3, wF5, wF7, wF9, wF11, wF12, wF31, wF35, wF36, wF40, wF42, wF45, wF46]; try ring
private theorem ckEq5 (x y z u : Rat) : ck5 x y z u = wF1 x y z u - wF2 x y z u + wF5 x y z u + wF11 x y z u - wF12 x y z u - wF13 x y z u + wF31 x y z u + wF33 x y z u - wF36 x y z u - wF38 x y z u + wF40 x y z u + wF42 x y z u + wF43 x y z u + wF44 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck5, ck5_p0, ck5_p1, ck5_p2, ck5_p3, ck5_p4, wF1, wF2, wF5, wF11, wF12, wF13, wF31, wF33, wF36, wF38, wF40, wF42, wF43, wF44, wF45, wF46]; try ring
private theorem ckEq6 (x y z u : Rat) : ck6 x y z u = -wF0 x y z u - wF2 x y z u - wF6 x y z u - wF7 x y z u - wF8 x y z u - wF12 x y z u - wF13 x y z u - wF14 x y z u - wF30 x y z u - wF32 x y z u - wF34 x y z u - wF35 x y z u - wF36 x y z u - wF38 x y z u - wF41 x y z u - wF46 x y z u := by
  simp only [ck6, ck6_p0, ck6_p1, ck6_p2, ck6_p3, ck6_p4, wF0, wF2, wF6, wF7, wF8, wF12, wF13, wF14, wF30, wF32, wF34, wF35, wF36, wF38, wF41, wF46]; try ring
private theorem ckEq7 (x y z u : Rat) : ck7 x y z u = wF1 x y z u + wF3 x y z u + wF4 x y z u + wF5 x y z u + wF9 x y z u + wF10 x y z u + wF11 x y z u + wF31 x y z u + wF33 x y z u + wF37 x y z u + wF39 x y z u - wF41 x y z u - wF46 x y z u := by
  simp only [ck7, ck7_p0, ck7_p1, ck7_p2, ck7_p3, ck7_p4, ck7_p5, wF1, wF3, wF4, wF5, wF9, wF10, wF11, wF31, wF33, wF37, wF39, wF41, wF46]; try ring
private theorem ckEq8 (x y z u : Rat) : ck8 x y z u = wF1 x y z u + wF3 x y z u + wF5 x y z u + wF8 x y z u + wF9 x y z u + wF10 x y z u + wF11 x y z u + wF12 x y z u - wF30 x y z u + wF33 x y z u - wF36 x y z u - wF39 x y z u - wF41 x y z u - wF42 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck8, ck8_p0, ck8_p1, ck8_p2, ck8_p3, ck8_p4, ck8_p5, wF1, wF3, wF5, wF8, wF9, wF10, wF11, wF12, wF30, wF33, wF36, wF39, wF41, wF42, wF45, wF46]; try ring
private theorem ckEq9 (x y z u : Rat) : ck9 x y z u = wF1 x y z u + wF3 x y z u + wF4 x y z u + wF5 x y z u + wF7 x y z u + wF8 x y z u + wF9 x y z u + wF10 x y z u + wF11 x y z u + wF12 x y z u - wF30 x y z u - wF35 x y z u - wF36 x y z u - wF41 x y z u - wF46 x y z u := by
  simp only [ck9, ck9_p0, ck9_p1, ck9_p2, ck9_p3, ck9_p4, ck9_p5, wF1, wF3, wF4, wF5, wF7, wF8, wF9, wF10, wF11, wF12, wF30, wF35, wF36, wF41, wF46]; try ring
private theorem ckEq10 (x y z u : Rat) : ck10 x y z u = -wF0 x y z u - wF2 x y z u - wF4 x y z u - wF6 x y z u - wF7 x y z u - wF13 x y z u - wF14 x y z u - wF30 x y z u - wF34 x y z u - wF35 x y z u - wF36 x y z u - wF39 x y z u - wF41 x y z u - wF42 x y z u - wF43 x y z u - wF46 x y z u := by
  simp only [ck10, ck10_p0, ck10_p1, ck10_p2, ck10_p3, ck10_p4, wF0, wF2, wF4, wF6, wF7, wF13, wF14, wF30, wF34, wF35, wF36, wF39, wF41, wF42, wF43, wF46]; try ring
private theorem ckEq11 (x y z u : Rat) : ck11 x y z u = wF1 x y z u + wF3 x y z u + wF5 x y z u - wF13 x y z u - wF14 x y z u + wF31 x y z u + wF32 x y z u + wF33 x y z u + wF37 x y z u + wF38 x y z u + wF40 x y z u + wF44 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck11, ck11_p0, ck11_p1, ck11_p2, ck11_p3, ck11_p4, ck11_p5, wF1, wF3, wF5, wF13, wF14, wF31, wF32, wF33, wF37, wF38, wF40, wF44, wF45, wF46]; try ring
private theorem ckEq12 (x y z u : Rat) : ck12 x y z u = wF1 x y z u - wF2 x y z u + wF5 x y z u + wF7 x y z u - wF13 x y z u - wF14 x y z u + wF31 x y z u + wF32 x y z u - wF35 x y z u - wF36 x y z u + wF40 x y z u + wF42 x y z u + wF43 x y z u + wF44 x y z u + wF45 x y z u - wF46 x y z u := by
  simp only [ck12, ck12_p0, ck12_p1, ck12_p2, ck12_p3, ck12_p4, wF1, wF2, wF5, wF7, wF13, wF14, wF31, wF32, wF35, wF36, wF40, wF42, wF43, wF44, wF45, wF46]; try ring
private theorem ckEq13 (x y z u : Rat) : ck13 x y z u = wF1 x y z u + wF3 x y z u + wF4 x y z u - wF6 x y z u - wF13 x y z u - wF14 x y z u + wF31 x y z u + wF32 x y z u + wF33 x y z u + wF34 x y z u + wF37 x y z u + wF38 x y z u + wF39 x y z u - wF41 x y z u - wF46 x y z u := by
  simp only [ck13, ck13_p0, ck13_p1, ck13_p2, ck13_p3, ck13_p4, ck13_p5, wF1, wF3, wF4, wF6, wF13, wF14, wF31, wF32, wF33, wF34, wF37, wF38, wF39, wF41, wF46]; try ring
private theorem ckEq14 (x y z u : Rat) : ck14 x y z u = -wF0 x y z u - wF2 x y z u - wF6 x y z u - wF13 x y z u - wF14 x y z u - wF30 x y z u - wF35 x y z u - wF36 x y z u - wF41 x y z u - wF46 x y z u := by
  simp only [ck14, ck14_p0, ck14_p1, ck14_p2, ck14_p3, ck14_p4, wF0, wF2, wF6, wF13, wF14, wF30, wF35, wF36, wF41, wF46]; try ring

private theorem row0 (x y z u : Rat) : rowVal 0 x y z u = -wk1 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row1 (x y z u : Rat) : rowVal 1 x y z u = wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u + wk11 x y z u + wk12 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row2 (x y z u : Rat) : rowVal 2 x y z u = -wk1 x y z u - wk2 x y z u - wk5 x y z u - wk6 x y z u - wk10 x y z u - wk12 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row3 (x y z u : Rat) : rowVal 3 x y z u = wk0 x y z u + wk3 x y z u + wk4 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u + wk11 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row4 (x y z u : Rat) : rowVal 4 x y z u = -wk1 x y z u - wk2 x y z u + wk7 x y z u + wk9 x y z u - wk10 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row5 (x y z u : Rat) : rowVal 5 x y z u = wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u + wk11 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row6 (x y z u : Rat) : rowVal 6 x y z u = -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u - wk13 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row7 (x y z u : Rat) : rowVal 7 x y z u = -wk2 x y z u + wk4 x y z u - wk6 x y z u + wk9 x y z u - wk10 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row8 (x y z u : Rat) : rowVal 8 x y z u = -wk1 x y z u - wk2 x y z u - wk6 x y z u + wk8 x y z u + wk9 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row9 (x y z u : Rat) : rowVal 9 x y z u = wk3 x y z u + wk4 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row10 (x y z u : Rat) : rowVal 10 x y z u = -wk0 x y z u - wk1 x y z u - wk2 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row11 (x y z u : Rat) : rowVal 11 x y z u = wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row12 (x y z u : Rat) : rowVal 12 x y z u = -wk2 x y z u + wk4 x y z u - wk5 x y z u - wk6 x y z u + wk8 x y z u + wk9 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row13 (x y z u : Rat) : rowVal 13 x y z u = -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk5 x y z u - wk6 x y z u - wk10 x y z u - wk11 x y z u - wk12 x y z u - wk13 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row14 (x y z u : Rat) : rowVal 14 x y z u = -wk1 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u - wk11 x y z u - wk12 x y z u - wk13 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row15 (x y z u : Rat) : rowVal 15 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row16 (x y z u : Rat) : rowVal 16 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row17 (x y z u : Rat) : rowVal 17 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row18 (x y z u : Rat) : rowVal 18 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row19 (x y z u : Rat) : rowVal 19 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row20 (x y z u : Rat) : rowVal 20 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row21 (x y z u : Rat) : rowVal 21 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row22 (x y z u : Rat) : rowVal 22 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row23 (x y z u : Rat) : rowVal 23 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row24 (x y z u : Rat) : rowVal 24 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row25 (x y z u : Rat) : rowVal 25 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row26 (x y z u : Rat) : rowVal 26 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row27 (x y z u : Rat) : rowVal 27 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row28 (x y z u : Rat) : rowVal 28 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row29 (x y z u : Rat) : rowVal 29 x y z u = 0 := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row30 (x y z u : Rat) : rowVal 30 x y z u = -wk1 x y z u - wk2 x y z u - wk6 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row31 (x y z u : Rat) : rowVal 31 x y z u = wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk11 x y z u + wk12 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row32 (x y z u : Rat) : rowVal 32 x y z u = -wk1 x y z u - wk2 x y z u - wk6 x y z u + wk11 x y z u + wk12 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row33 (x y z u : Rat) : rowVal 33 x y z u = wk0 x y z u + wk3 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk11 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row34 (x y z u : Rat) : rowVal 34 x y z u = wk0 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row35 (x y z u : Rat) : rowVal 35 x y z u = -wk1 x y z u - wk2 x y z u - wk4 x y z u - wk6 x y z u - wk9 x y z u - wk10 x y z u - wk12 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row36 (x y z u : Rat) : rowVal 36 x y z u = -wk1 x y z u - wk2 x y z u - wk4 x y z u - wk5 x y z u - wk6 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk12 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row37 (x y z u : Rat) : rowVal 37 x y z u = wk0 x y z u + wk3 x y z u + wk7 x y z u + wk11 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row38 (x y z u : Rat) : rowVal 38 x y z u = wk0 x y z u - wk2 x y z u - wk5 x y z u - wk6 x y z u + wk11 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row39 (x y z u : Rat) : rowVal 39 x y z u = wk0 x y z u - wk2 x y z u + wk7 x y z u - wk8 x y z u - wk10 x y z u + wk13 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row40 (x y z u : Rat) : rowVal 40 x y z u = wk3 x y z u + wk4 x y z u + wk5 x y z u + wk11 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row41 (x y z u : Rat) : rowVal 41 x y z u = -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk6 x y z u - wk7 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk13 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row42 (x y z u : Rat) : rowVal 42 x y z u = -wk2 x y z u + wk4 x y z u + wk5 x y z u - wk8 x y z u - wk10 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row43 (x y z u : Rat) : rowVal 43 x y z u = -wk1 x y z u - wk2 x y z u + wk5 x y z u - wk10 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row44 (x y z u : Rat) : rowVal 44 x y z u = -wk0 x y z u - wk1 x y z u - wk2 x y z u + wk5 x y z u + wk11 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row45 (x y z u : Rat) : rowVal 45 x y z u = wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk8 x y z u + wk11 x y z u + wk12 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring
private theorem row46 (x y z u : Rat) : rowVal 46 x y z u = -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk3 x y z u - wk4 x y z u - wk5 x y z u - wk6 x y z u - wk7 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk11 x y z u - wk12 x y z u - wk13 x y z u - wk14 x y z u := by
  simp only [rowVal]
  try simp only [wkEq0, wkEq1, wkEq2, wkEq3, wkEq4, wkEq5, wkEq6, wkEq7, wkEq8, wkEq9, wkEq10, wkEq11, wkEq12, wkEq13, wkEq14]
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, stFinal, wFinal,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue, if_true, if_false,
    sub_zero, zero_sub, sub_self, one_mul, neg_mul, zero_mul, add_zero, zero_add]
  try ring

/-- Each row of `δ`, contracted against the level-1 class weights. -/
private theorem rowAll (j : Fin 47) (x y z u : Rat) : rowVal j x y z u = ![fun x y z u => -wk1 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u - wk14 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u + wk11 x y z u + wk12 x y z u + wk13 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u - wk5 x y z u - wk6 x y z u - wk10 x y z u - wk12 x y z u - wk14 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk4 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u + wk11 x y z u + wk13 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u + wk7 x y z u + wk9 x y z u - wk10 x y z u + wk13 x y z u, fun x y z u => wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u + wk11 x y z u + wk12 x y z u, fun x y z u => -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u - wk13 x y z u - wk14 x y z u, fun x y z u => -wk2 x y z u + wk4 x y z u - wk6 x y z u + wk9 x y z u - wk10 x y z u + wk12 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u - wk6 x y z u + wk8 x y z u + wk9 x y z u, fun x y z u => wk3 x y z u + wk4 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u, fun x y z u => -wk0 x y z u - wk1 x y z u - wk2 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk9 x y z u, fun x y z u => -wk2 x y z u + wk4 x y z u - wk5 x y z u - wk6 x y z u + wk8 x y z u + wk9 x y z u, fun x y z u => -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk5 x y z u - wk6 x y z u - wk10 x y z u - wk11 x y z u - wk12 x y z u - wk13 x y z u - wk14 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u - wk11 x y z u - wk12 x y z u - wk13 x y z u - wk14 x y z u, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => 0, fun x y z u => -wk1 x y z u - wk2 x y z u - wk6 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk14 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk7 x y z u + wk11 x y z u + wk12 x y z u + wk13 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u - wk6 x y z u + wk11 x y z u + wk12 x y z u + wk13 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk5 x y z u + wk7 x y z u + wk8 x y z u + wk11 x y z u + wk13 x y z u, fun x y z u => wk0 x y z u - wk2 x y z u - wk6 x y z u - wk10 x y z u + wk13 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u - wk4 x y z u - wk6 x y z u - wk9 x y z u - wk10 x y z u - wk12 x y z u - wk14 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u - wk4 x y z u - wk5 x y z u - wk6 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk12 x y z u - wk14 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk7 x y z u + wk11 x y z u + wk13 x y z u, fun x y z u => wk0 x y z u - wk2 x y z u - wk5 x y z u - wk6 x y z u + wk11 x y z u + wk13 x y z u, fun x y z u => wk0 x y z u - wk2 x y z u + wk7 x y z u - wk8 x y z u - wk10 x y z u + wk13 x y z u, fun x y z u => wk3 x y z u + wk4 x y z u + wk5 x y z u + wk11 x y z u + wk12 x y z u, fun x y z u => -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk6 x y z u - wk7 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk13 x y z u - wk14 x y z u, fun x y z u => -wk2 x y z u + wk4 x y z u + wk5 x y z u - wk8 x y z u - wk10 x y z u + wk12 x y z u, fun x y z u => -wk1 x y z u - wk2 x y z u + wk5 x y z u - wk10 x y z u + wk12 x y z u, fun x y z u => -wk0 x y z u - wk1 x y z u - wk2 x y z u + wk5 x y z u + wk11 x y z u + wk12 x y z u, fun x y z u => wk0 x y z u + wk3 x y z u + wk4 x y z u + wk5 x y z u + wk8 x y z u + wk11 x y z u + wk12 x y z u, fun x y z u => -wk0 x y z u - wk1 x y z u - wk2 x y z u - wk3 x y z u - wk4 x y z u - wk5 x y z u - wk6 x y z u - wk7 x y z u - wk8 x y z u - wk9 x y z u - wk10 x y z u - wk11 x y z u - wk12 x y z u - wk13 x y z u - wk14 x y z u] j x y z u := by
  fin_cases j
  · exact row0 x y z u
  · exact row1 x y z u
  · exact row2 x y z u
  · exact row3 x y z u
  · exact row4 x y z u
  · exact row5 x y z u
  · exact row6 x y z u
  · exact row7 x y z u
  · exact row8 x y z u
  · exact row9 x y z u
  · exact row10 x y z u
  · exact row11 x y z u
  · exact row12 x y z u
  · exact row13 x y z u
  · exact row14 x y z u
  · exact row15 x y z u
  · exact row16 x y z u
  · exact row17 x y z u
  · exact row18 x y z u
  · exact row19 x y z u
  · exact row20 x y z u
  · exact row21 x y z u
  · exact row22 x y z u
  · exact row23 x y z u
  · exact row24 x y z u
  · exact row25 x y z u
  · exact row26 x y z u
  · exact row27 x y z u
  · exact row28 x y z u
  · exact row29 x y z u
  · exact row30 x y z u
  · exact row31 x y z u
  · exact row32 x y z u
  · exact row33 x y z u
  · exact row34 x y z u
  · exact row35 x y z u
  · exact row36 x y z u
  · exact row37 x y z u
  · exact row38 x y z u
  · exact row39 x y z u
  · exact row40 x y z u
  · exact row41 x y z u
  · exact row42 x y z u
  · exact row43 x y z u
  · exact row44 x y z u
  · exact row45 x y z u
  · exact row46 x y z u

end BunkbedTMContract

open Bunkbed Bunkbed.Hyper Bunkbed.TM BunkbedTMContract Finset in
/-- **Contracting the profile pairs onto the fifteen classes.** -/
theorem solution (x y z u : Rat) :
    (∑ j : Fin 47, wFinal j x y z u *
       (∑ m : Fin 47, ((if glueConn (stFinal j) (stFinal m) 1 then (1 : ℚ) else 0)
          - (if glueConn (stFinal j) (stFinal m) 0 then (1 : ℚ) else 0)) * wFinal m x y z u))
      = ck0 x y z u * wk0 x y z u + ck1 x y z u * wk1 x y z u + ck2 x y z u * wk2 x y z u + ck3 x y z u * wk3 x y z u + ck4 x y z u * wk4 x y z u + ck5 x y z u * wk5 x y z u + ck6 x y z u * wk6 x y z u + ck7 x y z u * wk7 x y z u + ck8 x y z u * wk8 x y z u + ck9 x y z u * wk9 x y z u + ck10 x y z u * wk10 x y z u + ck11 x y z u * wk11 x y z u + ck12 x y z u * wk12 x y z u + ck13 x y z u * wk13 x y z u + ck14 x y z u * wk14 x y z u := by
  rw [Finset.sum_congr rfl (fun (j : Fin 47) _ => by rw [show (∑ m : Fin 47, ((if glueConn (stFinal j) (stFinal m) 1 then (1 : ℚ) else 0) - (if glueConn (stFinal j) (stFinal m) 0 then (1 : ℚ) else 0)) * wFinal m x y z u) = rowVal j x y z u from rfl, rowAll j])]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.isValue, wFinal]
  rw [ckEq0, ckEq1, ckEq2, ckEq3, ckEq4, ckEq5, ckEq6, ckEq7, ckEq8, ckEq9, ckEq10, ckEq11, ckEq12, ckEq13, ckEq14]
  ring

#print axioms solution
