-- Prove2me | solution 1 for FourierJacobi.Analysis.i2Classify_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:33.267921+00:00
-- url     : https://prove2.me/submissions/d2ed5cfb-194a-44fb-8745-48a306ef73a2

import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Mathlib.Data.Fintype.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Partition
import Theorems.Thm_FourierJacobi_Analysis_i2Case10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row0
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row1
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row10
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row11
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row12
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row13
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row14
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row15
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row16
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row17
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row18
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row19
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row2
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row20
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row21
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row22
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row23
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row24
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row3
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row4
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row5
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row6
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row7
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row8
import Theorems.Thm_FourierJacobi_Analysis_i2DepthPredicate_row9
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row0
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row1
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row10
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row11
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row12
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row13
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row14
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row15
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row16
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row17
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row18
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row19
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row2
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row20
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row21
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row22
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row23
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row24
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row3
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row4
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row5
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row6
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row7
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row8
import Theorems.Thm_FourierJacobi_Analysis_i2SpatialPredicate_row9
attribute [local simp] FourierJacobi.Analysis.i2Case10Equiv_val
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row0
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row1
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row10
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row11
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row12
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row13
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row14
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row15
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row16
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row17
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row18
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row19
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row2
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row20
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row21
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row22
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row23
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row24
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row3
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row4
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row5
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row6
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row7
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row8
attribute [local simp] FourierJacobi.Analysis.i2DepthPredicate_row9
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row0
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row1
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row10
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row11
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row12
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row13
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row14
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row15
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row16
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row17
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row18
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row19
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row2
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row20
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row21
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row22
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row23
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row24
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row3
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row4
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row5
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row6
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row7
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row8
attribute [local simp] FourierJacobi.Analysis.i2SpatialPredicate_row9



set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (ν : Fin 25) (k j h : ℤ) (c : ℕ)
    (hp : i2SpatialPredicate ν (k,j,h)) (hc : i2DepthPredicate ν c) :
    i2Classify k j h c = ν := by
  fin_cases ν
  · change 2 ≤ k ∧ -2*k ≤ j ∧ -k ≤ h at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : -2*k ≤ j := by omega
    have h2 : ¬(h < -k) := by omega
    have h3 : 2 ≤ k := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_pos h1, if_neg h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 1 ∧ -2 ≤ j ∧ -1 ≤ h at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : -2*k ≤ j := by omega
    have h2 : ¬(h < -k) := by omega
    have h3 : ¬(2 ≤ k) := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_pos h1, if_neg h2, if_neg h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ -2*k ≤ j ∧ h < -k at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : -2*k ≤ j := by omega
    have h2 : h < -k := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_pos h1, if_pos h2,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j-1 ≤ 2*h at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : j-1 ≤ 2*h := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    change c = 0 at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : 2*h = j-2 := by omega
    have h5 : c = 0 := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    change c = 1 at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : 2*h = j-2 := by omega
    have h5 : ¬(c = 0) := by omega
    have h6 : c = 1 := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, if_pos h6,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    change 2 ≤ c at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : 2*h = j-2 := by omega
    have h5 : ¬(c = 0) := by omega
    have h6 : ¬(c = 1) := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, if_neg h6,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-3 at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : ¬(h < k+j) := by omega
    have h3 : ¬(j-1 ≤ 2*h) := by omega
    have h4 : ¬(2*h = j-2) := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change 1 ≤ k ∧ j < -2*k ∧ h < k+j at hp
    change True at hc
    have h0 : 1 ≤ k := by omega
    have h1 : ¬(-2*k ≤ j) := by omega
    have h2 : h < k+j := by omega
    simp only [i2Classify, i2TailClassify, if_pos h0, if_neg h1, if_pos h2,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 0 ∧ 0 ≤ j ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : k = 0 := by omega
    have h2 : -1 ≤ j := by omega
    have h3 : ¬(h ≤ -2) := by omega
    have h4 : 0 ≤ j := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 0 ∧ j = -1 ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : k = 0 := by omega
    have h2 : -1 ≤ j := by omega
    have h3 : ¬(h ≤ -2) := by omega
    have h4 : ¬(0 ≤ j) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = 0 ∧ -1 ≤ j ∧ h ≤ -2 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : k = 0 := by omega
    have h2 : -1 ≤ j := by omega
    have h3 : h ≤ -2 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_pos h1, if_pos h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = -1 ∧ 0 ≤ j ∧ 0 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : 0 ≤ j := by omega
    have h3 : ¬(h ≤ -1) := by omega
    have h4 : k = -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = -1 ∧ j = -1 ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : ¬(h ≤ -2) := by omega
    have h5 : k = -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k = -1 ∧ j = -1 ∧ h ≤ -2 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : h ≤ -2 := by omega
    have h5 : k = -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -2 ∧ 0 ≤ j ∧ 0 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : 0 ≤ j := by omega
    have h3 : ¬(h ≤ -1) := by omega
    have h4 : ¬(k = -1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -2 ∧ j = -1 ∧ -1 ≤ h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : ¬(h ≤ -2) := by omega
    have h5 : ¬(k = -1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_neg h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -2 ∧ j = -1 ∧ h ≤ -2 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : j = -1 := by omega
    have h4 : h ≤ -2 := by omega
    have h5 : ¬(k = -1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_neg h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ -1 ∧ 0 ≤ j ∧ h ≤ -1 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(k = 0) := by omega
    have h2 : 0 ≤ j := by omega
    have h3 : h ≤ -1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_pos h2, if_pos h3,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ j-1 ≤ 2*h at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : j-1 ≤ 2*h := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    change c = 0 at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : 2*h = j-2 := by omega
    have h7 : c = 0 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_pos h7,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    change c = 1 at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : 2*h = j-2 := by omega
    have h7 : ¬(c = 0) := by omega
    have h8 : c = 1 := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg h7, if_pos h8,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    change 2 ≤ c at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : 2*h = j-2 := by omega
    have h7 : ¬(c = 0) := by omega
    have h8 : ¬(c = 1) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, if_neg h7, if_neg h8,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h ≤ j-3 at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : ¬(h < j) := by omega
    have h5 : ¬(j-1 ≤ 2*h) := by omega
    have h6 : ¬(2*h = j-2) := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
  · change k ≤ 0 ∧ j < -1 ∧ h < j at hp
    change True at hc
    have h0 : ¬(1 ≤ k) := by omega
    have h1 : ¬(-1 ≤ j) := by omega
    have h2 : ¬(0 ≤ j) := by omega
    have h3 : ¬(j = -1) := by omega
    have h4 : h < j := by omega
    simp only [i2Classify, i2TailClassify, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
      if_pos (rfl : true = true), if_neg (by decide : ¬ false = true), ite_self]
    rfl
end FourierJacobi.Analysis
