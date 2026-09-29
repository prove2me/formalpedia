-- Prove2me | solution 1 for Freiman.section14_row_modes
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-18T10:11:57.478041+00:00
-- url     : https://prove2.me/submissions/53bbb940-d9e6-4811-b0de-97ab9bb79982

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

open Freiman

namespace S14RM

/-! ### Quadratic surd arithmetic -/

lemma sq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma sq21 : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
lemma r3lb : (17/10:ℝ) < Real.sqrt 3 := by nlinarith [sq3, Real.sqrt_nonneg (3:ℝ)]
lemma r3ub : Real.sqrt 3 < 18/10 := by nlinarith [sq3, Real.sqrt_nonneg (3:ℝ)]
lemma r21lb : (458/100:ℝ) < Real.sqrt 21 := by nlinarith [sq21, Real.sqrt_nonneg (21:ℝ)]
lemma r21ub : Real.sqrt 21 < 459/100 := by nlinarith [sq21, Real.sqrt_nonneg (21:ℝ)]

lemma pe_cons (a : ℕ+) (w : List ℕ+) (x v u c : ℝ)
    (h : prefixEval w x = v) (hv : 0 ≤ v) (hc : (((a:ℕ)):ℝ) = c)
    (hu : u * (c + v) = 1) : prefixEval (a :: w) x = u := by
  subst hc
  have ha : (0:ℝ) < (((a:ℕ)):ℝ) := by exact_mod_cast a.pos
  have hd : (((a:ℕ)):ℝ) + v ≠ 0 := ne_of_gt (by linarith)
  show 1 / ((((a:ℕ)):ℝ) + prefixEval w x) = u
  rw [h, div_eq_iff hd]
  linarith [hu]

lemma peA0 : prefixEval [] lowerTau = (-1) + (1)*Real.sqrt 3 := by
  show lowerTau = _
  unfold lowerTau; ring
lemma peA1 : prefixEval ([3] : List ℕ+) lowerTau = (2) + (-1)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (3) peA0 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1) * sq3)
lemma peA2 : prefixEval ([1,3] : List ℕ+) lowerTau = (1/2) + (1/6)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (1) peA1 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/6) * sq3)
lemma peA3 : prefixEval ([1,1,3] : List ℕ+) lowerTau = (9/13) + (-1/13)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (1) peA2 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1/78) * sq3)
lemma peA4 : prefixEval ([3,1,1,3] : List ℕ+) lowerTau = (16/59) + (1/177)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (3) peA3 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/2301) * sq3)
lemma peA5 : prefixEval ([2,1,3] : List ℕ+) lowerTau = (15/37) + (-1/37)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (2) peA2 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1/222) * sq3)
lemma peA6 : prefixEval ([1,2,1,3] : List ℕ+) lowerTau = (52/73) + (1/73)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (1) peA5 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/2701) * sq3)
lemma peA7 : prefixEval ([1,1,2,1,3] : List ℕ+) lowerTau = (125/214) + (-1/214)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (1) peA6 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1/15622) * sq3)
lemma peA8 : prefixEval ([2,1,2,1,3] : List ℕ+) lowerTau = (66/179) + (-1/537)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (2) peA6 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1/39201) * sq3)
lemma peA9 : prefixEval ([3,2,1,3] : List ℕ+) lowerTau = (42/143) + (1/429)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (3) peA5 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/15873) * sq3)
lemma peA10 : prefixEval ([2,3] : List ℕ+) lowerTau = (4/13) + (1/13)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (2) peA1 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/13) * sq3)
lemma peA11 : prefixEval ([3,2,3] : List ℕ+) lowerTau = (43/142) + (-1/142)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (3) peA10 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1/1846) * sq3)
lemma peA12 : prefixEval ([3,3] : List ℕ+) lowerTau = (5/22) + (1/22)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (3) peA1 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/22) * sq3)
lemma peB0 : prefixEval [] (lowerTau/2) = (-1/2) + (1/2)*Real.sqrt 3 := by
  show lowerTau/2 = _
  unfold lowerTau; ring
lemma peB1 : prefixEval ([2] : List ℕ+) (lowerTau/2) = (1) + (-1/3)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (2) peB0 (by linarith [r3lb]) (by norm_num)
    (by linear_combination (-1/6) * sq3)
lemma peB2 : prefixEval ([3,2] : List ℕ+) (lowerTau/2) = (12/47) + (1/47)*Real.sqrt 3 :=
  pe_cons _ _ _ _ _ (3) peB1 (by linarith [r3ub]) (by norm_num)
    (by linear_combination (-1/141) * sq3)
lemma peC0 : prefixEval [] lowerAlpha = (-1/2) + (1/6)*Real.sqrt 21 := by
  show lowerAlpha = _
  unfold lowerAlpha; ring
lemma peC1 : prefixEval ([3] : List ℕ+) lowerAlpha = (15/34) + (-1/34)*Real.sqrt 21 :=
  pe_cons _ _ _ _ _ (3) peC0 (by linarith [r21lb]) (by norm_num)
    (by linear_combination (-1/204) * sq21)
lemma peC2 : prefixEval ([3,3] : List ℕ+) lowerAlpha = (39/134) + (1/402)*Real.sqrt 21 :=
  pe_cons _ _ _ _ _ (3) peC1 (by linarith [r21ub]) (by norm_num)
    (by linear_combination (-1/13668) * sq21)
lemma peC3 : prefixEval ([1,3] : List ℕ+) lowerAlpha = (7/10) + (1/70)*Real.sqrt 21 :=
  pe_cons _ _ _ _ _ (1) peC1 (by linarith [r21ub]) (by norm_num)
    (by linear_combination (-1/2380) * sq21)
lemma peC4 : prefixEval ([1,1,3] : List ℕ+) lowerAlpha = (119/202) + (-1/202)*Real.sqrt 21 :=
  pe_cons _ _ _ _ _ (1) peC3 (by linarith [r21lb]) (by norm_num)
    (by linear_combination (-1/14140) * sq21)
lemma peD0 : prefixEval [] lowerBeta = (-3/2) + (1/2)*Real.sqrt 21 := by
  show lowerBeta = _
  unfold lowerBeta; ring
lemma peD1 : prefixEval ([1] : List ℕ+) lowerBeta = (1/10) + (1/10)*Real.sqrt 21 :=
  pe_cons _ _ _ _ _ (1) peD0 (by linarith [r21lb]) (by norm_num)
    (by linear_combination (1/20) * sq21)

lemma t3  : lowerTheta 3  = (2:ℝ) + (-1)*Real.sqrt 3 := peA1
lemma t13 : lowerTheta 13 = (16/59:ℝ) + (1/177)*Real.sqrt 3 := peA4
lemma t16 : lowerTheta 16 = (43/142:ℝ) + (-1/142)*Real.sqrt 3 := peA11
lemma t18 : lowerTheta 18 = (12/47:ℝ) + (1/47)*Real.sqrt 3 := peB2
lemma t20 : lowerTheta 20 = (42/143:ℝ) + (1/429)*Real.sqrt 3 := peA9
lemma t22 : lowerTheta 22 = (39/134:ℝ) + (1/402)*Real.sqrt 21 := peC2
lemma t25 : lowerTheta 25 = (5/22:ℝ) + (1/22)*Real.sqrt 3 := peA12
lemma t28 : lowerTheta 28 = (15/34:ℝ) + (-1/34)*Real.sqrt 21 := peC1
lemma t35 : lowerTheta 35 = (66/179:ℝ) + (-1/537)*Real.sqrt 3 := peA8
lemma t63 : lowerTheta 63 = (4/13:ℝ) + (1/13)*Real.sqrt 3 := peA10
lemma t65 : lowerTheta 65 = (1/10:ℝ) + (1/10)*Real.sqrt 21 := peD1
lemma t66 : lowerTheta 66 = (9/13:ℝ) + (-1/13)*Real.sqrt 3 := peA3
lemma t68 : lowerTheta 68 = (119/202:ℝ) + (-1/202)*Real.sqrt 21 := peC4
lemma t70 : lowerTheta 70 = (125/214:ℝ) + (-1/214)*Real.sqrt 3 := peA7
lemma t90 : lowerTheta 90 = (52/73:ℝ) + (1/73)*Real.sqrt 3 := peA6
lemma t94 : lowerTheta 94 = (1/2:ℝ) + (1/6)*Real.sqrt 3 := peA2

lemma C17 : |(lowerTheta 16 - lowerTheta 13)/(lowerTheta 18 - lowerTheta 25)|
    = (-145/4189:ℝ) + (5312/12567)*Real.sqrt 3 := by
  rw [t16, t13, t18, t25]
  have hden : ((12/47:ℝ) + (1/47)*Real.sqrt 3) - ((5/22:ℝ) + (1/22)*Real.sqrt 3) ≠ 0 :=
    ne_of_lt (by linarith [r3lb])
  have key : (((43/142:ℝ) + (-1/142)*Real.sqrt 3) - ((16/59:ℝ) + (1/177)*Real.sqrt 3)) /
      (((12/47:ℝ) + (1/47)*Real.sqrt 3) - ((5/22:ℝ) + (1/22)*Real.sqrt 3))
      = -(((-145/4189:ℝ)) + (5312/12567)*Real.sqrt 3) := by
    rw [div_eq_iff hden]
    linear_combination (-66400/6497139 : ℝ) * sq3
  rw [key, abs_neg, abs_of_nonneg (by linarith [r3lb] :
    (0:ℝ) ≤ ((-145/4189:ℝ)) + (5312/12567)*Real.sqrt 3)]

lemma C21 : |(lowerTheta 63 - lowerTheta 3)/(lowerTheta 20 - lowerTheta 66)|
    = (-2334/781:ℝ) + (1646/781)*Real.sqrt 3 := by
  rw [t63, t3, t20, t66]
  have hden : ((42/143:ℝ) + (1/429)*Real.sqrt 3) - ((9/13:ℝ) + (-1/13)*Real.sqrt 3) ≠ 0 :=
    ne_of_lt (by linarith [r3ub])
  have key : (((4/13:ℝ) + (1/13)*Real.sqrt 3) - ((2:ℝ) + (-1)*Real.sqrt 3)) /
      (((42/143:ℝ) + (1/429)*Real.sqrt 3) - ((9/13:ℝ) + (-1/13)*Real.sqrt 3))
      = -(((-2334/781:ℝ)) + (1646/781)*Real.sqrt 3) := by
    rw [div_eq_iff hden]
    linear_combination (55964/335049 : ℝ) * sq3
  rw [key, abs_neg, abs_of_nonneg (by linarith [r3lb] :
    (0:ℝ) ≤ ((-2334/781:ℝ)) + (1646/781)*Real.sqrt 3)]

/-! ### Catalog thresholds are the report's scalar cuts -/

lemma lthr (p : LowerPair) (c : ℝ) (i j k l : ℕ) :
    lowerThreshold p c i j k l =
      c * ((1+ section14S p * lowerTheta j)*(1+ section14S p * lowerTheta l)) /
        ((1 + section14R p * lowerTheta i)*(1+ section14R p * lowerTheta k)) := rfl

lemma h2def (p : LowerPair) : lowerH p 2 ↔ lowerThreshold p (37/50) 63 70 66 90 < section14Q p := Iff.rfl
lemma h5def (p : LowerPair) : lowerH p 5 ↔ section14Q p < lowerThreshold p (279/500) 35 63 63 70 := Iff.rfl
lemma h6def (p : LowerPair) : lowerH p 6 ↔ section14Q p < lowerThreshold p (69/200) 22 65 28 68 := Iff.rfl
lemma h7def (p : LowerPair) : lowerH p 7 ↔ section14Q p < lowerThreshold p (161/500) 3 63 25 66 := Iff.rfl
lemma h17def (p : LowerPair) : lowerH p 17 ↔
    lowerThreshold p (|(lowerTheta 16-lowerTheta 13)/(lowerTheta 18-lowerTheta 25)|) 13 18 16 25
      < section14Q p := Iff.rfl
lemma h21def (p : LowerPair) : lowerH p 21 ↔
    section14Q p <
      lowerThreshold p (|(lowerTheta 63-lowerTheta 3)/(lowerTheta 20-lowerTheta 66)|) 3 20 63 66 := Iff.rfl
lemma h23def (p : LowerPair) : lowerH p 23 ↔ lowerThreshold p (139/250) 63 70 66 94 < section14Q p := Iff.rfl

set_option maxRecDepth 100000 in
lemma V22 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 22) (section14R p) (section14S p)
      = lowerThreshold p (37/50) 63 70 66 90 := by
  rw [show section14Threshold section14Catalog 22 =
      (⟨⟨37/50,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨125/214,-1/214,0,0⟩,⟨52/73,1/73,0,0⟩⟩ :
        CertThreshold) from rfl, lthr, t63, t70, t66, t90]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

set_option maxRecDepth 100000 in
lemma V65 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 65) (section14R p) (section14S p)
      = lowerThreshold p (279/500) 35 63 63 70 := by
  rw [show section14Threshold section14Catalog 65 =
      (⟨⟨279/500,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨66/179,-1/537,0,0⟩,⟨4/13,1/13,0,0⟩,⟨125/214,-1/214,0,0⟩⟩ :
        CertThreshold) from rfl, lthr, t35, t63, t70]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

set_option maxRecDepth 100000 in
lemma V66 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 66) (section14R p) (section14S p)
      = lowerThreshold p (69/200) 22 65 28 68 := by
  rw [show section14Threshold section14Catalog 66 =
      (⟨⟨69/200,0,0,0⟩,⟨39/134,0,0,1/402⟩,⟨15/34,0,0,-1/34⟩,⟨1/10,0,0,1/10⟩,⟨119/202,0,0,-1/202⟩⟩ :
        CertThreshold) from rfl, lthr, t22, t65, t28, t68]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

set_option maxRecDepth 100000 in
lemma V67 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 67) (section14R p) (section14S p)
      = lowerThreshold p (161/500) 3 63 25 66 := by
  rw [show section14Threshold section14Catalog 67 =
      (⟨⟨161/500,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩ :
        CertThreshold) from rfl, lthr, t3, t63, t25, t66]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

set_option maxRecDepth 100000 in
lemma V116 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 116) (section14R p) (section14S p)
      = lowerThreshold p (|(lowerTheta 16-lowerTheta 13)/(lowerTheta 18-lowerTheta 25)|) 13 18 16 25 := by
  rw [show section14Threshold section14Catalog 116 =
      (⟨⟨-145/4189,5312/12567,0,0⟩,⟨16/59,1/177,0,0⟩,⟨43/142,-1/142,0,0⟩,⟨5/22,1/22,0,0⟩,
        ⟨12/47,1/47,0,0⟩⟩ : CertThreshold) from rfl, lthr, C17, t13, t18, t16, t25]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

set_option maxRecDepth 100000 in
lemma V117 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 117) (section14R p) (section14S p)
      = lowerThreshold p (|(lowerTheta 63-lowerTheta 3)/(lowerTheta 20-lowerTheta 66)|) 3 20 63 66 := by
  rw [show section14Threshold section14Catalog 117 =
      (⟨⟨-2334/781,1646/781,0,0⟩,⟨4/13,1/13,0,0⟩,⟨2,-1,0,0⟩,⟨42/143,1/429,0,0⟩,⟨9/13,-1/13,0,0⟩⟩ :
        CertThreshold) from rfl, lthr, C21, t3, t20, t63, t66]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

set_option maxRecDepth 100000 in
lemma V339 (p : LowerPair) :
    certThresholdVal (section14Threshold section14Catalog 339) (section14R p) (section14S p)
      = lowerThreshold p (139/250) 63 70 66 94 := by
  rw [show section14Threshold section14Catalog 339 =
      (⟨⟨139/250,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨1/2,1/6,0,0⟩,⟨125/214,-1/214,0,0⟩⟩ :
        CertThreshold) from rfl, lthr, t63, t70, t66, t94]
  simp only [certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal]
  push_cast
  ring

/-! ### Bound wrappers -/

lemma bTT (p : LowerPair) (n : ℕ) (c : ℝ) (i j k l : ℕ)
    (hV : certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
        = lowerThreshold p c i j k l)
    (h : lowerThreshold p c i j k l < section14Q p) :
    certBoundHolds ⟨true,true,section14Threshold section14Catalog n⟩
      (section14R p) (section14S p) (section14Q p) := by
  show certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
      < section14Q p
  rw [hV]; exact h

lemma bTF (p : LowerPair) (n : ℕ) (c : ℝ) (i j k l : ℕ)
    (hV : certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
        = lowerThreshold p c i j k l)
    (h : lowerThreshold p c i j k l ≤ section14Q p) :
    certBoundHolds ⟨true,false,section14Threshold section14Catalog n⟩
      (section14R p) (section14S p) (section14Q p) := by
  show certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
      ≤ section14Q p
  rw [hV]; exact h

lemma bFT (p : LowerPair) (n : ℕ) (c : ℝ) (i j k l : ℕ)
    (hV : certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
        = lowerThreshold p c i j k l)
    (h : section14Q p < lowerThreshold p c i j k l) :
    certBoundHolds ⟨false,true,section14Threshold section14Catalog n⟩
      (section14R p) (section14S p) (section14Q p) := by
  show section14Q p
      < certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
  rw [hV]; exact h

lemma bFF (p : LowerPair) (n : ℕ) (c : ℝ) (i j k l : ℕ)
    (hV : certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
        = lowerThreshold p c i j k l)
    (h : section14Q p ≤ lowerThreshold p c i j k l) :
    certBoundHolds ⟨false,false,section14Threshold section14Catalog n⟩
      (section14R p) (section14S p) (section14Q p) := by
  show section14Q p
      ≤ certThresholdVal (section14Threshold section14Catalog n) (section14R p) (section14S p)
  rw [hV]; exact h

lemma holds1 (b1 : CertBound) (r s q : ℝ) (h1 : certBoundHolds b1 r s q) :
    section14Holds [b1] r s q := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb; exact h1

lemma holds3 (b1 b2 b3 : CertBound) (r s q : ℝ) (h1 : certBoundHolds b1 r s q)
    (h2 : certBoundHolds b2 r s q) (h3 : certBoundHolds b3 r s q) :
    section14Holds [b1,b2,b3] r s q := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl|rfl|rfl <;> assumption

lemma holds4 (b1 b2 b3 b4 : CertBound) (r s q : ℝ) (h1 : certBoundHolds b1 r s q)
    (h2 : certBoundHolds b2 r s q) (h3 : certBoundHolds b3 r s q)
    (h4 : certBoundHolds b4 r s q) :
    section14Holds [b1,b2,b3,b4] r s q := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl <;> assumption

/-! ### The nine printed case conjunctions -/

lemma case1 (p : LowerPair) (h2 : lowerH p 2) :
    section14Holds (section14Case section14Catalog 1)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,true,section14Threshold section14Catalog 22⟩] _ _ _
  exact holds1 _ _ _ _ (bTT p 22 _ _ _ _ _ (V22 p) ((h2def p).mp h2))

lemma case2 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (h6 : lowerH p 6)
    (h7 : lowerH p 7) :
    section14Holds (section14Case section14Catalog 2)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨false,false,section14Threshold section14Catalog 22⟩,
    ⟨false,true,section14Threshold section14Catalog 65⟩,
    ⟨false,true,section14Threshold section14Catalog 66⟩,
    ⟨false,true,section14Threshold section14Catalog 67⟩] _ _ _
  exact holds4 _ _ _ _ _ _ _
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))
    (bFT p 65 _ _ _ _ _ (V65 p) ((h5def p).mp h5))
    (bFT p 66 _ _ _ _ _ (V66 p) ((h6def p).mp h6))
    (bFT p 67 _ _ _ _ _ (V67 p) ((h7def p).mp h7))

lemma case3 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (h6 : ¬ lowerH p 6) :
    section14Holds (section14Case section14Catalog 3)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,false,section14Threshold section14Catalog 66⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩,
    ⟨false,true,section14Threshold section14Catalog 65⟩] _ _ _
  exact holds3 _ _ _ _ _ _
    (bTF p 66 _ _ _ _ _ (V66 p) (not_lt.mp (fun h => h6 ((h6def p).mpr h))))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))
    (bFT p 65 _ _ _ _ _ (V65 p) ((h5def p).mp h5))

lemma case4 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (h6 : lowerH p 6)
    (h7 : ¬ lowerH p 7) :
    section14Holds (section14Case section14Catalog 4)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,false,section14Threshold section14Catalog 67⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩,
    ⟨false,true,section14Threshold section14Catalog 65⟩,
    ⟨false,true,section14Threshold section14Catalog 66⟩] _ _ _
  exact holds4 _ _ _ _ _ _ _
    (bTF p 67 _ _ _ _ _ (V67 p) (not_lt.mp (fun h => h7 ((h7def p).mpr h))))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))
    (bFT p 65 _ _ _ _ _ (V65 p) ((h5def p).mp h5))
    (bFT p 66 _ _ _ _ _ (V66 p) ((h6def p).mp h6))

lemma case5 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h17 : lowerH p 17)
    (h21 : lowerH p 21) :
    section14Holds (section14Case section14Catalog 5)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,true,section14Threshold section14Catalog 116⟩,
    ⟨true,false,section14Threshold section14Catalog 65⟩,
    ⟨false,true,section14Threshold section14Catalog 117⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩] _ _ _
  exact holds4 _ _ _ _ _ _ _
    (bTT p 116 _ _ _ _ _ (V116 p) ((h17def p).mp h17))
    (bTF p 65 _ _ _ _ _ (V65 p) (not_lt.mp (fun h => h5 ((h5def p).mpr h))))
    (bFT p 117 _ _ _ _ _ (V117 p) ((h21def p).mp h21))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))

lemma case6 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h17 : ¬ lowerH p 17)
    (h21 : lowerH p 21) :
    section14Holds (section14Case section14Catalog 6)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,false,section14Threshold section14Catalog 65⟩,
    ⟨false,false,section14Threshold section14Catalog 116⟩,
    ⟨false,true,section14Threshold section14Catalog 117⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩] _ _ _
  exact holds4 _ _ _ _ _ _ _
    (bTF p 65 _ _ _ _ _ (V65 p) (not_lt.mp (fun h => h5 ((h5def p).mpr h))))
    (bFF p 116 _ _ _ _ _ (V116 p) (not_lt.mp (fun h => h17 ((h17def p).mpr h))))
    (bFT p 117 _ _ _ _ _ (V117 p) ((h21def p).mp h21))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))

lemma case7 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : ¬ lowerH p 21)
    (h23 : lowerH p 23) :
    section14Holds (section14Case section14Catalog 7)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,false,section14Threshold section14Catalog 117⟩,
    ⟨true,true,section14Threshold section14Catalog 339⟩,
    ⟨true,false,section14Threshold section14Catalog 65⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩] _ _ _
  exact holds4 _ _ _ _ _ _ _
    (bTF p 117 _ _ _ _ _ (V117 p) (not_lt.mp (fun h => h21 ((h21def p).mpr h))))
    (bTT p 339 _ _ _ _ _ (V339 p) ((h23def p).mp h23))
    (bTF p 65 _ _ _ _ _ (V65 p) (not_lt.mp (fun h => h5 ((h5def p).mpr h))))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))

lemma case8 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : ¬ lowerH p 21)
    (h23 : ¬ lowerH p 23) :
    section14Holds (section14Case section14Catalog 8)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,false,section14Threshold section14Catalog 117⟩,
    ⟨true,false,section14Threshold section14Catalog 65⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩,
    ⟨false,false,section14Threshold section14Catalog 339⟩] _ _ _
  exact holds4 _ _ _ _ _ _ _
    (bTF p 117 _ _ _ _ _ (V117 p) (not_lt.mp (fun h => h21 ((h21def p).mpr h))))
    (bTF p 65 _ _ _ _ _ (V65 p) (not_lt.mp (fun h => h5 ((h5def p).mpr h))))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))
    (bFF p 339 _ _ _ _ _ (V339 p) (not_lt.mp (fun h => h23 ((h23def p).mpr h))))

lemma case9 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : ¬ lowerH p 21) :
    section14Holds (section14Case section14Catalog 9)
      (section14R p) (section14S p) (section14Q p) := by
  show section14Holds [⟨true,false,section14Threshold section14Catalog 117⟩,
    ⟨true,false,section14Threshold section14Catalog 65⟩,
    ⟨false,false,section14Threshold section14Catalog 22⟩] _ _ _
  exact holds3 _ _ _ _ _ _
    (bTF p 117 _ _ _ _ _ (V117 p) (not_lt.mp (fun h => h21 ((h21def p).mpr h))))
    (bTF p 65 _ _ _ _ _ (V65 p) (not_lt.mp (fun h => h5 ((h5def p).mpr h))))
    (bFF p 22 _ _ _ _ _ (V22 p) (not_lt.mp (fun h => h2 ((h2def p).mpr h))))

/-! ### The printed rows -/

lemma rawB (p : LowerPair) (h2 : lowerH p 2) :
    section14RawList p = [([1],[]),([],[1])] := by
  unfold section14RawList; simp only [h2, if_pos]

lemma raw2T (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (hL : lowerL p) :
    section14RawList p = [([1],[]),([2],[])] := by
  unfold section14RawList; simp only [if_pos, if_neg, h2, h5, hL, not_false_iff]

lemma raw3F (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (hL : ¬ lowerL p)
    (h6 : lowerH p 6) (h7 : lowerH p 7) :
    section14RawList p = [([1],[]),([2],[]),([3],[])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, hL, h6, h7, not_false_iff, and_self]

lemma raw4F (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (hL : ¬ lowerL p)
    (h67 : ¬ (lowerH p 6 ∧ lowerH p 7)) :
    section14RawList p = [([1],[]),([2],[]),([3],[1])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, hL, h67, not_false_iff]

lemma raw5F (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : lowerH p 21)
    (h17 : lowerH p 17) (hL : ¬ lowerL p) :
    section14RawList p = [([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),
      ([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, h21, h17, hL, not_false_iff, not_true_eq_false,
    false_and, and_false, List.nil_append, List.cons_append, List.append_nil]

lemma raw5T (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : lowerH p 21)
    (h17 : lowerH p 17) (hL : lowerL p) :
    section14RawList p = [([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),
      ([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, h21, h17, hL, not_false_iff, not_true_eq_false,
    false_and, and_false, List.nil_append, List.cons_append, List.append_nil]

lemma raw6F (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : lowerH p 21)
    (h17 : ¬ lowerH p 17) (hL : ¬ lowerL p) :
    section14RawList p = [([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),
      ([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),
      ([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, h21, h17, hL, not_false_iff, not_true_eq_false,
    false_and, and_false, List.nil_append, List.cons_append, List.append_nil]

lemma raw6T (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : lowerH p 21)
    (h17 : ¬ lowerH p 17) (hL : lowerL p) :
    section14RawList p = [([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),
      ([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),
      ([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, h21, h17, hL, not_false_iff, not_true_eq_false,
    false_and, and_false, List.nil_append, List.cons_append, List.append_nil]

lemma raw7 (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : ¬ lowerH p 21)
    (hE : ¬ lowerEnds (lowerNormalize p).2 [3]) (h23 : lowerH p 23) :
    section14RawList p = [([1],[]),([],[1])] := by
  unfold section14RawList
  simp only [if_pos, if_neg, h2, h5, h21, hE, h23, not_false_iff, and_self, true_and]

lemma raw8F (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : ¬ lowerH p 21)
    (hc : ¬ (¬ lowerH p 21 ∧ ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23))
    (hL : ¬ lowerL p) :
    section14RawList p = [([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),
      ([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])] := by
  unfold section14RawList
  simp only [if_neg hc, if_pos, if_neg, h2, h5, h21, hL, not_false_iff,
    List.nil_append, List.cons_append, List.append_nil]

lemma raw8T (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : ¬ lowerH p 5) (h21 : ¬ lowerH p 21)
    (hc : ¬ (¬ lowerH p 21 ∧ ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23))
    (hL : lowerL p) :
    section14RawList p = [([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),
      ([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])] := by
  unfold section14RawList
  simp only [if_neg hc, if_pos, if_neg, h2, h5, h21, hL, not_false_iff,
    List.nil_append, List.cons_append, List.append_nil]

lemma tlT (p : LowerPair) (h2 : ¬ lowerH p 2) (h5 : lowerH p 5) (hL : lowerL p) :
    section14TargetLower p = true := by
  unfold section14TargetLower; simp only [decide_eq_true_eq]; exact ⟨h2, h5, hL⟩

lemma tlF2 (p : LowerPair) (h2 : lowerH p 2) : section14TargetLower p = false := by
  unfold section14TargetLower; simp only [decide_eq_false_iff_not]; tauto

lemma tlF5 (p : LowerPair) (h5 : ¬ lowerH p 5) : section14TargetLower p = false := by
  unfold section14TargetLower; simp only [decide_eq_false_iff_not]; tauto

lemma tlFL (p : LowerPair) (hL : ¬ lowerL p) : section14TargetLower p = false := by
  unfold section14TargetLower; simp only [decide_eq_false_iff_not]; tauto


/-! ### Selecting the plan inside a catalog state -/

def key (pl : Section14Plan) : ℕ × List LowerLabel × Bool :=
  (pl.caseId, pl.labels, pl.targetLower)

lemma pick (S : Section14State) (T : List (ℕ × List LowerLabel × Bool))
    (hd : S.plans.map key = T) (t : ℕ × List LowerLabel × Bool) (ht : t ∈ T) :
    ∃ pl ∈ S.plans, pl.caseId = t.1 ∧ pl.labels = t.2.1 ∧ pl.targetLower = t.2.2 := by
  rw [← hd] at ht
  obtain ⟨pl, hpl, he⟩ := List.mem_map.mp ht
  subst he
  exact ⟨pl, hpl, rfl, rfl, rfl⟩

def rowsFF : List (ℕ × List LowerLabel × Bool) :=
  [(1,[([1],[]),([],[1])],false),
   (2,[([1],[]),([2],[]),([3],[])],false),
   (3,[([1],[]),([2],[]),([3],[1])],false),
   (4,[([1],[]),([2],[]),([3],[1])],false),
   (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false),
   (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false),
   (7,[([1],[]),([],[1])],false),
   (8,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false)]

def rowsFT : List (ℕ × List LowerLabel × Bool) :=
  [(1,[([1],[]),([],[1])],false),
   (2,[([1],[]),([2],[]),([3],[])],false),
   (3,[([1],[]),([2],[]),([3],[1])],false),
   (4,[([1],[]),([2],[]),([3],[1])],false),
   (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false),
   (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false),
   (9,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false)]

def rowsTF : List (ℕ × List LowerLabel × Bool) :=
  [(1,[([1],[]),([],[1])],false),
   (2,[([1],[]),([2],[])],true),
   (3,[([1],[]),([2],[])],true),
   (4,[([1],[]),([2],[])],true),
   (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false),
   (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false),
   (7,[([1],[]),([],[1])],false),
   (8,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])],false)]

def rowsTT : List (ℕ × List LowerLabel × Bool) :=
  [(1,[([1],[]),([],[1])],false),
   (2,[([1],[]),([2],[])],true),
   (3,[([1],[]),([2],[])],true),
   (4,[([1],[]),([2],[])],true),
   (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false),
   (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false),
   (9,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])],false)]

set_option maxRecDepth 100000 in
lemma mainFF (p : LowerPair) (S : Section14State) (w1 w2 : List ℕ+)
    (hmatch : section14Matches p S)
    (hc1 : S.context.words.1 = w1) (hc2 : S.context.words.2 = w2)
    (hw1 : ¬ (([3,1] : List ℕ+) <:+ w1)) (hw2 : ¬ (([3] : List ℕ+) <:+ w2))
    (hd : S.plans.map key = rowsFF) :
    ∃ pl ∈ S.plans, pl.labels = section14RawList p ∧ pl.targetLower = section14TargetLower p ∧
      section14Holds (section14Case section14Catalog pl.caseId)
        (section14R p) (section14S p) (section14Q p) := by
  have e1 := hmatch.1.2 []
  have e2 := hmatch.2.1.1 []
  simp only [List.append_nil] at e1 e2
  rw [hc1] at e1
  rw [hc2] at e2
  have hL : ¬ lowerL p := fun h => hw1 (e1.mp h)
  have hE : ¬ lowerEnds (lowerNormalize p).2 [3] := fun h => hw2 (e2.mp h)
  by_cases h2 : lowerH p 2
  · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (1,[([1],[]),([],[1])],false) (by simp [rowsFF])
    exact ⟨pl, hpm, by rw [hl, rawB p h2], by rw [ht, tlF2 p h2], by rw [hc]; exact case1 p h2⟩
  · by_cases h5 : lowerH p 5
    · by_cases h6 : lowerH p 6
      · by_cases h7 : lowerH p 7
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (2,[([1],[]),([2],[]),([3],[])],false) (by simp [rowsFF])
          exact ⟨pl, hpm, by rw [hl, raw3F p h2 h5 hL h6 h7], by rw [ht, tlFL p hL], by rw [hc]; exact case2 p h2 h5 h6 h7⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (4,[([1],[]),([2],[]),([3],[1])],false) (by simp [rowsFF])
          exact ⟨pl, hpm, by rw [hl, raw4F p h2 h5 hL (fun h => h7 h.2)], by rw [ht, tlFL p hL], by rw [hc]; exact case4 p h2 h5 h6 h7⟩
      · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (3,[([1],[]),([2],[]),([3],[1])],false) (by simp [rowsFF])
        exact ⟨pl, hpm, by rw [hl, raw4F p h2 h5 hL (fun h => h6 h.1)], by rw [ht, tlFL p hL], by rw [hc]; exact case3 p h2 h5 h6⟩
    · by_cases h21 : lowerH p 21
      · by_cases h17 : lowerH p 17
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false) (by simp [rowsFF])
          exact ⟨pl, hpm, by rw [hl, raw5F p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case5 p h2 h5 h17 h21⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false) (by simp [rowsFF])
          exact ⟨pl, hpm, by rw [hl, raw6F p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case6 p h2 h5 h17 h21⟩
      · by_cases h23 : lowerH p 23
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (7,[([1],[]),([],[1])],false) (by simp [rowsFF])
          exact ⟨pl, hpm, by rw [hl, raw7 p h2 h5 h21 hE h23], by rw [ht, tlF5 p h5], by rw [hc]; exact case7 p h2 h5 h21 h23⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (8,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false) (by simp [rowsFF])
          exact ⟨pl, hpm, by rw [hl, raw8F p h2 h5 h21 (fun h => h23 h.2.2) hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case8 p h2 h5 h21 h23⟩

set_option maxRecDepth 100000 in
lemma mainFT (p : LowerPair) (S : Section14State) (w1 w2 : List ℕ+)
    (hmatch : section14Matches p S)
    (hc1 : S.context.words.1 = w1) (hc2 : S.context.words.2 = w2)
    (hw1 : ¬ (([3,1] : List ℕ+) <:+ w1)) (hw2 : (([3] : List ℕ+) <:+ w2))
    (hd : S.plans.map key = rowsFT) :
    ∃ pl ∈ S.plans, pl.labels = section14RawList p ∧ pl.targetLower = section14TargetLower p ∧
      section14Holds (section14Case section14Catalog pl.caseId)
        (section14R p) (section14S p) (section14Q p) := by
  have e1 := hmatch.1.2 []
  have e2 := hmatch.2.1.1 []
  simp only [List.append_nil] at e1 e2
  rw [hc1] at e1
  rw [hc2] at e2
  have hL : ¬ lowerL p := fun h => hw1 (e1.mp h)
  have hE : lowerEnds (lowerNormalize p).2 [3] := e2.mpr hw2
  by_cases h2 : lowerH p 2
  · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (1,[([1],[]),([],[1])],false) (by simp [rowsFT])
    exact ⟨pl, hpm, by rw [hl, rawB p h2], by rw [ht, tlF2 p h2], by rw [hc]; exact case1 p h2⟩
  · by_cases h5 : lowerH p 5
    · by_cases h6 : lowerH p 6
      · by_cases h7 : lowerH p 7
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (2,[([1],[]),([2],[]),([3],[])],false) (by simp [rowsFT])
          exact ⟨pl, hpm, by rw [hl, raw3F p h2 h5 hL h6 h7], by rw [ht, tlFL p hL], by rw [hc]; exact case2 p h2 h5 h6 h7⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (4,[([1],[]),([2],[]),([3],[1])],false) (by simp [rowsFT])
          exact ⟨pl, hpm, by rw [hl, raw4F p h2 h5 hL (fun h => h7 h.2)], by rw [ht, tlFL p hL], by rw [hc]; exact case4 p h2 h5 h6 h7⟩
      · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (3,[([1],[]),([2],[]),([3],[1])],false) (by simp [rowsFT])
        exact ⟨pl, hpm, by rw [hl, raw4F p h2 h5 hL (fun h => h6 h.1)], by rw [ht, tlFL p hL], by rw [hc]; exact case3 p h2 h5 h6⟩
    · by_cases h21 : lowerH p 21
      · by_cases h17 : lowerH p 17
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false) (by simp [rowsFT])
          exact ⟨pl, hpm, by rw [hl, raw5F p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case5 p h2 h5 h17 h21⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false) (by simp [rowsFT])
          exact ⟨pl, hpm, by rw [hl, raw6F p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case6 p h2 h5 h17 h21⟩
      · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (9,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false) (by simp [rowsFT])
        exact ⟨pl, hpm, by rw [hl, raw8F p h2 h5 h21 (fun h => h.2.1 hE) hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case9 p h2 h5 h21⟩

set_option maxRecDepth 100000 in
lemma mainTF (p : LowerPair) (S : Section14State) (w1 w2 : List ℕ+)
    (hmatch : section14Matches p S)
    (hc1 : S.context.words.1 = w1) (hc2 : S.context.words.2 = w2)
    (hw1 : (([3,1] : List ℕ+) <:+ w1)) (hw2 : ¬ (([3] : List ℕ+) <:+ w2))
    (hd : S.plans.map key = rowsTF) :
    ∃ pl ∈ S.plans, pl.labels = section14RawList p ∧ pl.targetLower = section14TargetLower p ∧
      section14Holds (section14Case section14Catalog pl.caseId)
        (section14R p) (section14S p) (section14Q p) := by
  have e1 := hmatch.1.2 []
  have e2 := hmatch.2.1.1 []
  simp only [List.append_nil] at e1 e2
  rw [hc1] at e1
  rw [hc2] at e2
  have hL : lowerL p := e1.mpr hw1
  have hE : ¬ lowerEnds (lowerNormalize p).2 [3] := fun h => hw2 (e2.mp h)
  by_cases h2 : lowerH p 2
  · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (1,[([1],[]),([],[1])],false) (by simp [rowsTF])
    exact ⟨pl, hpm, by rw [hl, rawB p h2], by rw [ht, tlF2 p h2], by rw [hc]; exact case1 p h2⟩
  · by_cases h5 : lowerH p 5
    · by_cases h6 : lowerH p 6
      · by_cases h7 : lowerH p 7
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (2,[([1],[]),([2],[])],true) (by simp [rowsTF])
          exact ⟨pl, hpm, by rw [hl, raw2T p h2 h5 hL], by rw [ht, tlT p h2 h5 hL], by rw [hc]; exact case2 p h2 h5 h6 h7⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (4,[([1],[]),([2],[])],true) (by simp [rowsTF])
          exact ⟨pl, hpm, by rw [hl, raw2T p h2 h5 hL], by rw [ht, tlT p h2 h5 hL], by rw [hc]; exact case4 p h2 h5 h6 h7⟩
      · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (3,[([1],[]),([2],[])],true) (by simp [rowsTF])
        exact ⟨pl, hpm, by rw [hl, raw2T p h2 h5 hL], by rw [ht, tlT p h2 h5 hL], by rw [hc]; exact case3 p h2 h5 h6⟩
    · by_cases h21 : lowerH p 21
      · by_cases h17 : lowerH p 17
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false) (by simp [rowsTF])
          exact ⟨pl, hpm, by rw [hl, raw5T p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case5 p h2 h5 h17 h21⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false) (by simp [rowsTF])
          exact ⟨pl, hpm, by rw [hl, raw6T p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case6 p h2 h5 h17 h21⟩
      · by_cases h23 : lowerH p 23
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (7,[([1],[]),([],[1])],false) (by simp [rowsTF])
          exact ⟨pl, hpm, by rw [hl, raw7 p h2 h5 h21 hE h23], by rw [ht, tlF5 p h5], by rw [hc]; exact case7 p h2 h5 h21 h23⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (8,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])],false) (by simp [rowsTF])
          exact ⟨pl, hpm, by rw [hl, raw8T p h2 h5 h21 (fun h => h23 h.2.2) hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case8 p h2 h5 h21 h23⟩

set_option maxRecDepth 100000 in
lemma mainTT (p : LowerPair) (S : Section14State) (w1 w2 : List ℕ+)
    (hmatch : section14Matches p S)
    (hc1 : S.context.words.1 = w1) (hc2 : S.context.words.2 = w2)
    (hw1 : (([3,1] : List ℕ+) <:+ w1)) (hw2 : (([3] : List ℕ+) <:+ w2))
    (hd : S.plans.map key = rowsTT) :
    ∃ pl ∈ S.plans, pl.labels = section14RawList p ∧ pl.targetLower = section14TargetLower p ∧
      section14Holds (section14Case section14Catalog pl.caseId)
        (section14R p) (section14S p) (section14Q p) := by
  have e1 := hmatch.1.2 []
  have e2 := hmatch.2.1.1 []
  simp only [List.append_nil] at e1 e2
  rw [hc1] at e1
  rw [hc2] at e2
  have hL : lowerL p := e1.mpr hw1
  have hE : lowerEnds (lowerNormalize p).2 [3] := e2.mpr hw2
  by_cases h2 : lowerH p 2
  · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (1,[([1],[]),([],[1])],false) (by simp [rowsTT])
    exact ⟨pl, hpm, by rw [hl, rawB p h2], by rw [ht, tlF2 p h2], by rw [hc]; exact case1 p h2⟩
  · by_cases h5 : lowerH p 5
    · by_cases h6 : lowerH p 6
      · by_cases h7 : lowerH p 7
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (2,[([1],[]),([2],[])],true) (by simp [rowsTT])
          exact ⟨pl, hpm, by rw [hl, raw2T p h2 h5 hL], by rw [ht, tlT p h2 h5 hL], by rw [hc]; exact case2 p h2 h5 h6 h7⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (4,[([1],[]),([2],[])],true) (by simp [rowsTT])
          exact ⟨pl, hpm, by rw [hl, raw2T p h2 h5 hL], by rw [ht, tlT p h2 h5 hL], by rw [hc]; exact case4 p h2 h5 h6 h7⟩
      · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (3,[([1],[]),([2],[])],true) (by simp [rowsTT])
        exact ⟨pl, hpm, by rw [hl, raw2T p h2 h5 hL], by rw [ht, tlT p h2 h5 hL], by rw [hc]; exact case3 p h2 h5 h6⟩
    · by_cases h21 : lowerH p 21
      · by_cases h17 : lowerH p 17
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (5,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false) (by simp [rowsTT])
          exact ⟨pl, hpm, by rw [hl, raw5T p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case5 p h2 h5 h17 h21⟩
        · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (6,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false) (by simp [rowsTT])
          exact ⟨pl, hpm, by rw [hl, raw6T p h2 h5 h21 h17 hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case6 p h2 h5 h17 h21⟩
      · obtain ⟨pl, hpm, hc, hl, ht⟩ := pick S _ hd (9,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])],false) (by simp [rowsTT])
        exact ⟨pl, hpm, by rw [hl, raw8T p h2 h5 h21 (fun h => h.2.1 hE) hL], by rw [ht, tlF5 p h5], by rw [hc]; exact case9 p h2 h5 h21⟩

end S14RM

set_option maxRecDepth 100000 in
theorem solution (p : LowerPair) (i : Fin 16) (hm : lowerMixed p)
    (hmatch : section14Matches p (section14State section14Catalog (i.val+1))) :
    ∃ pl ∈ (section14State section14Catalog (i.val+1)).plans,
      pl.labels = section14RawList p ∧ pl.targetLower = section14TargetLower p ∧
      section14Holds (section14Case section14Catalog pl.caseId) (section14R p) (section14S p) (section14Q p) := by
  fin_cases i
  · exact S14RM.mainFF p _ [1] [1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [1] [2] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFT p _ [1] [3] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [1] [3,1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [2] [1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [2] [2] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFT p _ [2] [3] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [2] [3,1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [3] [1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [3] [2] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFT p _ [3] [3] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainFF p _ [3] [3,1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainTF p _ [3,1] [1] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainTF p _ [3,1] [2] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainTT p _ [3,1] [3] hmatch rfl rfl (by decide) (by decide) rfl
  · exact S14RM.mainTF p _ [3,1] [3,1] hmatch rfl rfl (by decide) (by decide) rfl
