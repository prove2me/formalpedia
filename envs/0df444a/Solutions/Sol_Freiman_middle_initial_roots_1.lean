-- Prove2me | solution 1 for Freiman.middle_initial_roots_1
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:47:36.461873+00:00
-- url     : https://prove2.me/submissions/cd92e8be-5761-400d-be37-39a7cbd59e25

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
open Freiman
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
namespace M8Sep10InitialRootsOpt

private lemma inv_est (x a b p q : ℝ) (ha : 0 < a)
    (hx : a ≤ x ∧ x ≤ b) (hl : p ≤ 1/b) (hu : 1/a ≤ q) :
    p ≤ 1/x ∧ 1/x ≤ q := by
  exact ⟨hl.trans (one_div_le_one_div_of_le (ha.trans_le hx.1) hx.2),
    (one_div_le_one_div_of_le ha hx.1).trans hu⟩
private lemma div_est (x y l u a b p q : ℝ) (hl : 0 ≤ l) (ha : 0 < a)
    (hx : l ≤ x ∧ x ≤ u) (hy : a ≤ y ∧ y ≤ b)
    (hp : p ≤ l/b) (hq : u/a ≤ q) : p ≤ x/y ∧ x/y ≤ q := by
  have hpos : 0 < y := ha.trans_le hy.1
  have hu : 0 ≤ u := hl.trans (hx.1.trans hx.2)
  exact ⟨hp.trans ((div_le_div_of_nonneg_left hl hpos hy.2).trans
    (div_le_div_of_nonneg_right hx.1 hpos.le)),
    ((div_le_div_of_nonneg_right hx.2 hpos.le).trans
    (div_le_div_of_nonneg_left hu ha hy.1)).trans hq⟩
private lemma sqrt_21_bounds : (916515138991/200000000000:ℝ) ≤ Real.sqrt 21 ∧ Real.sqrt 21 ≤ (1145643923739/250000000000:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
  have hn := Real.sqrt_nonneg (21:ℝ)
  constructor <;> nlinarith
private lemma sqrt_3_bounds : (108253175473/62500000000:ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (1732050807569/1000000000000:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3:ℝ)
  constructor <;> nlinarith

private theorem bound_000 : (791287847477/1000000000000:ℝ) ≤ middleBeta ∧ middleBeta ≤ (395643923739/500000000000:ℝ) := by
  dsimp only [middleBeta]
  constructor <;> linarith only [sqrt_21_bounds.1, sqrt_21_bounds.2]

private theorem bound_001 : (71651513899/200000000000:ℝ) ≤ prefixEval [2] middleBeta ∧ prefixEval [2] middleBeta ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + middleBeta) ∧ 1 / (2 + middleBeta) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (1395643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_002 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2] middleBeta ∧ prefixEval [1,2] middleBeta ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2] middleBeta) ∧ 1 / (1 + prefixEval [2] middleBeta) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_003 : (10550504633/40000000000:ℝ) ≤ middleAlpha ∧ middleAlpha ≤ (131881307913/500000000000:ℝ) := by
  dsimp only [middleAlpha]
  constructor <;> linarith only [sqrt_21_bounds.1, sqrt_21_bounds.2]

private theorem bound_004 : (55217803813/125000000000:ℝ) ≤ prefixEval [2] middleAlpha ∧ prefixEval [2] middleAlpha ≤ (88348486101/200000000000:ℝ) := by
  suffices hh : (55217803813/125000000000:ℝ) ≤ 1 / (2 + middleAlpha) ∧ 1 / (2 + middleAlpha) ≤ (88348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (90550504633/40000000000:ℝ) (1131881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_005 : (346802583749/500000000000:ℝ) ≤ prefixEval [1,2] middleAlpha ∧ prefixEval [1,2] middleAlpha ≤ (693605167499/1000000000000:ℝ) := by
  suffices hh : (346802583749/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2] middleAlpha) ∧ 1 / (1 + prefixEval [2] middleAlpha) ≤ (693605167499/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (180217803813/125000000000:ℝ) (288348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_004.1, bound_004.2]
  · norm_num
  · norm_num

private theorem bound_006 : (21316108337/500000000000:ℝ) ≤ middleWidth [1,2] ∧ middleWidth [1,2] ≤ (42632216677/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_002.1, bound_005.2])]
  constructor <;> linarith only [bound_002.1, bound_002.2, bound_005.1, bound_005.2]

private theorem bound_007 : (5217803813/62500000000:ℝ) ≤ middleWidth [2] ∧ middleWidth [2] ≤ (8348486101/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_001.2, bound_004.1])]
  constructor <;> linarith only [bound_001.1, bound_001.2, bound_004.1, bound_004.2]

private theorem bound_008 : ¬ (middleWidth [2] ≤ middleWidth [1,2]) := by linarith only [bound_007.1, bound_006.2]

private theorem bound_009 : middleNormalized (⟨[1,2],[2]⟩ : MiddleCore) = (⟨[2],[1,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_008, ite_false]

private theorem bound_010 : (111651513899/200000000000:ℝ) ≤ prefixEval [1] middleBeta ∧ prefixEval [1] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + middleBeta) ∧ 1 / (1 + middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (895643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_011 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1] middleBeta ∧ prefixEval [2,1] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1] middleBeta) ∧ 1 / (2 + prefixEval [1] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_010.1, bound_010.2]
  · norm_num
  · norm_num

private theorem bound_012 : (359481785611/500000000000:ℝ) ≤ prefixEval [1,2,1] middleBeta ∧ prefixEval [1,2,1] middleBeta ≤ (89870446403/125000000000:ℝ) := by
  suffices hh : (359481785611/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1] middleBeta) ∧ 1 / (1 + prefixEval [2,1] middleBeta) ≤ (89870446403/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1390891054881/1000000000000:ℝ) (1390891054883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_011.1, bound_011.2]
  · norm_num
  · norm_num

private theorem bound_013 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1] middleAlpha ∧ prefixEval [1] middleAlpha ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + middleAlpha) ∧ 1 / (1 + middleAlpha) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (631881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_014 : (71651513899/200000000000:ℝ) ≤ prefixEval [2,1] middleAlpha ∧ prefixEval [2,1] middleAlpha ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1] middleAlpha) ∧ 1 / (2 + prefixEval [1] middleAlpha) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (2791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_013.1, bound_013.2]
  · norm_num
  · norm_num

private theorem bound_015 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2,1] middleAlpha ∧ prefixEval [1,2,1] middleAlpha ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1] middleAlpha) ∧ 1 / (1 + prefixEval [2,1] middleAlpha) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_014.1, bound_014.2]
  · norm_num
  · norm_num

private theorem bound_016 : (17273812949/1000000000000:ℝ) ≤ middleWidth [1,2,1] ∧ middleWidth [1,2,1] ≤ (17273812953/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_012.2, bound_015.1])]
  constructor <;> linarith only [bound_012.1, bound_012.2, bound_015.1, bound_015.2]

private theorem bound_017 : middleWidth [1,2,1] ≤ middleWidth [2] := by linarith only [bound_016.2, bound_007.1]

private theorem bound_018 : middleNormalized (⟨[2],[1,2,1]⟩ : MiddleCore) = (⟨[2],[1,2,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_017, ite_true]

private theorem bound_019 : (10550504633/40000000000:ℝ) ≤ prefixEval [3] middleBeta ∧ prefixEval [3] middleBeta ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + middleBeta) ∧ 1 / (3 + middleBeta) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (1895643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_020 : (55217803813/125000000000:ℝ) ≤ prefixEval [2,3] middleBeta ∧ prefixEval [2,3] middleBeta ≤ (88348486101/200000000000:ℝ) := by
  suffices hh : (55217803813/125000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleBeta) ∧ 1 / (2 + prefixEval [3] middleBeta) ≤ (88348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (90550504633/40000000000:ℝ) (2263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_019.1, bound_019.2]
  · norm_num
  · norm_num

private theorem bound_021 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3] middleAlpha ∧ prefixEval [3] middleAlpha ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + middleAlpha) ∧ 1 / (3 + middleAlpha) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (1631881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_022 : (2167885537/5000000000:ℝ) ≤ prefixEval [2,3] middleAlpha ∧ prefixEval [2,3] middleAlpha ≤ (433577107401/1000000000000:ℝ) := by
  suffices hh : (2167885537/5000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleAlpha) ∧ 1 / (2 + prefixEval [3] middleAlpha) ≤ (433577107401/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2306394832501/1000000000000:ℝ) (1153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_021.1, bound_021.2]
  · norm_num
  · norm_num

private theorem bound_023 : (8165323103/1000000000000:ℝ) ≤ middleWidth [2,3] ∧ middleWidth [2,3] ≤ (1633064621/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_020.1, bound_022.2])]
  constructor <;> linarith only [bound_020.1, bound_020.2, bound_022.1, bound_022.2]

private theorem bound_024 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1,3] middleBeta ∧ prefixEval [1,3] middleBeta ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleBeta) ∧ 1 / (1 + prefixEval [3] middleBeta) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (1263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_019.1, bound_019.2]
  · norm_num
  · norm_num

private theorem bound_025 : (71651513899/200000000000:ℝ) ≤ prefixEval [2,1,3] middleBeta ∧ prefixEval [2,1,3] middleBeta ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,3] middleBeta) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (2791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_026 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2,1,3] middleBeta ∧ prefixEval [1,2,1,3] middleBeta ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [2,1,3] middleBeta) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_025.1, bound_025.2]
  · norm_num
  · norm_num

private theorem bound_027 : (76546536707/100000000000:ℝ) ≤ prefixEval [1,3] middleAlpha ∧ prefixEval [1,3] middleAlpha ≤ (765465367071/1000000000000:ℝ) := by
  suffices hh : (76546536707/100000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleAlpha) ∧ 1 / (1 + prefixEval [3] middleAlpha) ≤ (765465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1306394832501/1000000000000:ℝ) (653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_021.1, bound_021.2]
  · norm_num
  · norm_num

private theorem bound_028 : (180801396377/500000000000:ℝ) ≤ prefixEval [2,1,3] middleAlpha ∧ prefixEval [2,1,3] middleAlpha ≤ (90400698189/250000000000:ℝ) := by
  suffices hh : (180801396377/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,3] middleAlpha) ≤ (90400698189/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (276546536707/100000000000:ℝ) (2765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_027.1, bound_027.2]
  · norm_num
  · norm_num

private theorem bound_029 : (734428575881/1000000000000:ℝ) ≤ prefixEval [1,2,1,3] middleAlpha ∧ prefixEval [1,2,1,3] middleAlpha ≤ (734428575883/1000000000000:ℝ) := by
  suffices hh : (734428575881/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,1,3] middleAlpha) ≤ (734428575883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (680801396377/500000000000:ℝ) (340400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_028.1, bound_028.2]
  · norm_num
  · norm_num

private theorem bound_030 : (180880829/100000000000:ℝ) ≤ middleWidth [1,2,1,3] ∧ middleWidth [1,2,1,3] ≤ (904404147/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_026.1, bound_029.2])]
  constructor <;> linarith only [bound_026.1, bound_026.2, bound_029.1, bound_029.2]

private theorem bound_031 : ¬ (middleWidth [2,3] ≤ (7/5:ℝ) * middleWidth [1,2,1,3]) := by linarith only [bound_023.1, bound_030.2]

private theorem bound_032 : (45753175473/62500000000:ℝ) ≤ middleRho ∧ middleRho ≤ (732050807569/1000000000000:ℝ) := by
  dsimp only [middleRho]
  constructor <;> linarith only [sqrt_3_bounds.1, sqrt_3_bounds.2]

private theorem bound_033 : (267949192431/1000000000000:ℝ) ≤ prefixEval [3] middleRho ∧ prefixEval [3] middleRho ≤ (16746824527/62500000000:ℝ) := by
  suffices hh : (267949192431/1000000000000:ℝ) ≤ 1 / (3 + middleRho) ∧ 1 / (3 + middleRho) ≤ (16746824527/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (233253175473/62500000000:ℝ) (3732050807569/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_032.1, bound_032.2]
  · norm_num
  · norm_num

private theorem bound_034 : (394337567297/500000000000:ℝ) ≤ prefixEval [1,3] middleRho ∧ prefixEval [1,3] middleRho ≤ (157735026919/200000000000:ℝ) := by
  suffices hh : (394337567297/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleRho) ∧ 1 / (1 + prefixEval [3] middleRho) ≤ (157735026919/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1267949192431/1000000000000:ℝ) (79246824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_033.1, bound_033.2]
  · norm_num
  · norm_num

private theorem bound_035 : (358593221417/1000000000000:ℝ) ≤ prefixEval [2,1,3] middleRho ∧ prefixEval [2,1,3] middleRho ≤ (179296610709/500000000000:ℝ) := by
  suffices hh : (358593221417/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleRho) ∧ 1 / (2 + prefixEval [1,3] middleRho) ≤ (179296610709/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1394337567297/500000000000:ℝ) (557735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_034.1, bound_034.2]
  · norm_num
  · norm_num

private theorem bound_036 : (368027745257/500000000000:ℝ) ≤ prefixEval [1,2,1,3] middleRho ∧ prefixEval [1,2,1,3] middleRho ≤ (147211098103/200000000000:ℝ) := by
  suffices hh : (368027745257/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleRho) ∧ 1 / (1 + prefixEval [2,1,3] middleRho) ≤ (147211098103/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1358593221417/1000000000000:ℝ) (679296610709/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_035.1, bound_035.2]
  · norm_num
  · norm_num

private theorem bound_037 : middleE3 (⟨[2],[1,2,1]⟩ : MiddleCore) = 4 + prefixEval [2] middleAlpha + prefixEval [1,2,1,3] middleRho := by
  norm_num [middleE3, bound_031]

private theorem bound_038 : (2588898960509/500000000000:ℝ) ≤ middleE3 (⟨[2],[1,2,1]⟩ : MiddleCore) ∧ middleE3 (⟨[2],[1,2,1]⟩ : MiddleCore) ≤ (258889896051/50000000000:ℝ) := by
  rw [bound_037]
  constructor <;> linarith only [bound_004.1, bound_004.2, bound_036.1, bound_036.2]

private theorem bound_039 : (1672611629/500000000000:ℝ) ≤ middleWidth [2,1,3] ∧ middleWidth [2,1,3] ≤ (3345223261/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_025.2, bound_028.1])]
  constructor <;> linarith only [bound_025.1, bound_025.2, bound_028.1, bound_028.2]

private theorem bound_040 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1,3] middleBeta ∧ prefixEval [1,1,3] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3] middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_041 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1,1,3] middleBeta ∧ prefixEval [2,1,1,3] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_040.1, bound_040.2]
  · norm_num
  · norm_num

private theorem bound_042 : (359481785611/500000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleBeta ∧ prefixEval [1,2,1,1,3] middleBeta ≤ (89870446403/125000000000:ℝ) := by
  suffices hh : (359481785611/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [2,1,1,3] middleBeta) ≤ (89870446403/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1390891054881/1000000000000:ℝ) (1390891054883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_041.1, bound_041.2]
  · norm_num
  · norm_num

private theorem bound_043 : (566422892599/1000000000000:ℝ) ≤ prefixEval [1,1,3] middleAlpha ∧ prefixEval [1,1,3] middleAlpha ≤ (2832114463/5000000000:ℝ) := by
  suffices hh : (566422892599/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3] middleAlpha) ≤ (2832114463/5000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (176546536707/100000000000:ℝ) (1765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_027.1, bound_027.2]
  · norm_num
  · norm_num

private theorem bound_044 : (77929479423/200000000000:ℝ) ≤ prefixEval [2,1,1,3] middleAlpha ∧ prefixEval [2,1,1,3] middleAlpha ≤ (97411849279/250000000000:ℝ) := by
  suffices hh : (77929479423/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3] middleAlpha) ≤ (97411849279/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2566422892599/1000000000000:ℝ) (12832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_043.1, bound_043.2]
  · norm_num
  · norm_num

private theorem bound_045 : (17990175099/25000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleAlpha ∧ prefixEval [1,2,1,1,3] middleAlpha ≤ (719607003961/1000000000000:ℝ) := by
  suffices hh : (17990175099/25000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,1,1,3] middleAlpha) ≤ (719607003961/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (277929479423/200000000000:ℝ) (347411849279/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_044.1, bound_044.2]
  · norm_num
  · norm_num

private theorem bound_046 : (20107273/31250000000:ℝ) ≤ middleWidth [1,2,1,1,3] ∧ middleWidth [1,2,1,1,3] ≤ (643432739/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_042.2, bound_045.1])]
  constructor <;> linarith only [bound_042.1, bound_042.2, bound_045.1, bound_045.2]

private theorem bound_047 : ¬ (middleWidth [2,1,3] ≤ (7/5:ℝ) * middleWidth [1,2,1,1,3]) := by linarith only [bound_039.1, bound_046.2]

private theorem bound_048 : (279536507401/500000000000:ℝ) ≤ prefixEval [1,1,3] middleRho ∧ prefixEval [1,1,3] middleRho ≤ (559073014803/1000000000000:ℝ) := by
  suffices hh : (279536507401/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleRho) ∧ 1 / (1 + prefixEval [1,3] middleRho) ≤ (559073014803/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (894337567297/500000000000:ℝ) (357735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_034.1, bound_034.2]
  · norm_num
  · norm_num

private theorem bound_049 : (12211453061/31250000000:ℝ) ≤ prefixEval [2,1,1,3] middleRho ∧ prefixEval [2,1,1,3] middleRho ≤ (390766497953/1000000000000:ℝ) := by
  suffices hh : (12211453061/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3] middleRho) ≤ (390766497953/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1279536507401/500000000000:ℝ) (2559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_050 : (719027961539/1000000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleRho ∧ prefixEval [1,2,1,1,3] middleRho ≤ (35951398077/50000000000:ℝ) := by
  suffices hh : (719027961539/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [2,1,1,3] middleRho) ≤ (35951398077/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (43461453061/31250000000:ℝ) (1390766497953/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_049.1, bound_049.2]
  · norm_num
  · norm_num

private theorem bound_051 : middleE13 (⟨[2],[1,2,1]⟩ : MiddleCore) = 4 + prefixEval [2] middleBeta + prefixEval [1,2,1,1,3] middleRho := by
  norm_num [middleE13, bound_047]

private theorem bound_052 : (2538642765517/500000000000:ℝ) ≤ middleE13 (⟨[2],[1,2,1]⟩ : MiddleCore) ∧ middleE13 (⟨[2],[1,2,1]⟩ : MiddleCore) ≤ (1269321382759/250000000000:ℝ) := by
  rw [bound_051]
  constructor <;> linarith only [bound_001.1, bound_001.2, bound_050.1, bound_050.2]

private theorem bound_053 : middleEqualBounds (⟨[2],[1,2,1]⟩ : MiddleCore) = (middleE13 (⟨[2],[1,2,1]⟩ : MiddleCore), middleE3 (⟨[2],[1,2,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_018]

private theorem bound_054 : (6526697077/200000000000:ℝ) ≤ middleWidth [2,1] ∧ middleWidth [2,1] ≤ (8158371347/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_011.1, bound_014.2])]
  constructor <;> linarith only [bound_011.1, bound_011.2, bound_014.1, bound_014.2]

private theorem bound_055 : ¬ (middleWidth [1,2] ≤ middleWidth [2,1]) := by linarith only [bound_006.1, bound_054.2]

private theorem bound_056 : middleNormalized (⟨[2,1],[1,2]⟩ : MiddleCore) = (⟨[1,2],[2,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_055, ite_false]

private theorem bound_057 : (346802583749/500000000000:ℝ) ≤ prefixEval [1,2,3] middleBeta ∧ prefixEval [1,2,3] middleBeta ≤ (693605167499/1000000000000:ℝ) := by
  suffices hh : (346802583749/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleBeta) ∧ 1 / (1 + prefixEval [2,3] middleBeta) ≤ (693605167499/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (180217803813/125000000000:ℝ) (288348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_020.1, bound_020.2]
  · norm_num
  · norm_num

private theorem bound_058 : (697555781853/1000000000000:ℝ) ≤ prefixEval [1,2,3] middleAlpha ∧ prefixEval [1,2,3] middleAlpha ≤ (348777890927/500000000000:ℝ) := by
  suffices hh : (697555781853/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,3] middleAlpha) ≤ (348777890927/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (7167885537/5000000000:ℝ) (1433577107401/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_022.1, bound_022.2]
  · norm_num
  · norm_num

private theorem bound_059 : (1975307177/500000000000:ℝ) ≤ middleWidth [1,2,3] ∧ middleWidth [1,2,3] ≤ (987653589/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_057.2, bound_058.1])]
  constructor <;> linarith only [bound_057.1, bound_057.2, bound_058.1, bound_058.2]

private theorem bound_060 : middleWidth [1,2,3] ≤ (7/5:ℝ) * middleWidth [2,1,3] := by linarith only [bound_059.2, bound_039.1]

private theorem bound_061 : (440926985197/1000000000000:ℝ) ≤ prefixEval [2,3] middleRho ∧ prefixEval [2,3] middleRho ≤ (220463492599/500000000000:ℝ) := by
  suffices hh : (440926985197/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleRho) ∧ 1 / (2 + prefixEval [3] middleRho) ≤ (220463492599/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2267949192431/1000000000000:ℝ) (141746824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_033.1, bound_033.2]
  · norm_num
  · norm_num

private theorem bound_062 : (173499422641/250000000000:ℝ) ≤ prefixEval [1,2,3] middleRho ∧ prefixEval [1,2,3] middleRho ≤ (346998845283/500000000000:ℝ) := by
  suffices hh : (173499422641/250000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleRho) ∧ 1 / (1 + prefixEval [2,3] middleRho) ≤ (346998845283/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1440926985197/1000000000000:ℝ) (720463492599/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_061.1, bound_061.2]
  · norm_num
  · norm_num

private theorem bound_063 : (36546536707/100000000000:ℝ) ≤ prefixEval [2,1,2] middleBeta ∧ prefixEval [2,1,2] middleBeta ≤ (365465367071/1000000000000:ℝ) := by
  suffices hh : (36546536707/100000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,2] middleBeta) ≤ (365465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2736237384173/1000000000000:ℝ) (109449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_064 : middleE3 (⟨[1,2],[2,1]⟩ : MiddleCore) = 4 + prefixEval [1,2,3] middleRho + prefixEval [2,1,2] middleBeta := by
  norm_num [middleE3, bound_060]

private theorem bound_065 : (2529731528817/500000000000:ℝ) ≤ middleE3 (⟨[1,2],[2,1]⟩ : MiddleCore) ∧ middleE3 (⟨[1,2],[2,1]⟩ : MiddleCore) ≤ (5059463057637/1000000000000:ℝ) := by
  rw [bound_064]
  constructor <;> linarith only [bound_062.1, bound_062.2, bound_063.1, bound_063.2]

private theorem bound_066 : (248731553/200000000000:ℝ) ≤ middleWidth [2,1,1,3] ∧ middleWidth [2,1,1,3] ≤ (155457221/125000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_041.1, bound_044.2])]
  constructor <;> linarith only [bound_041.1, bound_041.2, bound_044.1, bound_044.2]

private theorem bound_067 : ¬ (middleWidth [1,2,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3]) := by linarith only [bound_030.1, bound_066.2]

private theorem bound_068 : middleE13 (⟨[1,2],[2,1]⟩ : MiddleCore) = 4 + prefixEval [1,2] middleBeta + prefixEval [2,1,1,3] middleRho := by
  norm_num [middleE13, bound_067]

private theorem bound_069 : (41016031057/8000000000:ℝ) ≤ middleE13 (⟨[1,2],[2,1]⟩ : MiddleCore) ∧ middleE13 (⟨[1,2],[2,1]⟩ : MiddleCore) ≤ (320437742633/62500000000:ℝ) := by
  rw [bound_068]
  constructor <;> linarith only [bound_002.1, bound_002.2, bound_049.1, bound_049.2]

private theorem bound_070 : middleEqualBounds (⟨[2,1],[1,2]⟩ : MiddleCore) = (middleE3 (⟨[1,2],[2,1]⟩ : MiddleCore), middleE13 (⟨[1,2],[2,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_056]

private theorem bound_071 : middleBounds (⟨[1,2],[2]⟩ : MiddleCore) = (middleE3 (⟨[1,2],[2,1]⟩ : MiddleCore), middleE3 (⟨[2],[1,2,1]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_009, bound_053, bound_070]

private theorem bound_072 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1] middleBeta ∧ prefixEval [1,1] middleBeta ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1] middleBeta) ∧ 1 / (1 + prefixEval [1] middleBeta) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_010.1, bound_010.2]
  · norm_num
  · norm_num

private theorem bound_073 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1] middleAlpha ∧ prefixEval [1,1] middleAlpha ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1] middleAlpha) ∧ 1 / (1 + prefixEval [1] middleAlpha) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_013.1, bound_013.2]
  · norm_num
  · norm_num

private theorem bound_074 : (5217803813/62500000000:ℝ) ≤ middleWidth [1,1] ∧ middleWidth [1,1] ≤ (8348486101/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_072.1, bound_073.2])]
  constructor <;> linarith only [bound_072.1, bound_072.2, bound_073.1, bound_073.2]

private theorem bound_075 : middleWidth [2] ≤ middleWidth [1,1] := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_001.1, bound_001.2, bound_004.1, bound_004.2]), abs_of_nonneg (by linarith only [bound_072.1, bound_072.2, bound_073.1, bound_073.2])]
  apply le_of_eq
  norm_num [prefixEval]
  have hx (x : ℝ) (hx : 0 < x) :
      (1 + (1 + x)⁻¹)⁻¹ = 1 - (2 + x)⁻¹ := by
    have bound_000 : 1+x ≠ 0 := by linarith
    have bound_010 : 2+x ≠ 0 := by linarith
    have hinv : 0 < (1+x)⁻¹ := inv_pos.mpr (by linarith)
    have bound_072 : 1+(1+x)⁻¹ ≠ 0 := by linarith
    field_simp [bound_000, bound_010, bound_072]
    <;> ring
  rw [hx middleAlpha (by linarith only [bound_003.1]), hx middleBeta (by linarith only [bound_000.1])]
  ring

private theorem bound_076 : middleNormalized (⟨[1,1],[2]⟩ : MiddleCore) = (⟨[1,1],[2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_075, ite_true]

private theorem bound_077 : middleWidth [2,1] ≤ middleWidth [1,1] := by linarith only [bound_054.2, bound_074.1]

private theorem bound_078 : middleNormalized (⟨[1,1],[2,1]⟩ : MiddleCore) = (⟨[1,1],[2,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_077, ite_true]

private theorem bound_079 : (8165323103/1000000000000:ℝ) ≤ middleWidth [1,1,3] ∧ middleWidth [1,1,3] ≤ (1633064621/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_040.2, bound_043.1])]
  constructor <;> linarith only [bound_040.1, bound_040.2, bound_043.1, bound_043.2]

private theorem bound_080 : ¬ (middleWidth [1,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,3]) := by linarith only [bound_079.1, bound_039.2]

private theorem bound_081 : middleE3 (⟨[1,1],[2,1]⟩ : MiddleCore) = 4 + prefixEval [1,1] middleAlpha + prefixEval [2,1,3] middleRho := by
  norm_num [middleE3, bound_080]

private theorem bound_082 : (9603224201/1953125000:ℝ) ≤ middleE3 (⟨[1,1],[2,1]⟩ : MiddleCore) ∧ middleE3 (⟨[1,1],[2,1]⟩ : MiddleCore) ≤ (2458425395457/500000000000:ℝ) := by
  rw [bound_081]
  constructor <;> linarith only [bound_073.1, bound_073.2, bound_035.1, bound_035.2]

private theorem bound_083 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1,1,3] middleBeta ∧ prefixEval [1,1,1,3] middleBeta ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,3] middleBeta) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_040.1, bound_040.2]
  · norm_num
  · norm_num

private theorem bound_084 : (159599301811/250000000000:ℝ) ≤ prefixEval [1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,3] middleAlpha ≤ (319198603623/500000000000:ℝ) := by
  suffices hh : (159599301811/250000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,3] middleAlpha) ≤ (319198603623/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1566422892599/1000000000000:ℝ) (7832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_043.1, bound_043.2]
  · norm_num
  · norm_num

private theorem bound_085 : (1672611629/500000000000:ℝ) ≤ middleWidth [1,1,1,3] ∧ middleWidth [1,1,1,3] ≤ (3345223261/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_083.1, bound_084.2])]
  constructor <;> linarith only [bound_083.1, bound_083.2, bound_084.1, bound_084.2]

private theorem bound_086 : ¬ (middleWidth [1,1,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3]) := by linarith only [bound_085.1, bound_066.2]

private theorem bound_087 : middleE13 (⟨[1,1],[2,1]⟩ : MiddleCore) = 4 + prefixEval [1,1] middleBeta + prefixEval [2,1,1,3] middleRho := by
  norm_num [middleE13, bound_086]

private theorem bound_088 : (629063616057/125000000000:ℝ) ≤ middleE13 (⟨[1,1],[2,1]⟩ : MiddleCore) ∧ middleE13 (⟨[1,1],[2,1]⟩ : MiddleCore) ≤ (2516254464229/500000000000:ℝ) := by
  rw [bound_087]
  constructor <;> linarith only [bound_072.1, bound_072.2, bound_049.1, bound_049.2]

private theorem bound_089 : middleEqualBounds (⟨[1,1],[2,1]⟩ : MiddleCore) = (middleE3 (⟨[1,1],[2,1]⟩ : MiddleCore), middleE13 (⟨[1,1],[2,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_078]

private theorem bound_090 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1] middleBeta ∧ prefixEval [1,1,1] middleBeta ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1] middleBeta) ∧ 1 / (1 + prefixEval [1,1] middleBeta) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_072.1, bound_072.2]
  · norm_num
  · norm_num

private theorem bound_091 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1,1] middleAlpha ∧ prefixEval [1,1,1] middleAlpha ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,1] middleAlpha) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_073.1, bound_073.2]
  · norm_num
  · norm_num

private theorem bound_092 : (6526697077/200000000000:ℝ) ≤ middleWidth [1,1,1] ∧ middleWidth [1,1,1] ≤ (8158371347/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_090.2, bound_091.1])]
  constructor <;> linarith only [bound_090.1, bound_090.2, bound_091.1, bound_091.2]

private theorem bound_093 : ¬ (middleWidth [2] ≤ middleWidth [1,1,1]) := by linarith only [bound_007.1, bound_092.2]

private theorem bound_094 : middleNormalized (⟨[1,1,1],[2]⟩ : MiddleCore) = (⟨[2],[1,1,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_093, ite_false]

private theorem bound_095 : ¬ (middleWidth [2,3] ≤ (7/5:ℝ) * middleWidth [1,1,1,3]) := by linarith only [bound_023.1, bound_085.2]

private theorem bound_096 : (320703389291/500000000000:ℝ) ≤ prefixEval [1,1,1,3] middleRho ∧ prefixEval [1,1,1,3] middleRho ≤ (80175847323/125000000000:ℝ) := by
  suffices hh : (320703389291/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,1,3] middleRho) ≤ (80175847323/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (779536507401/500000000000:ℝ) (1559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_097 : middleE3 (⟨[2],[1,1,1]⟩ : MiddleCore) = 4 + prefixEval [2] middleAlpha + prefixEval [1,1,1,3] middleRho := by
  norm_num [middleE3, bound_095]

private theorem bound_098 : (2541574604543/500000000000:ℝ) ≤ middleE3 (⟨[2],[1,1,1]⟩ : MiddleCore) ∧ middleE3 (⟨[2],[1,1,1]⟩ : MiddleCore) ≤ (5083149209089/1000000000000:ℝ) := by
  rw [bound_097]
  constructor <;> linarith only [bound_004.1, bound_004.2, bound_096.1, bound_096.2]

private theorem bound_099 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleBeta ∧ prefixEval [1,1,1,1,3] middleBeta ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,1,3] middleBeta) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_083.1, bound_083.2]
  · norm_num
  · norm_num

private theorem bound_100 : (610352602883/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,1,3] middleAlpha ≤ (122070520577/200000000000:ℝ) := by
  suffices hh : (610352602883/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,1,3] middleAlpha) ≤ (122070520577/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (409599301811/250000000000:ℝ) (819198603623/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_084.1, bound_084.2]
  · norm_num
  · norm_num

private theorem bound_101 : (310914441/250000000000:ℝ) ≤ middleWidth [1,1,1,1,3] ∧ middleWidth [1,1,1,1,3] ≤ (155457221/125000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_099.2, bound_100.1])]
  constructor <;> linarith only [bound_099.1, bound_099.2, bound_100.1, bound_100.2]

private theorem bound_102 : ¬ (middleWidth [2,1,3] ≤ (7/5:ℝ) * middleWidth [1,1,1,1,3]) := by linarith only [bound_039.1, bound_101.2]

private theorem bound_103 : (304616751023/500000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleRho ∧ prefixEval [1,1,1,1,3] middleRho ≤ (19038546939/31250000000:ℝ) := by
  suffices hh : (304616751023/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,1,1,3] middleRho) ≤ (19038546939/31250000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (820703389291/500000000000:ℝ) (205175847323/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_096.1, bound_096.2]
  · norm_num
  · norm_num

private theorem bound_104 : middleE13 (⟨[2],[1,1,1]⟩ : MiddleCore) = 4 + prefixEval [2] middleBeta + prefixEval [1,1,1,1,3] middleRho := by
  norm_num [middleE13, bound_102]

private theorem bound_105 : (4967491071541/1000000000000:ℝ) ≤ middleE13 (⟨[2],[1,1,1]⟩ : MiddleCore) ∧ middleE13 (⟨[2],[1,1,1]⟩ : MiddleCore) ≤ (620936383943/125000000000:ℝ) := by
  rw [bound_104]
  constructor <;> linarith only [bound_001.1, bound_001.2, bound_103.1, bound_103.2]

private theorem bound_106 : middleEqualBounds (⟨[1,1,1],[2]⟩ : MiddleCore) = (middleE13 (⟨[2],[1,1,1]⟩ : MiddleCore), middleE3 (⟨[2],[1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_094]

private theorem bound_107 : middleBounds (⟨[1,1],[2]⟩ : MiddleCore) = (middleE3 (⟨[1,1],[2,1]⟩ : MiddleCore), middleE3 (⟨[2],[1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_076, bound_089, bound_106]

private theorem bound_108 : (21316108337/500000000000:ℝ) ≤ middleWidth [3] ∧ middleWidth [3] ≤ (42632216677/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_019.2, bound_021.1])]
  constructor <;> linarith only [bound_019.1, bound_019.2, bound_021.1, bound_021.2]

private theorem bound_109 : middleWidth [3] ≤ middleWidth [1,1] := by linarith only [bound_108.2, bound_074.1]

private theorem bound_110 : middleNormalized (⟨[1,1],[3]⟩ : MiddleCore) = (⟨[1,1],[3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_109, ite_true]

private theorem bound_111 : (281036428777/1000000000000:ℝ) ≤ prefixEval [3,1] middleBeta ∧ prefixEval [3,1] middleBeta ≤ (140518214389/500000000000:ℝ) := by
  suffices hh : (281036428777/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1] middleBeta) ∧ 1 / (3 + prefixEval [1] middleBeta) ≤ (140518214389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (711651513899/200000000000:ℝ) (444782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_010.1, bound_010.2]
  · norm_num
  · norm_num

private theorem bound_112 : (10550504633/40000000000:ℝ) ≤ prefixEval [3,1] middleAlpha ∧ prefixEval [3,1] middleAlpha ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + prefixEval [1] middleAlpha) ∧ 1 / (3 + prefixEval [1] middleAlpha) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (3791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_013.1, bound_013.2]
  · norm_num
  · norm_num

private theorem bound_113 : (345476259/20000000000:ℝ) ≤ middleWidth [3,1] ∧ middleWidth [3,1] ≤ (17273812953/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_111.1, bound_112.2])]
  constructor <;> linarith only [bound_111.1, bound_111.2, bound_112.1, bound_112.2]

private theorem bound_114 : middleWidth [3,1] ≤ middleWidth [1,1] := by linarith only [bound_113.2, bound_074.1]

private theorem bound_115 : middleNormalized (⟨[1,1],[3,1]⟩ : MiddleCore) = (⟨[1,1],[3,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_114, ite_true]

private theorem bound_116 : (10550504633/40000000000:ℝ) ≤ prefixEval [3,1,3] middleBeta ∧ prefixEval [3,1,3] middleBeta ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,3] middleBeta) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (3791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_117 : (265571424117/1000000000000:ℝ) ≤ prefixEval [3,1,3] middleAlpha ∧ prefixEval [3,1,3] middleAlpha ≤ (265571424119/1000000000000:ℝ) := by
  suffices hh : (265571424117/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,3] middleAlpha) ≤ (265571424119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (376546536707/100000000000:ℝ) (3765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_027.1, bound_027.2]
  · norm_num
  · norm_num

private theorem bound_118 : (180880829/100000000000:ℝ) ≤ middleWidth [3,1,3] ∧ middleWidth [3,1,3] ≤ (904404147/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_116.2, bound_117.1])]
  constructor <;> linarith only [bound_116.1, bound_116.2, bound_117.1, bound_117.2]

private theorem bound_119 : ¬ (middleWidth [1,1,3] ≤ (7/5:ℝ) * middleWidth [3,1,3]) := by linarith only [bound_079.1, bound_118.2]

private theorem bound_120 : (52788901897/200000000000:ℝ) ≤ prefixEval [3,1,3] middleRho ∧ prefixEval [3,1,3] middleRho ≤ (131972254743/500000000000:ℝ) := by
  suffices hh : (52788901897/200000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleRho) ∧ 1 / (3 + prefixEval [1,3] middleRho) ≤ (131972254743/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1894337567297/500000000000:ℝ) (757735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_034.1, bound_034.2]
  · norm_num
  · norm_num

private theorem bound_121 : middleE3 (⟨[1,1],[3,1]⟩ : MiddleCore) = 4 + prefixEval [1,1] middleAlpha + prefixEval [3,1,3] middleRho := by
  norm_num [middleE3, bound_119]

private theorem bound_122 : (241110103949/50000000000:ℝ) ≤ middleE3 (⟨[1,1],[3,1]⟩ : MiddleCore) ∧ middleE3 (⟨[1,1],[3,1]⟩ : MiddleCore) ≤ (2411101039491/500000000000:ℝ) := by
  rw [bound_121]
  constructor <;> linarith only [bound_073.1, bound_073.2, bound_120.1, bound_120.2]

private theorem bound_123 : (281036428777/1000000000000:ℝ) ≤ prefixEval [3,1,1,3] middleBeta ∧ prefixEval [3,1,1,3] middleBeta ≤ (140518214389/500000000000:ℝ) := by
  suffices hh : (281036428777/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,1,3] middleBeta) ≤ (140518214389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (711651513899/200000000000:ℝ) (444782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_040.1, bound_040.2]
  · norm_num
  · norm_num

private theorem bound_124 : (280392996039/1000000000000:ℝ) ≤ prefixEval [3,1,1,3] middleAlpha ∧ prefixEval [3,1,1,3] middleAlpha ≤ (7009824901/25000000000:ℝ) := by
  suffices hh : (280392996039/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,1,3] middleAlpha) ≤ (7009824901/25000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3566422892599/1000000000000:ℝ) (17832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_043.1, bound_043.2]
  · norm_num
  · norm_num

private theorem bound_125 : (643432737/1000000000000:ℝ) ≤ middleWidth [3,1,1,3] ∧ middleWidth [3,1,1,3] ≤ (643432739/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_123.1, bound_124.2])]
  constructor <;> linarith only [bound_123.1, bound_123.2, bound_124.1, bound_124.2]

private theorem bound_126 : ¬ (middleWidth [1,1,1,3] ≤ (7/5:ℝ) * middleWidth [3,1,1,3]) := by linarith only [bound_085.1, bound_125.2]

private theorem bound_127 : (14048601923/50000000000:ℝ) ≤ prefixEval [3,1,1,3] middleRho ∧ prefixEval [3,1,1,3] middleRho ≤ (280972038461/1000000000000:ℝ) := by
  suffices hh : (14048601923/50000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleRho) ∧ 1 / (3 + prefixEval [1,1,3] middleRho) ≤ (280972038461/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1779536507401/500000000000:ℝ) (3559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_128 : middleE13 (⟨[1,1],[3,1]⟩ : MiddleCore) = 4 + prefixEval [1,1] middleBeta + prefixEval [3,1,1,3] middleRho := by
  norm_num [middleE13, bound_126]

private theorem bound_129 : (1230678617241/250000000000:ℝ) ≤ middleE13 (⟨[1,1],[3,1]⟩ : MiddleCore) ∧ middleE13 (⟨[1,1],[3,1]⟩ : MiddleCore) ≤ (2461357234483/500000000000:ℝ) := by
  rw [bound_128]
  constructor <;> linarith only [bound_072.1, bound_072.2, bound_127.1, bound_127.2]

private theorem bound_130 : middleEqualBounds (⟨[1,1],[3,1]⟩ : MiddleCore) = (middleE3 (⟨[1,1],[3,1]⟩ : MiddleCore), middleE13 (⟨[1,1],[3,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_115]

private theorem bound_131 : ¬ (middleWidth [3] ≤ middleWidth [1,1,1]) := by linarith only [bound_108.1, bound_092.2]

private theorem bound_132 : middleNormalized (⟨[1,1,1],[3]⟩ : MiddleCore) = (⟨[3],[1,1,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_131, ite_false]

private theorem bound_133 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3,3] middleBeta ∧ prefixEval [3,3] middleBeta ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleBeta) ∧ 1 / (3 + prefixEval [3] middleBeta) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (3263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_019.1, bound_019.2]
  · norm_num
  · norm_num

private theorem bound_134 : (151222109073/500000000000:ℝ) ≤ prefixEval [3,3] middleAlpha ∧ prefixEval [3,3] middleAlpha ≤ (302444218147/1000000000000:ℝ) := by
  suffices hh : (151222109073/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleAlpha) ∧ 1 / (3 + prefixEval [3] middleAlpha) ≤ (302444218147/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3306394832501/1000000000000:ℝ) (1653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_021.1, bound_021.2]
  · norm_num
  · norm_num

private theorem bound_135 : (1975307177/500000000000:ℝ) ≤ middleWidth [3,3] ∧ middleWidth [3,3] ≤ (987653589/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_133.1, bound_134.2])]
  constructor <;> linarith only [bound_133.1, bound_133.2, bound_134.1, bound_134.2]

private theorem bound_136 : middleWidth [3,3] ≤ (7/5:ℝ) * middleWidth [1,1,1,3] := by linarith only [bound_135.2, bound_085.1]

private theorem bound_137 : (153001154717/500000000000:ℝ) ≤ prefixEval [3,3] middleRho ∧ prefixEval [3,3] middleRho ≤ (61200461887/200000000000:ℝ) := by
  suffices hh : (153001154717/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleRho) ∧ 1 / (3 + prefixEval [3] middleRho) ≤ (61200461887/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3267949192431/1000000000000:ℝ) (204246824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_033.1, bound_033.2]
  · norm_num
  · norm_num

private theorem bound_138 : (287979054337/500000000000:ℝ) ≤ prefixEval [1,1,2] middleBeta ∧ prefixEval [1,1,2] middleBeta ≤ (143989527169/250000000000:ℝ) := by
  suffices hh : (287979054337/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2] middleBeta) ∧ 1 / (1 + prefixEval [1,2] middleBeta) ≤ (143989527169/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1736237384173/1000000000000:ℝ) (69449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_139 : (19829207279/31250000000:ℝ) ≤ prefixEval [1,1,1,2] middleBeta ∧ prefixEval [1,1,1,2] middleBeta ≤ (63453463293/100000000000:ℝ) := by
  suffices hh : (19829207279/31250000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,2] middleBeta) ∧ 1 / (1 + prefixEval [1,1,2] middleBeta) ≤ (63453463293/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (787979054337/500000000000:ℝ) (393989527169/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_138.1, bound_138.2]
  · norm_num
  · norm_num

private theorem bound_140 : middleE3 (⟨[3],[1,1,1]⟩ : MiddleCore) = 4 + prefixEval [3,3] middleRho + prefixEval [1,1,1,2] middleBeta := by
  norm_num [middleE3, bound_136]

private theorem bound_141 : (2470268471181/500000000000:ℝ) ≤ middleE3 (⟨[3],[1,1,1]⟩ : MiddleCore) ∧ middleE3 (⟨[3],[1,1,1]⟩ : MiddleCore) ≤ (988107388473/200000000000:ℝ) := by
  rw [bound_140]
  constructor <;> linarith only [bound_137.1, bound_137.2, bound_139.1, bound_139.2]

private theorem bound_142 : ¬ (middleWidth [3,1,3] ≤ (7/5:ℝ) * middleWidth [1,1,1,1,3]) := by linarith only [bound_118.1, bound_101.2]

private theorem bound_143 : middleE13 (⟨[3],[1,1,1]⟩ : MiddleCore) = 4 + prefixEval [3] middleBeta + prefixEval [1,1,1,1,3] middleRho := by
  norm_num [middleE13, bound_142]

private theorem bound_144 : (4872996117871/1000000000000:ℝ) ≤ middleE13 (⟨[3],[1,1,1]⟩ : MiddleCore) ∧ middleE13 (⟨[3],[1,1,1]⟩ : MiddleCore) ≤ (38983968943/8000000000:ℝ) := by
  rw [bound_143]
  constructor <;> linarith only [bound_019.1, bound_019.2, bound_103.1, bound_103.2]

private theorem bound_145 : middleEqualBounds (⟨[1,1,1],[3]⟩ : MiddleCore) = (middleE13 (⟨[3],[1,1,1]⟩ : MiddleCore), middleE3 (⟨[3],[1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_132]

private theorem bound_146 : middleBounds (⟨[1,1],[3]⟩ : MiddleCore) = (middleE3 (⟨[1,1],[3,1]⟩ : MiddleCore), middleE3 (⟨[3],[1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_110, bound_130, bound_145]

private theorem bound_147 : middleWidth [2] ≤ middleWidth [2] := le_rfl

private theorem bound_148 : middleNormalized (⟨[2],[2]⟩ : MiddleCore) = (⟨[2],[2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_147, ite_true]

private theorem bound_149 : middleWidth [2,3] ≤ (7/5:ℝ) * middleWidth [2,3] := by linarith only [bound_023.2, bound_023.1]

private theorem bound_150 : (106010472831/250000000000:ℝ) ≤ prefixEval [2,2] middleBeta ∧ prefixEval [2,2] middleBeta ≤ (16961675653/40000000000:ℝ) := by
  suffices hh : (106010472831/250000000000:ℝ) ≤ 1 / (2 + prefixEval [2] middleBeta) ∧ 1 / (2 + prefixEval [2] middleBeta) ≤ (16961675653/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (471651513899/200000000000:ℝ) (294782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_151 : middleE3 (⟨[2],[2]⟩ : MiddleCore) = 4 + prefixEval [2,3] middleRho + prefixEval [2,2] middleBeta := by
  norm_num [middleE3, bound_149]

private theorem bound_152 : (4864968876521/1000000000000:ℝ) ≤ middleE3 (⟨[2],[2]⟩ : MiddleCore) ∧ middleE3 (⟨[2],[2]⟩ : MiddleCore) ≤ (4864968876523/1000000000000:ℝ) := by
  rw [bound_151]
  constructor <;> linarith only [bound_061.1, bound_061.2, bound_150.1, bound_150.2]

private theorem bound_153 : middleWidth [2,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,3] := by linarith only [bound_039.2, bound_039.1]

private theorem bound_154 : middleE13 (⟨[2],[2]⟩ : MiddleCore) = 4 + prefixEval [2,1,3] middleRho + prefixEval [2,1,2] middleBeta := by
  norm_num [middleE13, bound_153]

private theorem bound_155 : (4724058588487/1000000000000:ℝ) ≤ middleE13 (⟨[2],[2]⟩ : MiddleCore) ∧ middleE13 (⟨[2],[2]⟩ : MiddleCore) ≤ (4724058588489/1000000000000:ℝ) := by
  rw [bound_154]
  constructor <;> linarith only [bound_035.1, bound_035.2, bound_063.1, bound_063.2]

private theorem bound_156 : middleEqualBounds (⟨[2],[2]⟩ : MiddleCore) = (middleE13 (⟨[2],[2]⟩ : MiddleCore), middleE3 (⟨[2],[2]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_148]

private theorem bound_157 : middleBounds (⟨[2],[2]⟩ : MiddleCore) = (middleE13 (⟨[2],[2]⟩ : MiddleCore), middleE3 (⟨[2],[2]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_148, bound_156]

private theorem bound_158 : middleWidth [3] ≤ middleWidth [2] := by linarith only [bound_108.2, bound_007.1]

private theorem bound_159 : middleNormalized (⟨[2],[3]⟩ : MiddleCore) = (⟨[2],[3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_158, ite_true]

private theorem bound_160 : ¬ (middleWidth [2,3] ≤ (7/5:ℝ) * middleWidth [3,3]) := by linarith only [bound_023.1, bound_135.2]

private theorem bound_161 : middleE3 (⟨[2],[3]⟩ : MiddleCore) = 4 + prefixEval [2] middleAlpha + prefixEval [3,3] middleRho := by
  norm_num [middleE3, bound_160]

private theorem bound_162 : (2373872369969/500000000000:ℝ) ≤ middleE3 (⟨[2],[3]⟩ : MiddleCore) ∧ middleE3 (⟨[2],[3]⟩ : MiddleCore) ≤ (237387236997/50000000000:ℝ) := by
  rw [bound_161]
  constructor <;> linarith only [bound_004.1, bound_004.2, bound_137.1, bound_137.2]

private theorem bound_163 : ¬ (middleWidth [2,1,3] ≤ (7/5:ℝ) * middleWidth [3,1,3]) := by linarith only [bound_039.1, bound_118.2]

private theorem bound_164 : middleE13 (⟨[2],[3]⟩ : MiddleCore) = 4 + prefixEval [2] middleBeta + prefixEval [3,1,3] middleRho := by
  norm_num [middleE13, bound_163]

private theorem bound_165 : (231110103949/50000000000:ℝ) ≤ middleE13 (⟨[2],[3]⟩ : MiddleCore) ∧ middleE13 (⟨[2],[3]⟩ : MiddleCore) ≤ (2311101039491/500000000000:ℝ) := by
  rw [bound_164]
  constructor <;> linarith only [bound_001.1, bound_001.2, bound_120.1, bound_120.2]

private theorem bound_166 : middleEqualBounds (⟨[2],[3]⟩ : MiddleCore) = (middleE13 (⟨[2],[3]⟩ : MiddleCore), middleE3 (⟨[2],[3]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_159]

private theorem bound_167 : middleBounds (⟨[2],[3]⟩ : MiddleCore) = (middleE13 (⟨[2],[3]⟩ : MiddleCore), middleE3 (⟨[2],[3]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_159, bound_166]

private theorem root_0 : middleRootCertificate 0 := by
  change middleRegular (⟨[1,2],[2]⟩ : MiddleCore) ∧ middleRatio (⟨[1,2],[2]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[1,2],[2]⟩ : MiddleCore)).1 < middleInnerLeft 0 ∧ middleInnerRight 0 < (middleBounds (⟨[1,2],[2]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_006.1]
    · linarith only [bound_007.1]
  constructor
  · have h73 : (1958257569399/1000000000000:ℝ) ≤ middleWidth [2] / middleWidth [1,2] ∧ middleWidth [2] / middleWidth [1,2] ≤ (122391098099/62500000000:ℝ) := by
      apply div_est _ _ (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) (21316108337/500000000000:ℝ) (42632216677/1000000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_007 bound_006 <;> norm_num
    simp only [middleRatio, bound_009]
    linarith only [h73.2]
  rw [bound_071]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_065.2]
  · linarith only [bound_038.1]



private theorem root_1 : middleRootCertificate 1 := by
  change middleRegular (⟨[1,1],[2]⟩ : MiddleCore) ∧ middleRatio (⟨[1,1],[2]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[1,1],[2]⟩ : MiddleCore)).1 < middleInnerLeft 1 ∧ middleInnerRight 1 < (middleBounds (⟨[1,1],[2]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_074.1]
    · linarith only [bound_007.1]
  constructor
  · have h68 : (124999999997/125000000000:ℝ) ≤ middleWidth [1,1] / middleWidth [2] ∧ middleWidth [1,1] / middleWidth [2] ≤ (125000000003/125000000000:ℝ) := by
      apply div_est _ _ (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_074 bound_007 <;> norm_num
    simp only [middleRatio, bound_076]
    linarith only [h68.2]
  rw [bound_107]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_082.2]
  · linarith only [bound_098.1]



private theorem root_2 : middleRootCertificate 2 := by
  change middleRegular (⟨[1,1],[3]⟩ : MiddleCore) ∧ middleRatio (⟨[1,1],[3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[1,1],[3]⟩ : MiddleCore)).1 < middleInnerLeft 2 ∧ middleInnerRight 2 < (middleBounds (⟨[1,1],[3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_074.1]
    · linarith only [bound_108.1]
  constructor
  · have h71 : (1958257569399/1000000000000:ℝ) ≤ middleWidth [1,1] / middleWidth [3] ∧ middleWidth [1,1] / middleWidth [3] ≤ (122391098099/62500000000:ℝ) := by
      apply div_est _ _ (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) (21316108337/500000000000:ℝ) (42632216677/1000000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_074 bound_108 <;> norm_num
    simp only [middleRatio, bound_110]
    linarith only [h71.2]
  rw [bound_146]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_122.2]
  · linarith only [bound_141.1]



private theorem root_3 : middleRootCertificate 3 := by
  change middleRegular (⟨[2],[2]⟩ : MiddleCore) ∧ middleRatio (⟨[2],[2]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2],[2]⟩ : MiddleCore)).1 < middleInnerLeft 3 ∧ middleInnerRight 3 < (middleBounds (⟨[2],[2]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_007.1]
    · linarith only [bound_007.1]
  constructor
  · have h34 : (124999999997/125000000000:ℝ) ≤ middleWidth [2] / middleWidth [2] ∧ middleWidth [2] / middleWidth [2] ≤ (125000000003/125000000000:ℝ) := by
      apply div_est _ _ (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_007 bound_007 <;> norm_num
    simp only [middleRatio, bound_148]
    linarith only [h34.2]
  rw [bound_157]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_155.2]
  · linarith only [bound_152.1]



private theorem root_4 : middleRootCertificate 4 := by
  change middleRegular (⟨[2],[3]⟩ : MiddleCore) ∧ middleRatio (⟨[2],[3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2],[3]⟩ : MiddleCore)).1 < middleInnerLeft 4 ∧ middleInnerRight 4 < (middleBounds (⟨[2],[3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_007.1]
    · linarith only [bound_108.1]
  constructor
  · have h38 : (1958257569399/1000000000000:ℝ) ≤ middleWidth [2] / middleWidth [3] ∧ middleWidth [2] / middleWidth [3] ≤ (122391098099/62500000000:ℝ) := by
      apply div_est _ _ (5217803813/62500000000:ℝ) (8348486101/100000000000:ℝ) (21316108337/500000000000:ℝ) (42632216677/1000000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_007 bound_108 <;> norm_num
    simp only [middleRatio, bound_159]
    linarith only [h38.2]
  rw [bound_167]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_165.2]
  · linarith only [bound_162.1]


end M8Sep10InitialRootsOpt

theorem solution : ∀ i : Fin 15, 0 ≤ i.val → i.val < 5 → middleRootCertificate i := by
  intro i hlo hi
  fin_cases i <;> norm_num at hlo <;> norm_num at hi <;> first | exact M8Sep10InitialRootsOpt.root_0 | exact M8Sep10InitialRootsOpt.root_1 | exact M8Sep10InitialRootsOpt.root_2 | exact M8Sep10InitialRootsOpt.root_3 | exact M8Sep10InitialRootsOpt.root_4
#print axioms solution
