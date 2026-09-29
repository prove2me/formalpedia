-- Prove2me | solution 1 for Freiman.middle_initial_roots_2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:51:07.166978+00:00
-- url     : https://prove2.me/submissions/cc76431c-9b3c-4d72-8f5b-551f644de2f0

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
open Freiman
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
namespace M8Sep10InitialRoots2Opt

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

private theorem bound_001 : (10550504633/40000000000:ℝ) ≤ prefixEval [3] middleBeta ∧ prefixEval [3] middleBeta ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + middleBeta) ∧ 1 / (3 + middleBeta) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (1895643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_002 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1,3] middleBeta ∧ prefixEval [1,3] middleBeta ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleBeta) ∧ 1 / (1 + prefixEval [3] middleBeta) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (1263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_003 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1,3] middleBeta ∧ prefixEval [1,1,3] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3] middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_004 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1,1,3] middleBeta ∧ prefixEval [2,1,1,3] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_005 : (10550504633/40000000000:ℝ) ≤ middleAlpha ∧ middleAlpha ≤ (131881307913/500000000000:ℝ) := by
  dsimp only [middleAlpha]
  constructor <;> linarith only [sqrt_21_bounds.1, sqrt_21_bounds.2]

private theorem bound_006 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3] middleAlpha ∧ prefixEval [3] middleAlpha ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + middleAlpha) ∧ 1 / (3 + middleAlpha) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (1631881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_005.1, bound_005.2]
  · norm_num
  · norm_num

private theorem bound_007 : (76546536707/100000000000:ℝ) ≤ prefixEval [1,3] middleAlpha ∧ prefixEval [1,3] middleAlpha ≤ (765465367071/1000000000000:ℝ) := by
  suffices hh : (76546536707/100000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleAlpha) ∧ 1 / (1 + prefixEval [3] middleAlpha) ≤ (765465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1306394832501/1000000000000:ℝ) (653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_008 : (566422892599/1000000000000:ℝ) ≤ prefixEval [1,1,3] middleAlpha ∧ prefixEval [1,1,3] middleAlpha ≤ (2832114463/5000000000:ℝ) := by
  suffices hh : (566422892599/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3] middleAlpha) ≤ (2832114463/5000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (176546536707/100000000000:ℝ) (1765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_007.1, bound_007.2]
  · norm_num
  · norm_num

private theorem bound_009 : (77929479423/200000000000:ℝ) ≤ prefixEval [2,1,1,3] middleAlpha ∧ prefixEval [2,1,1,3] middleAlpha ≤ (97411849279/250000000000:ℝ) := by
  suffices hh : (77929479423/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3] middleAlpha) ≤ (97411849279/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2566422892599/1000000000000:ℝ) (12832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_008.1, bound_008.2]
  · norm_num
  · norm_num

private theorem bound_010 : (248731553/200000000000:ℝ) ≤ middleWidth [2,1,1,3] ∧ middleWidth [2,1,1,3] ≤ (155457221/125000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_004.1, bound_009.2])]
  constructor <;> linarith only [bound_004.1, bound_004.2, bound_009.1, bound_009.2]

private theorem bound_011 : (234534632929/1000000000000:ℝ) ≤ prefixEval [4,3] middleBeta ∧ prefixEval [4,3] middleBeta ≤ (23453463293/100000000000:ℝ) := by
  suffices hh : (234534632929/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3] middleBeta) ∧ 1 / (4 + prefixEval [3] middleBeta) ≤ (23453463293/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (170550504633/40000000000:ℝ) (4263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_012 : (29026599943/125000000000:ℝ) ≤ prefixEval [4,3] middleAlpha ∧ prefixEval [4,3] middleAlpha ≤ (46442559909/200000000000:ℝ) := by
  suffices hh : (29026599943/125000000000:ℝ) ≤ 1 / (4 + prefixEval [3] middleAlpha) ∧ 1 / (4 + prefixEval [3] middleAlpha) ≤ (46442559909/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4306394832501/1000000000000:ℝ) (2153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_013 : (290229173/125000000000:ℝ) ≤ middleWidth [4,3] ∧ middleWidth [4,3] ≤ (1160916693/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_011.1, bound_012.2])]
  constructor <;> linarith only [bound_011.1, bound_011.2, bound_012.1, bound_012.2]

private theorem bound_014 : ¬ (middleWidth [4,3] ≤ middleWidth [2,1,1,3]) := by linarith only [bound_013.1, bound_010.2]

private theorem bound_015 : middleNormalized (⟨[2,1,1,3],[4,3]⟩ : MiddleCore) = (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_014, ite_false]

private theorem bound_016 : middleWidth [2,1,1,3] ≤ middleWidth [4,3] := by linarith only [bound_010.2, bound_013.1]

private theorem bound_017 : middleNormalized (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) = (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_016, ite_true]

private theorem bound_018 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3,3] middleBeta ∧ prefixEval [3,3] middleBeta ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleBeta) ∧ 1 / (3 + prefixEval [3] middleBeta) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (3263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_019 : (29026599943/125000000000:ℝ) ≤ prefixEval [4,3,3] middleBeta ∧ prefixEval [4,3,3] middleBeta ≤ (46442559909/200000000000:ℝ) := by
  suffices hh : (29026599943/125000000000:ℝ) ≤ 1 / (4 + prefixEval [3,3] middleBeta) ∧ 1 / (4 + prefixEval [3,3] middleBeta) ≤ (46442559909/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4306394832501/1000000000000:ℝ) (2153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_018.1, bound_018.2]
  · norm_num
  · norm_num

private theorem bound_020 : (151222109073/500000000000:ℝ) ≤ prefixEval [3,3] middleAlpha ∧ prefixEval [3,3] middleAlpha ≤ (302444218147/1000000000000:ℝ) := by
  suffices hh : (151222109073/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleAlpha) ∧ 1 / (3 + prefixEval [3] middleAlpha) ≤ (302444218147/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3306394832501/1000000000000:ℝ) (1653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_021 : (116213011639/500000000000:ℝ) ≤ prefixEval [4,3,3] middleAlpha ∧ prefixEval [4,3,3] middleAlpha ≤ (232426023279/1000000000000:ℝ) := by
  suffices hh : (116213011639/500000000000:ℝ) ≤ 1 / (4 + prefixEval [3,3] middleAlpha) ∧ 1 / (4 + prefixEval [3,3] middleAlpha) ≤ (232426023279/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2151222109073/500000000000:ℝ) (4302444218147/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_020.1, bound_020.2]
  · norm_num
  · norm_num

private theorem bound_022 : (213223733/1000000000000:ℝ) ≤ middleWidth [4,3,3] ∧ middleWidth [4,3,3] ≤ (42644747/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_019.2, bound_021.1])]
  constructor <;> linarith only [bound_019.1, bound_019.2, bound_021.1, bound_021.2]

private theorem bound_023 : (76546536707/100000000000:ℝ) ≤ prefixEval [1,3,3] middleBeta ∧ prefixEval [1,3,3] middleBeta ≤ (765465367071/1000000000000:ℝ) := by
  suffices hh : (76546536707/100000000000:ℝ) ≤ 1 / (1 + prefixEval [3,3] middleBeta) ∧ 1 / (1 + prefixEval [3,3] middleBeta) ≤ (765465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1306394832501/1000000000000:ℝ) (653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_018.1, bound_018.2]
  · norm_num
  · norm_num

private theorem bound_024 : (566422892599/1000000000000:ℝ) ≤ prefixEval [1,1,3,3] middleBeta ∧ prefixEval [1,1,3,3] middleBeta ≤ (2832114463/5000000000:ℝ) := by
  suffices hh : (566422892599/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,3] middleBeta) ≤ (2832114463/5000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (176546536707/100000000000:ℝ) (1765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_023.1, bound_023.2]
  · norm_num
  · norm_num

private theorem bound_025 : (77929479423/200000000000:ℝ) ≤ prefixEval [2,1,1,3,3] middleBeta ∧ prefixEval [2,1,1,3,3] middleBeta ≤ (97411849279/250000000000:ℝ) := by
  suffices hh : (77929479423/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,3] middleBeta) ≤ (97411849279/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2566422892599/1000000000000:ℝ) (12832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_026 : (153557440091/200000000000:ℝ) ≤ prefixEval [1,3,3] middleAlpha ∧ prefixEval [1,3,3] middleAlpha ≤ (95973400057/125000000000:ℝ) := by
  suffices hh : (153557440091/200000000000:ℝ) ≤ 1 / (1 + prefixEval [3,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,3] middleAlpha) ≤ (95973400057/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (651222109073/500000000000:ℝ) (1302444218147/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_020.1, bound_020.2]
  · norm_num
  · norm_num

private theorem bound_027 : (282839472913/500000000000:ℝ) ≤ prefixEval [1,1,3,3] middleAlpha ∧ prefixEval [1,1,3,3] middleAlpha ≤ (141419736457/250000000000:ℝ) := by
  suffices hh : (282839472913/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,3] middleAlpha) ≤ (141419736457/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (353557440091/200000000000:ℝ) (220973400057/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_026.1, bound_026.2]
  · norm_num
  · norm_num

private theorem bound_028 : (77952075931/200000000000:ℝ) ≤ prefixEval [2,1,1,3,3] middleAlpha ∧ prefixEval [2,1,1,3,3] middleAlpha ≤ (48720047457/125000000000:ℝ) := by
  suffices hh : (77952075931/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,3] middleAlpha) ≤ (48720047457/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1282839472913/500000000000:ℝ) (641419736457/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_027.1, bound_027.2]
  · norm_num
  · norm_num

private theorem bound_029 : (112982539/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,3] ∧ middleWidth [2,1,1,3,3] ≤ (112982541/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_025.2, bound_028.1])]
  constructor <;> linarith only [bound_025.1, bound_025.2, bound_028.1, bound_028.2]

private theorem bound_030 : ¬ (middleWidth [4,3,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,3]) := by linarith only [bound_022.1, bound_029.2]

private theorem bound_031 : (45753175473/62500000000:ℝ) ≤ middleRho ∧ middleRho ≤ (732050807569/1000000000000:ℝ) := by
  dsimp only [middleRho]
  constructor <;> linarith only [sqrt_3_bounds.1, sqrt_3_bounds.2]

private theorem bound_032 : (267949192431/1000000000000:ℝ) ≤ prefixEval [3] middleRho ∧ prefixEval [3] middleRho ≤ (16746824527/62500000000:ℝ) := by
  suffices hh : (267949192431/1000000000000:ℝ) ≤ 1 / (3 + middleRho) ∧ 1 / (3 + middleRho) ≤ (16746824527/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (233253175473/62500000000:ℝ) (3732050807569/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_031.1, bound_031.2]
  · norm_num
  · norm_num

private theorem bound_033 : (153001154717/500000000000:ℝ) ≤ prefixEval [3,3] middleRho ∧ prefixEval [3,3] middleRho ≤ (61200461887/200000000000:ℝ) := by
  suffices hh : (153001154717/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleRho) ∧ 1 / (3 + prefixEval [3] middleRho) ≤ (61200461887/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3267949192431/1000000000000:ℝ) (204246824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_032.1, bound_032.2]
  · norm_num
  · norm_num

private theorem bound_034 : (765695430073/1000000000000:ℝ) ≤ prefixEval [1,3,3] middleRho ∧ prefixEval [1,3,3] middleRho ≤ (30627817203/40000000000:ℝ) := by
  suffices hh : (765695430073/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,3] middleRho) ∧ 1 / (1 + prefixEval [3,3] middleRho) ≤ (30627817203/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (653001154717/500000000000:ℝ) (261200461887/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_033.1, bound_033.2]
  · norm_num
  · norm_num

private theorem bound_035 : (566349089977/1000000000000:ℝ) ≤ prefixEval [1,1,3,3] middleRho ∧ prefixEval [1,1,3,3] middleRho ≤ (283174544989/500000000000:ℝ) := by
  suffices hh : (566349089977/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,3] middleRho) ∧ 1 / (1 + prefixEval [1,3,3] middleRho) ≤ (283174544989/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1765695430073/1000000000000:ℝ) (70627817203/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_034.1, bound_034.2]
  · norm_num
  · norm_num

private theorem bound_036 : (12176831329/31250000000:ℝ) ≤ prefixEval [2,1,1,3,3] middleRho ∧ prefixEval [2,1,1,3,3] middleRho ≤ (389658602529/1000000000000:ℝ) := by
  suffices hh : (12176831329/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3,3] middleRho) ≤ (389658602529/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2566349089977/1000000000000:ℝ) (1283174544989/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_035.1, bound_035.2]
  · norm_num
  · norm_num

private theorem bound_037 : middleE3 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) = 4 + prefixEval [4,3] middleAlpha + prefixEval [2,1,1,3,3] middleRho := by
  norm_num [middleE3, bound_030]

private theorem bound_038 : (577733925259/125000000000:ℝ) ≤ middleE3 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) ∧ middleE3 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) ≤ (2310935701037/500000000000:ℝ) := by
  rw [bound_037]
  constructor <;> linarith only [bound_012.1, bound_012.2, bound_036.1, bound_036.2]

private theorem bound_039 : (10550504633/40000000000:ℝ) ≤ prefixEval [3,1,3] middleBeta ∧ prefixEval [3,1,3] middleBeta ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,3] middleBeta) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (3791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_040 : (234534632929/1000000000000:ℝ) ≤ prefixEval [4,3,1,3] middleBeta ∧ prefixEval [4,3,1,3] middleBeta ≤ (23453463293/100000000000:ℝ) := by
  suffices hh : (234534632929/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,3] middleBeta) ∧ 1 / (4 + prefixEval [3,1,3] middleBeta) ≤ (23453463293/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (170550504633/40000000000:ℝ) (4263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_039.1, bound_039.2]
  · norm_num
  · norm_num

private theorem bound_041 : (265571424117/1000000000000:ℝ) ≤ prefixEval [3,1,3] middleAlpha ∧ prefixEval [3,1,3] middleAlpha ≤ (265571424119/1000000000000:ℝ) := by
  suffices hh : (265571424117/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,3] middleAlpha) ≤ (265571424119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (376546536707/100000000000:ℝ) (3765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_007.1, bound_007.2]
  · norm_num
  · norm_num

private theorem bound_042 : (234435178917/1000000000000:ℝ) ≤ prefixEval [4,3,1,3] middleAlpha ∧ prefixEval [4,3,1,3] middleAlpha ≤ (117217589459/500000000000:ℝ) := by
  suffices hh : (234435178917/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [3,1,3] middleAlpha) ≤ (117217589459/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4265571424117/1000000000000:ℝ) (4265571424119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_041.1, bound_041.2]
  · norm_num
  · norm_num

private theorem bound_043 : (99454011/1000000000000:ℝ) ≤ middleWidth [4,3,1,3] ∧ middleWidth [4,3,1,3] ≤ (99454013/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_040.1, bound_042.2])]
  constructor <;> linarith only [bound_040.1, bound_040.2, bound_042.1, bound_042.2]

private theorem bound_044 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1,3,1,3] middleBeta ∧ prefixEval [1,3,1,3] middleBeta ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,3] middleBeta) ∧ 1 / (1 + prefixEval [3,1,3] middleBeta) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (1263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_039.1, bound_039.2]
  · norm_num
  · norm_num

private theorem bound_045 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1,3,1,3] middleBeta ∧ prefixEval [1,1,3,1,3] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,1,3] middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_044.1, bound_044.2]
  · norm_num
  · norm_num

private theorem bound_046 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,3] middleBeta ∧ prefixEval [2,1,1,3,1,3] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,1,3] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_045.1, bound_045.2]
  · norm_num
  · norm_num

private theorem bound_047 : (197539226341/250000000000:ℝ) ≤ prefixEval [1,3,1,3] middleAlpha ∧ prefixEval [1,3,1,3] middleAlpha ≤ (790156905367/1000000000000:ℝ) := by
  suffices hh : (197539226341/250000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,1,3] middleAlpha) ≤ (790156905367/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1265571424117/1000000000000:ℝ) (1265571424119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_041.1, bound_041.2]
  · norm_num
  · norm_num

private theorem bound_048 : (111722050397/200000000000:ℝ) ≤ prefixEval [1,1,3,1,3] middleAlpha ∧ prefixEval [1,1,3,1,3] middleAlpha ≤ (558610251987/1000000000000:ℝ) := by
  suffices hh : (111722050397/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,1,3] middleAlpha) ≤ (558610251987/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (447539226341/250000000000:ℝ) (1790156905367/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_047.1, bound_047.2]
  · norm_num
  · norm_num

private theorem bound_049 : (3908371739/10000000000:ℝ) ≤ prefixEval [2,1,1,3,1,3] middleAlpha ∧ prefixEval [2,1,1,3,1,3] middleAlpha ≤ (195418586951/500000000000:ℝ) := by
  suffices hh : (3908371739/10000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,1,3] middleAlpha) ≤ (195418586951/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511722050397/200000000000:ℝ) (2558610251987/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_050 : (53880979/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,1,3] ∧ middleWidth [2,1,1,3,1,3] ≤ (53880983/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_046.1, bound_049.2])]
  constructor <;> linarith only [bound_046.1, bound_046.2, bound_049.1, bound_049.2]

private theorem bound_051 : ¬ (middleWidth [4,3,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,1,3]) := by linarith only [bound_043.1, bound_050.2]

private theorem bound_052 : (394337567297/500000000000:ℝ) ≤ prefixEval [1,3] middleRho ∧ prefixEval [1,3] middleRho ≤ (157735026919/200000000000:ℝ) := by
  suffices hh : (394337567297/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleRho) ∧ 1 / (1 + prefixEval [3] middleRho) ≤ (157735026919/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1267949192431/1000000000000:ℝ) (79246824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_032.1, bound_032.2]
  · norm_num
  · norm_num

private theorem bound_053 : (52788901897/200000000000:ℝ) ≤ prefixEval [3,1,3] middleRho ∧ prefixEval [3,1,3] middleRho ≤ (131972254743/500000000000:ℝ) := by
  suffices hh : (52788901897/200000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleRho) ∧ 1 / (3 + prefixEval [1,3] middleRho) ≤ (131972254743/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1894337567297/500000000000:ℝ) (757735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_052.1, bound_052.2]
  · norm_num
  · norm_num

private theorem bound_054 : (158234794723/200000000000:ℝ) ≤ prefixEval [1,3,1,3] middleRho ∧ prefixEval [1,3,1,3] middleRho ≤ (791173973617/1000000000000:ℝ) := by
  suffices hh : (158234794723/200000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,3] middleRho) ∧ 1 / (1 + prefixEval [3,1,3] middleRho) ≤ (791173973617/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (252788901897/200000000000:ℝ) (631972254743/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_053.1, bound_053.2]
  · norm_num
  · norm_num

private theorem bound_055 : (69786632589/125000000000:ℝ) ≤ prefixEval [1,1,3,1,3] middleRho ∧ prefixEval [1,1,3,1,3] middleRho ≤ (279146530357/500000000000:ℝ) := by
  suffices hh : (69786632589/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,3,1,3] middleRho) ≤ (279146530357/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (358234794723/200000000000:ℝ) (1791173973617/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_054.1, bound_054.2]
  · norm_num
  · norm_num

private theorem bound_056 : (390885632047/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,3] middleRho ∧ prefixEval [2,1,1,3,1,3] middleRho ≤ (24430352003/62500000000:ℝ) := by
  suffices hh : (390885632047/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3,1,3] middleRho) ≤ (24430352003/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (319786632589/125000000000:ℝ) (1279146530357/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_055.1, bound_055.2]
  · norm_num
  · norm_num

private theorem bound_057 : middleE13 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) = 4 + prefixEval [4,3] middleBeta + prefixEval [2,1,1,3,1,3] middleRho := by
  norm_num [middleE13, bound_051]

private theorem bound_058 : (289088766561/62500000000:ℝ) ≤ middleE13 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) ∧ middleE13 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) ≤ (2312710132489/500000000000:ℝ) := by
  rw [bound_057]
  constructor <;> linarith only [bound_011.1, bound_011.2, bound_056.1, bound_056.2]

private theorem bound_059 : middleEqualBounds (⟨[4,3],[2,1,1,3]⟩ : MiddleCore) = (middleE3 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore), middleE13 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_017]

private theorem bound_060 : middleBounds (⟨[2,1,1,3],[4,3]⟩ : MiddleCore) = (middleE3 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore), middleE13 (⟨[4,3],[2,1,1,3]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_015, bound_059]

private theorem bound_061 : (71651513899/200000000000:ℝ) ≤ prefixEval [2] middleBeta ∧ prefixEval [2] middleBeta ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + middleBeta) ∧ 1 / (2 + middleBeta) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (1395643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_062 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2] middleBeta ∧ prefixEval [1,2] middleBeta ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2] middleBeta) ∧ 1 / (1 + prefixEval [2] middleBeta) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_061.1, bound_061.2]
  · norm_num
  · norm_num

private theorem bound_063 : (287979054337/500000000000:ℝ) ≤ prefixEval [1,1,2] middleBeta ∧ prefixEval [1,1,2] middleBeta ≤ (143989527169/250000000000:ℝ) := by
  suffices hh : (287979054337/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2] middleBeta) ∧ 1 / (1 + prefixEval [1,2] middleBeta) ≤ (143989527169/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1736237384173/1000000000000:ℝ) (69449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_062.1, bound_062.2]
  · norm_num
  · norm_num

private theorem bound_064 : (12131408463/31250000000:ℝ) ≤ prefixEval [2,1,1,2] middleBeta ∧ prefixEval [2,1,1,2] middleBeta ≤ (194102535409/500000000000:ℝ) := by
  suffices hh : (12131408463/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2] middleBeta) ≤ (194102535409/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1287979054337/500000000000:ℝ) (643989527169/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_063.1, bound_063.2]
  · norm_num
  · norm_num

private theorem bound_065 : (55217803813/125000000000:ℝ) ≤ prefixEval [2] middleAlpha ∧ prefixEval [2] middleAlpha ≤ (88348486101/200000000000:ℝ) := by
  suffices hh : (55217803813/125000000000:ℝ) ≤ 1 / (2 + middleAlpha) ∧ 1 / (2 + middleAlpha) ≤ (88348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (90550504633/40000000000:ℝ) (1131881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_005.1, bound_005.2]
  · norm_num
  · norm_num

private theorem bound_066 : (346802583749/500000000000:ℝ) ≤ prefixEval [1,2] middleAlpha ∧ prefixEval [1,2] middleAlpha ≤ (693605167499/1000000000000:ℝ) := by
  suffices hh : (346802583749/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2] middleAlpha) ∧ 1 / (1 + prefixEval [2] middleAlpha) ≤ (693605167499/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (180217803813/125000000000:ℝ) (288348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_065.1, bound_065.2]
  · norm_num
  · norm_num

private theorem bound_067 : (590456393963/1000000000000:ℝ) ≤ prefixEval [1,1,2] middleAlpha ∧ prefixEval [1,1,2] middleAlpha ≤ (118091278793/200000000000:ℝ) := by
  suffices hh : (590456393963/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2] middleAlpha) ∧ 1 / (1 + prefixEval [1,2] middleAlpha) ≤ (118091278793/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (846802583749/500000000000:ℝ) (1693605167499/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_066.1, bound_066.2]
  · norm_num
  · norm_num

private theorem bound_068 : (386032361837/1000000000000:ℝ) ≤ prefixEval [2,1,1,2] middleAlpha ∧ prefixEval [2,1,1,2] middleAlpha ≤ (386032361839/1000000000000:ℝ) := by
  suffices hh : (386032361837/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2] middleAlpha) ≤ (386032361839/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2590456393963/1000000000000:ℝ) (518091278793/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_067.1, bound_067.2]
  · norm_num
  · norm_num

private theorem bound_069 : (2172708977/1000000000000:ℝ) ≤ middleWidth [2,1,1,2] ∧ middleWidth [2,1,1,2] ≤ (2172708981/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_064.1, bound_068.2])]
  constructor <;> linarith only [bound_064.1, bound_064.2, bound_068.1, bound_068.2]

private theorem bound_070 : ¬ (middleWidth [4,3] ≤ middleWidth [2,1,1,2]) := by linarith only [bound_013.1, bound_069.2]

private theorem bound_071 : middleNormalized (⟨[2,1,1,2],[4,3]⟩ : MiddleCore) = (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_070, ite_false]

private theorem bound_072 : middleWidth [2,1,1,2] ≤ middleWidth [4,3] := by linarith only [bound_069.2, bound_013.1]

private theorem bound_073 : middleNormalized (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) = (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_072, ite_true]

private theorem bound_074 : (55217803813/125000000000:ℝ) ≤ prefixEval [2,3] middleBeta ∧ prefixEval [2,3] middleBeta ≤ (88348486101/200000000000:ℝ) := by
  suffices hh : (55217803813/125000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleBeta) ∧ 1 / (2 + prefixEval [3] middleBeta) ≤ (88348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (90550504633/40000000000:ℝ) (2263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_075 : (346802583749/500000000000:ℝ) ≤ prefixEval [1,2,3] middleBeta ∧ prefixEval [1,2,3] middleBeta ≤ (693605167499/1000000000000:ℝ) := by
  suffices hh : (346802583749/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleBeta) ∧ 1 / (1 + prefixEval [2,3] middleBeta) ≤ (693605167499/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (180217803813/125000000000:ℝ) (288348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_074.1, bound_074.2]
  · norm_num
  · norm_num

private theorem bound_076 : (590456393963/1000000000000:ℝ) ≤ prefixEval [1,1,2,3] middleBeta ∧ prefixEval [1,1,2,3] middleBeta ≤ (118091278793/200000000000:ℝ) := by
  suffices hh : (590456393963/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,3] middleBeta) ∧ 1 / (1 + prefixEval [1,2,3] middleBeta) ≤ (118091278793/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (846802583749/500000000000:ℝ) (1693605167499/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_075.1, bound_075.2]
  · norm_num
  · norm_num

private theorem bound_077 : (386032361837/1000000000000:ℝ) ≤ prefixEval [2,1,1,2,3] middleBeta ∧ prefixEval [2,1,1,2,3] middleBeta ≤ (386032361839/1000000000000:ℝ) := by
  suffices hh : (386032361837/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,3] middleBeta) ≤ (386032361839/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2590456393963/1000000000000:ℝ) (518091278793/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_076.1, bound_076.2]
  · norm_num
  · norm_num

private theorem bound_078 : (2167885537/5000000000:ℝ) ≤ prefixEval [2,3] middleAlpha ∧ prefixEval [2,3] middleAlpha ≤ (433577107401/1000000000000:ℝ) := by
  suffices hh : (2167885537/5000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleAlpha) ∧ 1 / (2 + prefixEval [3] middleAlpha) ≤ (433577107401/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2306394832501/1000000000000:ℝ) (1153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_079 : (697555781853/1000000000000:ℝ) ≤ prefixEval [1,2,3] middleAlpha ∧ prefixEval [1,2,3] middleAlpha ≤ (348777890927/500000000000:ℝ) := by
  suffices hh : (697555781853/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,3] middleAlpha) ≤ (348777890927/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (7167885537/5000000000:ℝ) (1433577107401/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_078.1, bound_078.2]
  · norm_num
  · norm_num

private theorem bound_080 : (58908226209/100000000000:ℝ) ≤ prefixEval [1,1,2,3] middleAlpha ∧ prefixEval [1,1,2,3] middleAlpha ≤ (147270565523/250000000000:ℝ) := by
  suffices hh : (58908226209/100000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,2,3] middleAlpha) ≤ (147270565523/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1697555781853/1000000000000:ℝ) (848777890927/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_079.1, bound_079.2]
  · norm_num
  · norm_num

private theorem bound_081 : (96559311251/250000000000:ℝ) ≤ prefixEval [2,1,1,2,3] middleAlpha ∧ prefixEval [2,1,1,2,3] middleAlpha ≤ (77247449001/200000000000:ℝ) := by
  suffices hh : (96559311251/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2,3] middleAlpha) ≤ (77247449001/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (258908226209/100000000000:ℝ) (647270565523/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_080.1, bound_080.2]
  · norm_num
  · norm_num

private theorem bound_082 : (40976633/200000000000:ℝ) ≤ middleWidth [2,1,1,2,3] ∧ middleWidth [2,1,1,2,3] ≤ (6402599/31250000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_077.2, bound_081.1])]
  constructor <;> linarith only [bound_077.1, bound_077.2, bound_081.1, bound_081.2]

private theorem bound_083 : middleWidth [4,3,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,2,3] := by linarith only [bound_022.2, bound_082.1]

private theorem bound_084 : (23223396741/100000000000:ℝ) ≤ prefixEval [4,3,3] middleRho ∧ prefixEval [4,3,3] middleRho ≤ (232233967411/1000000000000:ℝ) := by
  suffices hh : (23223396741/100000000000:ℝ) ≤ 1 / (4 + prefixEval [3,3] middleRho) ∧ 1 / (4 + prefixEval [3,3] middleRho) ≤ (232233967411/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2153001154717/500000000000:ℝ) (861200461887/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_033.1, bound_033.2]
  · norm_num
  · norm_num

private theorem bound_085 : (106010472831/250000000000:ℝ) ≤ prefixEval [2,2] middleBeta ∧ prefixEval [2,2] middleBeta ≤ (16961675653/40000000000:ℝ) := by
  suffices hh : (106010472831/250000000000:ℝ) ≤ 1 / (2 + prefixEval [2] middleBeta) ∧ 1 / (2 + prefixEval [2] middleBeta) ≤ (16961675653/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (471651513899/200000000000:ℝ) (294782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_061.1, bound_061.2]
  · norm_num
  · norm_num

private theorem bound_086 : (140445306573/200000000000:ℝ) ≤ prefixEval [1,2,2] middleBeta ∧ prefixEval [1,2,2] middleBeta ≤ (351113266433/500000000000:ℝ) := by
  suffices hh : (140445306573/200000000000:ℝ) ≤ 1 / (1 + prefixEval [2,2] middleBeta) ∧ 1 / (1 + prefixEval [2,2] middleBeta) ≤ (351113266433/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (356010472831/250000000000:ℝ) (56961675653/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_085.1, bound_085.2]
  · norm_num
  · norm_num

private theorem bound_087 : (587465875247/1000000000000:ℝ) ≤ prefixEval [1,1,2,2] middleBeta ∧ prefixEval [1,1,2,2] middleBeta ≤ (587465875249/1000000000000:ℝ) := by
  suffices hh : (587465875247/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,2] middleBeta) ∧ 1 / (1 + prefixEval [1,2,2] middleBeta) ≤ (587465875249/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (340445306573/200000000000:ℝ) (851113266433/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_086.1, bound_086.2]
  · norm_num
  · norm_num

private theorem bound_088 : (7729570539/20000000000:ℝ) ≤ prefixEval [2,1,1,2,2] middleBeta ∧ prefixEval [2,1,1,2,2] middleBeta ≤ (386478526951/1000000000000:ℝ) := by
  suffices hh : (7729570539/20000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,2] middleBeta) ≤ (386478526951/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2587465875247/1000000000000:ℝ) (2587465875249/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_087.1, bound_087.2]
  · norm_num
  · norm_num

private theorem bound_089 : middleE3 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) = 4 + prefixEval [4,3,3] middleRho + prefixEval [2,1,1,2,2] middleBeta := by
  norm_num [middleE3, bound_083]

private theorem bound_090 : (115467812359/25000000000:ℝ) ≤ middleE3 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) ∧ middleE3 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) ≤ (2309356247181/500000000000:ℝ) := by
  rw [bound_089]
  constructor <;> linarith only [bound_084.1, bound_084.2, bound_088.1, bound_088.2]

private theorem bound_091 : (71651513899/200000000000:ℝ) ≤ prefixEval [2,1,3] middleBeta ∧ prefixEval [2,1,3] middleBeta ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,3] middleBeta) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (2791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_092 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2,1,3] middleBeta ∧ prefixEval [1,2,1,3] middleBeta ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [2,1,3] middleBeta) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_091.1, bound_091.2]
  · norm_num
  · norm_num

private theorem bound_093 : (287979054337/500000000000:ℝ) ≤ prefixEval [1,1,2,1,3] middleBeta ∧ prefixEval [1,1,2,1,3] middleBeta ≤ (143989527169/250000000000:ℝ) := by
  suffices hh : (287979054337/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,2,1,3] middleBeta) ≤ (143989527169/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1736237384173/1000000000000:ℝ) (69449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_092.1, bound_092.2]
  · norm_num
  · norm_num

private theorem bound_094 : (12131408463/31250000000:ℝ) ≤ prefixEval [2,1,1,2,1,3] middleBeta ∧ prefixEval [2,1,1,2,1,3] middleBeta ≤ (194102535409/500000000000:ℝ) := by
  suffices hh : (12131408463/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,1,3] middleBeta) ≤ (194102535409/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1287979054337/500000000000:ℝ) (643989527169/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_093.1, bound_093.2]
  · norm_num
  · norm_num

private theorem bound_095 : (180801396377/500000000000:ℝ) ≤ prefixEval [2,1,3] middleAlpha ∧ prefixEval [2,1,3] middleAlpha ≤ (90400698189/250000000000:ℝ) := by
  suffices hh : (180801396377/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,3] middleAlpha) ≤ (90400698189/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (276546536707/100000000000:ℝ) (2765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_007.1, bound_007.2]
  · norm_num
  · norm_num

private theorem bound_096 : (734428575881/1000000000000:ℝ) ≤ prefixEval [1,2,1,3] middleAlpha ∧ prefixEval [1,2,1,3] middleAlpha ≤ (734428575883/1000000000000:ℝ) := by
  suffices hh : (734428575881/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,1,3] middleAlpha) ≤ (734428575883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (680801396377/500000000000:ℝ) (340400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_095.1, bound_095.2]
  · norm_num
  · norm_num

private theorem bound_097 : (57655876633/100000000000:ℝ) ≤ prefixEval [1,1,2,1,3] middleAlpha ∧ prefixEval [1,1,2,1,3] middleAlpha ≤ (144139691583/250000000000:ℝ) := by
  suffices hh : (57655876633/100000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,2,1,3] middleAlpha) ≤ (144139691583/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1734428575881/1000000000000:ℝ) (1734428575883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_096.1, bound_096.2]
  · norm_num
  · norm_num

private theorem bound_098 : (194057285451/500000000000:ℝ) ≤ prefixEval [2,1,1,2,1,3] middleAlpha ∧ prefixEval [2,1,1,2,1,3] middleAlpha ≤ (388114570903/1000000000000:ℝ) := by
  suffices hh : (194057285451/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2,1,3] middleAlpha) ≤ (388114570903/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (257655876633/100000000000:ℝ) (644139691583/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_097.1, bound_097.2]
  · norm_num
  · norm_num

private theorem bound_099 : (90499913/1000000000000:ℝ) ≤ middleWidth [2,1,1,2,1,3] ∧ middleWidth [2,1,1,2,1,3] ≤ (22624979/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_094.1, bound_098.2])]
  constructor <;> linarith only [bound_094.1, bound_094.2, bound_098.1, bound_098.2]

private theorem bound_100 : middleWidth [4,3,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,2,1,3] := by linarith only [bound_043.2, bound_099.1]

private theorem bound_101 : (234524628023/1000000000000:ℝ) ≤ prefixEval [4,3,1,3] middleRho ∧ prefixEval [4,3,1,3] middleRho ≤ (29315578503/125000000000:ℝ) := by
  suffices hh : (234524628023/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,3] middleRho) ∧ 1 / (4 + prefixEval [3,1,3] middleRho) ≤ (29315578503/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (852788901897/200000000000:ℝ) (2131972254743/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_053.1, bound_053.2]
  · norm_num
  · norm_num

private theorem bound_102 : (36546536707/100000000000:ℝ) ≤ prefixEval [2,1,2] middleBeta ∧ prefixEval [2,1,2] middleBeta ≤ (365465367071/1000000000000:ℝ) := by
  suffices hh : (36546536707/100000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,2] middleBeta) ≤ (365465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2736237384173/1000000000000:ℝ) (109449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_062.1, bound_062.2]
  · norm_num
  · norm_num

private theorem bound_103 : (91543881679/125000000000:ℝ) ≤ prefixEval [1,2,1,2] middleBeta ∧ prefixEval [1,2,1,2] middleBeta ≤ (366175526717/500000000000:ℝ) := by
  suffices hh : (91543881679/125000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,2] middleBeta) ∧ 1 / (1 + prefixEval [2,1,2] middleBeta) ≤ (366175526717/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (136546536707/100000000000:ℝ) (1365465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_102.1, bound_102.2]
  · norm_num
  · norm_num

private theorem bound_104 : (28862510229/50000000000:ℝ) ≤ prefixEval [1,1,2,1,2] middleBeta ∧ prefixEval [1,1,2,1,2] middleBeta ≤ (288625102291/500000000000:ℝ) := by
  suffices hh : (28862510229/50000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,2] middleBeta) ∧ 1 / (1 + prefixEval [1,2,1,2] middleBeta) ≤ (288625102291/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (216543881679/125000000000:ℝ) (866175526717/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_103.1, bound_103.2]
  · norm_num
  · norm_num

private theorem bound_105 : (194005222741/500000000000:ℝ) ≤ prefixEval [2,1,1,2,1,2] middleBeta ∧ prefixEval [2,1,1,2,1,2] middleBeta ≤ (388010445483/1000000000000:ℝ) := by
  suffices hh : (194005222741/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,1,2] middleBeta) ≤ (388010445483/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (128862510229/50000000000:ℝ) (1288625102291/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_104.1, bound_104.2]
  · norm_num
  · norm_num

private theorem bound_106 : middleE13 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) = 4 + prefixEval [4,3,1,3] middleRho + prefixEval [2,1,1,2,1,2] middleBeta := by
  norm_num [middleE13, bound_100]

private theorem bound_107 : (924507014701/200000000000:ℝ) ≤ middleE13 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) ∧ middleE13 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) ≤ (4622535073507/1000000000000:ℝ) := by
  rw [bound_106]
  constructor <;> linarith only [bound_101.1, bound_101.2, bound_105.1, bound_105.2]

private theorem bound_108 : middleEqualBounds (⟨[4,3],[2,1,1,2]⟩ : MiddleCore) = (middleE3 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore), middleE13 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_073]

private theorem bound_109 : middleBounds (⟨[2,1,1,2],[4,3]⟩ : MiddleCore) = (middleE3 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore), middleE13 (⟨[4,3],[2,1,1,2]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_071, bound_108]

private theorem bound_110 : (111651513899/200000000000:ℝ) ≤ prefixEval [1] middleBeta ∧ prefixEval [1] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + middleBeta) ∧ 1 / (1 + middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (895643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_111 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1] middleBeta ∧ prefixEval [1,1] middleBeta ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1] middleBeta) ∧ 1 / (1 + prefixEval [1] middleBeta) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_110.1, bound_110.2]
  · norm_num
  · norm_num

private theorem bound_112 : (274593829487/1000000000000:ℝ) ≤ prefixEval [3,1,1] middleBeta ∧ prefixEval [3,1,1] middleBeta ≤ (17162114343/62500000000:ℝ) := by
  suffices hh : (274593829487/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1] middleBeta) ∧ 1 / (3 + prefixEval [1,1] middleBeta) ≤ (17162114343/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (455217803813/125000000000:ℝ) (728348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_111.1, bound_111.2]
  · norm_num
  · norm_num

private theorem bound_113 : (12258807189/15625000000:ℝ) ≤ prefixEval [1,3,1,1] middleBeta ∧ prefixEval [1,3,1,1] middleBeta ≤ (392281830049/500000000000:ℝ) := by
  suffices hh : (12258807189/15625000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1] middleBeta) ∧ 1 / (1 + prefixEval [3,1,1] middleBeta) ≤ (392281830049/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1274593829487/1000000000000:ℝ) (79662114343/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_112.1, bound_112.2]
  · norm_num
  · norm_num

private theorem bound_114 : (35022566803/62500000000:ℝ) ≤ prefixEval [1,1,3,1,1] middleBeta ∧ prefixEval [1,1,3,1,1] middleBeta ≤ (560361068849/1000000000000:ℝ) := by
  suffices hh : (35022566803/62500000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1] middleBeta) ∧ 1 / (1 + prefixEval [1,3,1,1] middleBeta) ≤ (560361068849/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (27883807189/15625000000:ℝ) (892281830049/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_113.1, bound_113.2]
  · norm_num
  · norm_num

private theorem bound_115 : (78113982607/200000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1] middleBeta ∧ prefixEval [2,1,1,3,1,1] middleBeta ≤ (97642478259/250000000000:ℝ) := by
  suffices hh : (78113982607/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,1,1] middleBeta) ≤ (97642478259/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (160022566803/62500000000:ℝ) (2560361068849/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_114.1, bound_114.2]
  · norm_num
  · norm_num

private theorem bound_116 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1] middleAlpha ∧ prefixEval [1] middleAlpha ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + middleAlpha) ∧ 1 / (1 + middleAlpha) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (631881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_005.1, bound_005.2]
  · norm_num
  · norm_num

private theorem bound_117 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1] middleAlpha ∧ prefixEval [1,1] middleAlpha ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1] middleAlpha) ∧ 1 / (1 + prefixEval [1] middleAlpha) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_116.1, bound_116.2]
  · norm_num
  · norm_num

private theorem bound_118 : (281036428777/1000000000000:ℝ) ≤ prefixEval [3,1,1] middleAlpha ∧ prefixEval [3,1,1] middleAlpha ≤ (140518214389/500000000000:ℝ) := by
  suffices hh : (281036428777/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1] middleAlpha) ∧ 1 / (3 + prefixEval [1,1] middleAlpha) ≤ (140518214389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (711651513899/200000000000:ℝ) (444782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_117.1, bound_117.2]
  · norm_num
  · norm_num

private theorem bound_119 : (48788620367/62500000000:ℝ) ≤ prefixEval [1,3,1,1] middleAlpha ∧ prefixEval [1,3,1,1] middleAlpha ≤ (390308962937/500000000000:ℝ) := by
  suffices hh : (48788620367/62500000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1] middleAlpha) ∧ 1 / (1 + prefixEval [3,1,1] middleAlpha) ≤ (390308962937/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1281036428777/1000000000000:ℝ) (640518214389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_118.1, bound_118.2]
  · norm_num
  · norm_num

private theorem bound_120 : (280801396377/500000000000:ℝ) ≤ prefixEval [1,1,3,1,1] middleAlpha ∧ prefixEval [1,1,3,1,1] middleAlpha ≤ (140400698189/250000000000:ℝ) := by
  suffices hh : (280801396377/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,1,1] middleAlpha) ≤ (140400698189/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (111288620367/62500000000:ℝ) (890308962937/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_119.1, bound_119.2]
  · norm_num
  · norm_num

private theorem bound_121 : (390380586259/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1] middleAlpha ∧ prefixEval [2,1,1,3,1,1] middleAlpha ≤ (19519029313/50000000000:ℝ) := by
  suffices hh : (390380586259/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,1,1] middleAlpha) ≤ (19519029313/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1280801396377/500000000000:ℝ) (640400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_120.1, bound_120.2]
  · norm_num
  · norm_num

private theorem bound_122 : (7573071/40000000000:ℝ) ≤ middleWidth [2,1,1,3,1,1] ∧ middleWidth [2,1,1,3,1,1] ≤ (189326777/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_115.1, bound_121.2])]
  constructor <;> linarith only [bound_115.1, bound_115.2, bound_121.1, bound_121.2]

private theorem bound_123 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1] middleBeta ∧ prefixEval [1,1,1] middleBeta ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1] middleBeta) ∧ 1 / (1 + prefixEval [1,1] middleBeta) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_111.1, bound_111.2]
  · norm_num
  · norm_num

private theorem bound_124 : (383272611851/1000000000000:ℝ) ≤ prefixEval [2,1,1,1] middleBeta ∧ prefixEval [2,1,1,1] middleBeta ≤ (95818152963/250000000000:ℝ) := by
  suffices hh : (383272611851/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1] middleBeta) ≤ (95818152963/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2609108945117/1000000000000:ℝ) (2609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_123.1, bound_123.2]
  · norm_num
  · norm_num

private theorem bound_125 : (228140042509/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,1] middleBeta ∧ prefixEval [4,2,1,1,1] middleBeta ≤ (22814004251/100000000000:ℝ) := by
  suffices hh : (228140042509/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,1] middleBeta) ≤ (22814004251/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4383272611851/1000000000000:ℝ) (1095818152963/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_124.1, bound_124.2]
  · norm_num
  · norm_num

private theorem bound_126 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1,1] middleAlpha ∧ prefixEval [1,1,1] middleAlpha ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,1] middleAlpha) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_117.1, bound_117.2]
  · norm_num
  · norm_num

private theorem bound_127 : (378538039307/1000000000000:ℝ) ≤ prefixEval [2,1,1,1] middleAlpha ∧ prefixEval [2,1,1,1] middleAlpha ≤ (378538039309/1000000000000:ℝ) := by
  suffices hh : (378538039307/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1] middleAlpha) ≤ (378538039309/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (330217803813/125000000000:ℝ) (528348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_126.1, bound_126.2]
  · norm_num
  · norm_num

private theorem bound_128 : (22838673343/100000000000:ℝ) ≤ prefixEval [4,2,1,1,1] middleAlpha ∧ prefixEval [4,2,1,1,1] middleAlpha ≤ (228386733431/1000000000000:ℝ) := by
  suffices hh : (22838673343/100000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,1] middleAlpha) ≤ (228386733431/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4378538039307/1000000000000:ℝ) (4378538039309/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_127.1, bound_127.2]
  · norm_num
  · norm_num

private theorem bound_129 : (6167273/25000000000:ℝ) ≤ middleWidth [4,2,1,1,1] ∧ middleWidth [4,2,1,1,1] ≤ (123345461/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_125.2, bound_128.1])]
  constructor <;> linarith only [bound_125.1, bound_125.2, bound_128.1, bound_128.2]

private theorem bound_130 : ¬ (middleWidth [4,2,1,1,1] ≤ middleWidth [2,1,1,3,1,1]) := by linarith only [bound_129.1, bound_122.2]

private theorem bound_131 : middleNormalized (⟨[2,1,1,3,1,1],[4,2,1,1,1]⟩ : MiddleCore) = (⟨[4,2,1,1,1],[2,1,1,3,1,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_130, ite_false]

private theorem bound_132 : (138538350491/500000000000:ℝ) ≤ prefixEval [3,1,1,1] middleBeta ∧ prefixEval [3,1,1,1] middleBeta ≤ (277076700983/1000000000000:ℝ) := by
  suffices hh : (138538350491/500000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1] middleBeta) ∧ 1 / (3 + prefixEval [1,1,1] middleBeta) ≤ (277076700983/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3609108945117/1000000000000:ℝ) (3609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_123.1, bound_123.2]
  · norm_num
  · norm_num

private theorem bound_133 : (391519162173/500000000000:ℝ) ≤ prefixEval [1,3,1,1,1] middleBeta ∧ prefixEval [1,3,1,1,1] middleBeta ≤ (195759581087/250000000000:ℝ) := by
  suffices hh : (391519162173/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1] middleBeta) ∧ 1 / (1 + prefixEval [3,1,1,1] middleBeta) ≤ (195759581087/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (638538350491/500000000000:ℝ) (1277076700983/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_132.1, bound_132.2]
  · norm_num
  · norm_num

private theorem bound_134 : (560840440917/1000000000000:ℝ) ≤ prefixEval [1,1,3,1,1,1] middleBeta ∧ prefixEval [1,1,3,1,1,1] middleBeta ≤ (560840440919/1000000000000:ℝ) := by
  suffices hh : (560840440917/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1] middleBeta) ∧ 1 / (1 + prefixEval [1,3,1,1,1] middleBeta) ≤ (560840440919/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (891519162173/500000000000:ℝ) (445759581087/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_133.1, bound_133.2]
  · norm_num
  · norm_num

private theorem bound_135 : (19524840049/50000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1] middleBeta ∧ prefixEval [2,1,1,3,1,1,1] middleBeta ≤ (390496800981/1000000000000:ℝ) := by
  suffices hh : (19524840049/50000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1] middleBeta) ≤ (390496800981/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2560840440917/1000000000000:ℝ) (2560840440919/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_134.1, bound_134.2]
  · norm_num
  · norm_num

private theorem bound_136 : (274593829487/1000000000000:ℝ) ≤ prefixEval [3,1,1,1] middleAlpha ∧ prefixEval [3,1,1,1] middleAlpha ≤ (17162114343/62500000000:ℝ) := by
  suffices hh : (274593829487/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1] middleAlpha) ∧ 1 / (3 + prefixEval [1,1,1] middleAlpha) ≤ (17162114343/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (455217803813/125000000000:ℝ) (728348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_126.1, bound_126.2]
  · norm_num
  · norm_num

private theorem bound_137 : (12258807189/15625000000:ℝ) ≤ prefixEval [1,3,1,1,1] middleAlpha ∧ prefixEval [1,3,1,1,1] middleAlpha ≤ (392281830049/500000000000:ℝ) := by
  suffices hh : (12258807189/15625000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1] middleAlpha) ∧ 1 / (1 + prefixEval [3,1,1,1] middleAlpha) ≤ (392281830049/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1274593829487/1000000000000:ℝ) (79662114343/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_136.1, bound_136.2]
  · norm_num
  · norm_num

private theorem bound_138 : (35022566803/62500000000:ℝ) ≤ prefixEval [1,1,3,1,1,1] middleAlpha ∧ prefixEval [1,1,3,1,1,1] middleAlpha ≤ (560361068849/1000000000000:ℝ) := by
  suffices hh : (35022566803/62500000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,1,1,1] middleAlpha) ≤ (560361068849/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (27883807189/15625000000:ℝ) (892281830049/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_137.1, bound_137.2]
  · norm_num
  · norm_num

private theorem bound_139 : (78113982607/200000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1] middleAlpha ∧ prefixEval [2,1,1,3,1,1,1] middleAlpha ≤ (97642478259/250000000000:ℝ) := by
  suffices hh : (78113982607/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1] middleAlpha) ≤ (97642478259/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (160022566803/62500000000:ℝ) (2560361068849/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_138.1, bound_138.2]
  · norm_num
  · norm_num

private theorem bound_140 : (36556027/500000000000:ℝ) ≤ middleWidth [2,1,1,3,1,1,1] ∧ middleWidth [2,1,1,3,1,1,1] ≤ (9139007/125000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_135.2, bound_139.1])]
  constructor <;> linarith only [bound_135.1, bound_135.2, bound_139.1, bound_139.2]

private theorem bound_141 : middleWidth [2,1,1,3,1,1,1] ≤ middleWidth [4,2,1,1,1] := by linarith only [bound_140.2, bound_129.1]

private theorem bound_142 : middleNormalized (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) = (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_141, ite_true]

private theorem bound_143 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1,1,3] middleBeta ∧ prefixEval [1,1,1,3] middleBeta ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,3] middleBeta) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_144 : (378538039307/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,1,3] middleBeta ≤ (378538039309/1000000000000:ℝ) := by
  suffices hh : (378538039307/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1,3] middleBeta) ≤ (378538039309/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (330217803813/125000000000:ℝ) (528348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_143.1, bound_143.2]
  · norm_num
  · norm_num

private theorem bound_145 : (22838673343/100000000000:ℝ) ≤ prefixEval [4,2,1,1,1,3] middleBeta ∧ prefixEval [4,2,1,1,1,3] middleBeta ≤ (228386733431/1000000000000:ℝ) := by
  suffices hh : (22838673343/100000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,1,3] middleBeta) ≤ (228386733431/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4378538039307/1000000000000:ℝ) (4378538039309/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_144.1, bound_144.2]
  · norm_num
  · norm_num

private theorem bound_146 : (159599301811/250000000000:ℝ) ≤ prefixEval [1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,3] middleAlpha ≤ (319198603623/500000000000:ℝ) := by
  suffices hh : (159599301811/250000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,3] middleAlpha) ≤ (319198603623/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1566422892599/1000000000000:ℝ) (7832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_008.1, bound_008.2]
  · norm_num
  · norm_num

private theorem bound_147 : (379017987607/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,1,3] middleAlpha ≤ (47377248451/125000000000:ℝ) := by
  suffices hh : (379017987607/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1,3] middleAlpha) ≤ (47377248451/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (659599301811/250000000000:ℝ) (1319198603623/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_146.1, bound_146.2]
  · norm_num
  · norm_num

private theorem bound_148 : (228361701831/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,1,3] middleAlpha ∧ prefixEval [4,2,1,1,1,3] middleAlpha ≤ (28545212729/125000000000:ℝ) := by
  suffices hh : (228361701831/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,1,3] middleAlpha) ≤ (28545212729/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4379017987607/1000000000000:ℝ) (547377248451/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_147.1, bound_147.2]
  · norm_num
  · norm_num

private theorem bound_149 : (12515799/500000000000:ℝ) ≤ middleWidth [4,2,1,1,1,3] ∧ middleWidth [4,2,1,1,1,3] ≤ (62579/2500000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_145.1, bound_148.2])]
  constructor <;> linarith only [bound_145.1, bound_145.2, bound_148.1, bound_148.2]

private theorem bound_150 : (274593829487/1000000000000:ℝ) ≤ prefixEval [3,1,1,1,3] middleBeta ∧ prefixEval [3,1,1,1,3] middleBeta ≤ (17162114343/62500000000:ℝ) := by
  suffices hh : (274593829487/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,1,1,3] middleBeta) ≤ (17162114343/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (455217803813/125000000000:ℝ) (728348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_143.1, bound_143.2]
  · norm_num
  · norm_num

private theorem bound_151 : (12258807189/15625000000:ℝ) ≤ prefixEval [1,3,1,1,1,3] middleBeta ∧ prefixEval [1,3,1,1,1,3] middleBeta ≤ (392281830049/500000000000:ℝ) := by
  suffices hh : (12258807189/15625000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [3,1,1,1,3] middleBeta) ≤ (392281830049/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1274593829487/1000000000000:ℝ) (79662114343/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_150.1, bound_150.2]
  · norm_num
  · norm_num

private theorem bound_152 : (35022566803/62500000000:ℝ) ≤ prefixEval [1,1,3,1,1,1,3] middleBeta ∧ prefixEval [1,1,3,1,1,1,3] middleBeta ≤ (560361068849/1000000000000:ℝ) := by
  suffices hh : (35022566803/62500000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,1,1,1,3] middleBeta) ≤ (560361068849/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (27883807189/15625000000:ℝ) (892281830049/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_151.1, bound_151.2]
  · norm_num
  · norm_num

private theorem bound_153 : (78113982607/200000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,3,1,1,1,3] middleBeta ≤ (97642478259/250000000000:ℝ) := by
  suffices hh : (78113982607/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1,3] middleBeta) ≤ (97642478259/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (160022566803/62500000000:ℝ) (2560361068849/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_152.1, bound_152.2]
  · norm_num
  · norm_num

private theorem bound_154 : (274846297157/1000000000000:ℝ) ≤ prefixEval [3,1,1,1,3] middleAlpha ∧ prefixEval [3,1,1,1,3] middleAlpha ≤ (137423148579/500000000000:ℝ) := by
  suffices hh : (274846297157/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,1,1,3] middleAlpha) ≤ (137423148579/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (909599301811/250000000000:ℝ) (1819198603623/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_146.1, bound_146.2]
  · norm_num
  · norm_num

private theorem bound_155 : (98051035861/125000000000:ℝ) ≤ prefixEval [1,3,1,1,1,3] middleAlpha ∧ prefixEval [1,3,1,1,1,3] middleAlpha ≤ (78440828689/100000000000:ℝ) := by
  suffices hh : (98051035861/125000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,1,1,1,3] middleAlpha) ≤ (78440828689/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1274846297157/1000000000000:ℝ) (637423148579/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_154.1, bound_154.2]
  · norm_num
  · norm_num

private theorem bound_156 : (280204930493/500000000000:ℝ) ≤ prefixEval [1,1,3,1,1,1,3] middleAlpha ∧ prefixEval [1,1,3,1,1,1,3] middleAlpha ≤ (140102465247/250000000000:ℝ) := by
  suffices hh : (280204930493/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,1,1,1,3] middleAlpha) ≤ (140102465247/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (223051035861/125000000000:ℝ) (178440828689/100000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_155.1, bound_155.2]
  · norm_num
  · norm_num

private theorem bound_157 : (390562470187/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,3,1,1,1,3] middleAlpha ≤ (97640617547/250000000000:ℝ) := by
  suffices hh : (390562470187/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1,3] middleAlpha) ≤ (97640617547/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1280204930493/500000000000:ℝ) (640102465247/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_156.1, bound_156.2]
  · norm_num
  · norm_num

private theorem bound_158 : (7442847/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,1,1,1,3] ∧ middleWidth [2,1,1,3,1,1,1,3] ≤ (7442849/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_153.1, bound_157.2])]
  constructor <;> linarith only [bound_153.1, bound_153.2, bound_157.1, bound_157.2]

private theorem bound_159 : ¬ (middleWidth [4,2,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,1,1,1,3]) := by linarith only [bound_149.1, bound_158.2]

private theorem bound_160 : (279536507401/500000000000:ℝ) ≤ prefixEval [1,1,3] middleRho ∧ prefixEval [1,1,3] middleRho ≤ (559073014803/1000000000000:ℝ) := by
  suffices hh : (279536507401/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleRho) ∧ 1 / (1 + prefixEval [1,3] middleRho) ≤ (559073014803/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (894337567297/500000000000:ℝ) (357735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_052.1, bound_052.2]
  · norm_num
  · norm_num

private theorem bound_161 : (320703389291/500000000000:ℝ) ≤ prefixEval [1,1,1,3] middleRho ∧ prefixEval [1,1,1,3] middleRho ≤ (80175847323/125000000000:ℝ) := by
  suffices hh : (320703389291/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,1,3] middleRho) ≤ (80175847323/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (779536507401/500000000000:ℝ) (1559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_160.1, bound_160.2]
  · norm_num
  · norm_num

private theorem bound_162 : (274619140569/1000000000000:ℝ) ≤ prefixEval [3,1,1,1,3] middleRho ∧ prefixEval [3,1,1,1,3] middleRho ≤ (274619140571/1000000000000:ℝ) := by
  suffices hh : (274619140569/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1,3] middleRho) ∧ 1 / (3 + prefixEval [1,1,1,3] middleRho) ≤ (274619140571/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1820703389291/500000000000:ℝ) (455175847323/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_161.1, bound_161.2]
  · norm_num
  · norm_num

private theorem bound_163 : (392274040209/500000000000:ℝ) ≤ prefixEval [1,3,1,1,1,3] middleRho ∧ prefixEval [1,3,1,1,1,3] middleRho ≤ (784548080421/1000000000000:ℝ) := by
  suffices hh : (392274040209/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [3,1,1,1,3] middleRho) ≤ (784548080421/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1274619140569/1000000000000:ℝ) (1274619140571/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_162.1, bound_162.2]
  · norm_num
  · norm_num

private theorem bound_164 : (560365960979/1000000000000:ℝ) ≤ prefixEval [1,1,3,1,1,1,3] middleRho ∧ prefixEval [1,1,3,1,1,1,3] middleRho ≤ (560365960981/1000000000000:ℝ) := by
  suffices hh : (560365960979/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,3,1,1,1,3] middleRho) ≤ (560365960981/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (892274040209/500000000000:ℝ) (1784548080421/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_163.1, bound_163.2]
  · norm_num
  · norm_num

private theorem bound_165 : (390569166767/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1,3] middleRho ∧ prefixEval [2,1,1,3,1,1,1,3] middleRho ≤ (24410572923/62500000000:ℝ) := by
  suffices hh : (390569166767/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1,3] middleRho) ≤ (24410572923/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2560365960979/1000000000000:ℝ) (2560365960981/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_164.1, bound_164.2]
  · norm_num
  · norm_num

private theorem bound_166 : middleE3 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) = 4 + prefixEval [4,2,1,1,1] middleAlpha + prefixEval [2,1,1,3,1,1,1,3] middleRho := by
  norm_num [middleE3, bound_159]

private theorem bound_167 : (4618955900197/1000000000000:ℝ) ≤ middleE3 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) ∧ middleE3 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) ≤ (4618955900199/1000000000000:ℝ) := by
  rw [bound_166]
  constructor <;> linarith only [bound_128.1, bound_128.2, bound_165.1, bound_165.2]

private theorem bound_168 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleBeta ∧ prefixEval [1,1,1,1,3] middleBeta ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,1,3] middleBeta) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_143.1, bound_143.2]
  · norm_num
  · norm_num

private theorem bound_169 : (383272611851/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,1,1,3] middleBeta ≤ (95818152963/250000000000:ℝ) := by
  suffices hh : (383272611851/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1,1,3] middleBeta) ≤ (95818152963/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2609108945117/1000000000000:ℝ) (2609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_168.1, bound_168.2]
  · norm_num
  · norm_num

private theorem bound_170 : (228140042509/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1,3] middleBeta ∧ prefixEval [4,2,1,1,1,1,3] middleBeta ≤ (22814004251/100000000000:ℝ) := by
  suffices hh : (228140042509/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,1,1,3] middleBeta) ≤ (22814004251/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4383272611851/1000000000000:ℝ) (1095818152963/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_169.1, bound_169.2]
  · norm_num
  · norm_num

private theorem bound_171 : (610352602883/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,1,3] middleAlpha ≤ (122070520577/200000000000:ℝ) := by
  suffices hh : (610352602883/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,1,3] middleAlpha) ≤ (122070520577/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (409599301811/250000000000:ℝ) (819198603623/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_146.1, bound_146.2]
  · norm_num
  · norm_num

private theorem bound_172 : (383090008183/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,1,1,3] middleAlpha ≤ (47886251023/125000000000:ℝ) := by
  suffices hh : (383090008183/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1,1,3] middleAlpha) ≤ (47886251023/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2610352602883/1000000000000:ℝ) (522070520577/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_171.1, bound_171.2]
  · norm_num
  · norm_num

private theorem bound_173 : (228149547039/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1,3] middleAlpha ∧ prefixEval [4,2,1,1,1,1,3] middleAlpha ≤ (1425934669/6250000000:ℝ) := by
  suffices hh : (228149547039/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,1,1,3] middleAlpha) ≤ (1425934669/6250000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4383090008183/1000000000000:ℝ) (547886251023/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_172.1, bound_172.2]
  · norm_num
  · norm_num

private theorem bound_174 : (9504529/1000000000000:ℝ) ≤ middleWidth [4,2,1,1,1,1,3] ∧ middleWidth [4,2,1,1,1,1,3] ≤ (9504531/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_170.2, bound_173.1])]
  constructor <;> linarith only [bound_170.1, bound_170.2, bound_173.1, bound_173.2]

private theorem bound_175 : (138538350491/500000000000:ℝ) ≤ prefixEval [3,1,1,1,1,3] middleBeta ∧ prefixEval [3,1,1,1,1,3] middleBeta ≤ (277076700983/1000000000000:ℝ) := by
  suffices hh : (138538350491/500000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1,1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,1,1,1,3] middleBeta) ≤ (277076700983/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3609108945117/1000000000000:ℝ) (3609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_168.1, bound_168.2]
  · norm_num
  · norm_num

private theorem bound_176 : (391519162173/500000000000:ℝ) ≤ prefixEval [1,3,1,1,1,1,3] middleBeta ∧ prefixEval [1,3,1,1,1,1,3] middleBeta ≤ (195759581087/250000000000:ℝ) := by
  suffices hh : (391519162173/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [3,1,1,1,1,3] middleBeta) ≤ (195759581087/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (638538350491/500000000000:ℝ) (1277076700983/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_175.1, bound_175.2]
  · norm_num
  · norm_num

private theorem bound_177 : (560840440917/1000000000000:ℝ) ≤ prefixEval [1,1,3,1,1,1,1,3] middleBeta ∧ prefixEval [1,1,3,1,1,1,1,3] middleBeta ≤ (560840440919/1000000000000:ℝ) := by
  suffices hh : (560840440917/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,1,1,1,1,3] middleBeta) ≤ (560840440919/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (891519162173/500000000000:ℝ) (445759581087/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_176.1, bound_176.2]
  · norm_num
  · norm_num

private theorem bound_178 : (19524840049/50000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,3,1,1,1,1,3] middleBeta ≤ (390496800981/1000000000000:ℝ) := by
  suffices hh : (19524840049/50000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1,1,3] middleBeta) ≤ (390496800981/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2560840440917/1000000000000:ℝ) (2560840440919/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_177.1, bound_177.2]
  · norm_num
  · norm_num

private theorem bound_179 : (276981256401/1000000000000:ℝ) ≤ prefixEval [3,1,1,1,1,3] middleAlpha ∧ prefixEval [3,1,1,1,1,3] middleAlpha ≤ (138490628201/500000000000:ℝ) := by
  suffices hh : (276981256401/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,1,1,1,3] middleAlpha) ≤ (138490628201/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3610352602883/1000000000000:ℝ) (722070520577/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_171.1, bound_171.2]
  · norm_num
  · norm_num

private theorem bound_180 : (783096850471/1000000000000:ℝ) ≤ prefixEval [1,3,1,1,1,1,3] middleAlpha ∧ prefixEval [1,3,1,1,1,1,3] middleAlpha ≤ (783096850473/1000000000000:ℝ) := by
  suffices hh : (783096850471/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,1,1,1,1,3] middleAlpha) ≤ (783096850473/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1276981256401/1000000000000:ℝ) (638490628201/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_179.1, bound_179.2]
  · norm_num
  · norm_num

private theorem bound_181 : (560822032597/1000000000000:ℝ) ≤ prefixEval [1,1,3,1,1,1,1,3] middleAlpha ∧ prefixEval [1,1,3,1,1,1,1,3] middleAlpha ≤ (280411016299/500000000000:ℝ) := by
  suffices hh : (560822032597/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,1,1,1,1,3] middleAlpha) ≤ (280411016299/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1783096850471/1000000000000:ℝ) (1783096850473/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_180.1, bound_180.2]
  · norm_num
  · norm_num

private theorem bound_182 : (97624902011/250000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,3,1,1,1,1,3] middleAlpha ≤ (78099921609/200000000000:ℝ) := by
  suffices hh : (97624902011/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1,1,3] middleAlpha) ≤ (78099921609/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2560822032597/1000000000000:ℝ) (1280411016299/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_181.1, bound_181.2]
  · norm_num
  · norm_num

private theorem bound_183 : (2807063/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,1,1,1,1,3] ∧ middleWidth [2,1,1,3,1,1,1,1,3] ≤ (561413/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_178.2, bound_182.1])]
  constructor <;> linarith only [bound_178.1, bound_178.2, bound_182.1, bound_182.2]

private theorem bound_184 : ¬ (middleWidth [4,2,1,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,1,1,1,1,3]) := by linarith only [bound_174.1, bound_183.2]

private theorem bound_185 : (304616751023/500000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleRho ∧ prefixEval [1,1,1,1,3] middleRho ≤ (19038546939/31250000000:ℝ) := by
  suffices hh : (304616751023/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,1,1,3] middleRho) ≤ (19038546939/31250000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (820703389291/500000000000:ℝ) (205175847323/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_161.1, bound_161.2]
  · norm_num
  · norm_num

private theorem bound_186 : (27706713889/100000000000:ℝ) ≤ prefixEval [3,1,1,1,1,3] middleRho ∧ prefixEval [3,1,1,1,1,3] middleRho ≤ (277067138891/1000000000000:ℝ) := by
  suffices hh : (27706713889/100000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,1,1,3] middleRho) ∧ 1 / (3 + prefixEval [1,1,1,1,3] middleRho) ≤ (277067138891/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1804616751023/500000000000:ℝ) (112788546939/31250000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_185.1, bound_185.2]
  · norm_num
  · norm_num

private theorem bound_187 : (783044187377/1000000000000:ℝ) ≤ prefixEval [1,3,1,1,1,1,3] middleRho ∧ prefixEval [1,3,1,1,1,1,3] middleRho ≤ (783044187379/1000000000000:ℝ) := by
  suffices hh : (783044187377/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [3,1,1,1,1,3] middleRho) ≤ (783044187379/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (127706713889/100000000000:ℝ) (1277067138891/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_186.1, bound_186.2]
  · norm_num
  · norm_num

private theorem bound_188 : (560838596753/1000000000000:ℝ) ≤ prefixEval [1,1,3,1,1,1,1,3] middleRho ∧ prefixEval [1,1,3,1,1,1,1,3] middleRho ≤ (112167719351/200000000000:ℝ) := by
  suffices hh : (560838596753/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,3,1,1,1,1,3] middleRho) ≤ (112167719351/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1783044187377/1000000000000:ℝ) (1783044187379/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_187.1, bound_187.2]
  · norm_num
  · norm_num

private theorem bound_189 : (24406067637/62500000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,1,1,3] middleRho ∧ prefixEval [2,1,1,3,1,1,1,1,3] middleRho ≤ (195248541097/500000000000:ℝ) := by
  suffices hh : (24406067637/62500000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3,1,1,1,1,3] middleRho) ≤ (195248541097/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2560838596753/1000000000000:ℝ) (512167719351/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_188.1, bound_188.2]
  · norm_num
  · norm_num

private theorem bound_190 : middleE13 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) = 4 + prefixEval [4,2,1,1,1] middleBeta + prefixEval [2,1,1,3,1,1,1,1,3] middleRho := by
  norm_num [middleE13, bound_184]

private theorem bound_191 : (4618637124701/1000000000000:ℝ) ≤ middleE13 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) ∧ middleE13 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) ≤ (144332410147/31250000000:ℝ) := by
  rw [bound_190]
  constructor <;> linarith only [bound_125.1, bound_125.2, bound_189.1, bound_189.2]

private theorem bound_192 : middleEqualBounds (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore) = (middleE13 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore), middleE3 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_142]

private theorem bound_193 : (621461960691/1000000000000:ℝ) ≤ prefixEval [1,1,1,1] middleBeta ∧ prefixEval [1,1,1,1] middleBeta ≤ (621461960693/1000000000000:ℝ) := by
  suffices hh : (621461960691/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1] middleBeta) ∧ 1 / (1 + prefixEval [1,1,1] middleBeta) ≤ (621461960693/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1609108945117/1000000000000:ℝ) (1609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_123.1, bound_123.2]
  · norm_num
  · norm_num

private theorem bound_194 : (381466530887/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1] middleBeta ∧ prefixEval [2,1,1,1,1] middleBeta ≤ (381466530889/1000000000000:ℝ) := by
  suffices hh : (381466530887/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1,1] middleBeta) ≤ (381466530889/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2621461960691/1000000000000:ℝ) (2621461960693/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_193.1, bound_193.2]
  · norm_num
  · norm_num

private theorem bound_195 : (114117041971/500000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1] middleBeta ∧ prefixEval [4,2,1,1,1,1] middleBeta ≤ (228234083943/1000000000000:ℝ) := by
  suffices hh : (114117041971/500000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,1,1] middleBeta) ≤ (228234083943/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4381466530887/1000000000000:ℝ) (4381466530889/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_194.1, bound_194.2]
  · norm_num
  · norm_num

private theorem bound_196 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1,1] middleAlpha ∧ prefixEval [1,1,1,1] middleAlpha ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,1] middleAlpha) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_126.1, bound_126.2]
  · norm_num
  · norm_num

private theorem bound_197 : (383272611851/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1] middleAlpha ∧ prefixEval [2,1,1,1,1] middleAlpha ≤ (95818152963/250000000000:ℝ) := by
  suffices hh : (383272611851/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1,1] middleAlpha) ≤ (95818152963/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2609108945117/1000000000000:ℝ) (2609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_196.1, bound_196.2]
  · norm_num
  · norm_num

private theorem bound_198 : (228140042509/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1] middleAlpha ∧ prefixEval [4,2,1,1,1,1] middleAlpha ≤ (22814004251/100000000000:ℝ) := by
  suffices hh : (228140042509/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,1,1] middleAlpha) ≤ (22814004251/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4383272611851/1000000000000:ℝ) (1095818152963/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_197.1, bound_197.2]
  · norm_num
  · norm_num

private theorem bound_199 : (11755179/125000000000:ℝ) ≤ middleWidth [4,2,1,1,1,1] ∧ middleWidth [4,2,1,1,1,1] ≤ (47020717/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_195.1, bound_198.2])]
  constructor <;> linarith only [bound_195.1, bound_195.2, bound_198.1, bound_198.2]

private theorem bound_200 : ¬ (middleWidth [2,1,1,3,1,1] ≤ middleWidth [4,2,1,1,1,1]) := by linarith only [bound_122.1, bound_199.2]

private theorem bound_201 : middleNormalized (⟨[4,2,1,1,1,1],[2,1,1,3,1,1]⟩ : MiddleCore) = (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_200, ite_false]

private theorem bound_202 : (281036428777/1000000000000:ℝ) ≤ prefixEval [3,1,1,3] middleBeta ∧ prefixEval [3,1,1,3] middleBeta ≤ (140518214389/500000000000:ℝ) := by
  suffices hh : (281036428777/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,1,3] middleBeta) ≤ (140518214389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (711651513899/200000000000:ℝ) (444782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_203 : (48788620367/62500000000:ℝ) ≤ prefixEval [1,3,1,1,3] middleBeta ∧ prefixEval [1,3,1,1,3] middleBeta ≤ (390308962937/500000000000:ℝ) := by
  suffices hh : (48788620367/62500000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [3,1,1,3] middleBeta) ≤ (390308962937/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1281036428777/1000000000000:ℝ) (640518214389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_202.1, bound_202.2]
  · norm_num
  · norm_num

private theorem bound_204 : (280801396377/500000000000:ℝ) ≤ prefixEval [1,1,3,1,1,3] middleBeta ∧ prefixEval [1,1,3,1,1,3] middleBeta ≤ (140400698189/250000000000:ℝ) := by
  suffices hh : (280801396377/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,1,1,3] middleBeta) ≤ (140400698189/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (111288620367/62500000000:ℝ) (890308962937/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_203.1, bound_203.2]
  · norm_num
  · norm_num

private theorem bound_205 : (390380586259/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,3] middleBeta ∧ prefixEval [2,1,1,3,1,1,3] middleBeta ≤ (19519029313/50000000000:ℝ) := by
  suffices hh : (390380586259/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,1,1,3] middleBeta) ≤ (19519029313/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1280801396377/500000000000:ℝ) (640400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_204.1, bound_204.2]
  · norm_num
  · norm_num

private theorem bound_206 : (280392996039/1000000000000:ℝ) ≤ prefixEval [3,1,1,3] middleAlpha ∧ prefixEval [3,1,1,3] middleAlpha ≤ (7009824901/25000000000:ℝ) := by
  suffices hh : (280392996039/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,1,3] middleAlpha) ≤ (7009824901/25000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3566422892599/1000000000000:ℝ) (17832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_008.1, bound_008.2]
  · norm_num
  · norm_num

private theorem bound_207 : (6248081663/8000000000:ℝ) ≤ prefixEval [1,3,1,1,3] middleAlpha ∧ prefixEval [1,3,1,1,3] middleAlpha ≤ (781010207877/1000000000000:ℝ) := by
  suffices hh : (6248081663/8000000000:ℝ) ≤ 1 / (1 + prefixEval [3,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,1,1,3] middleAlpha) ≤ (781010207877/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1280392996039/1000000000000:ℝ) (32009824901/25000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_206.1, bound_206.2]
  · norm_num
  · norm_num

private theorem bound_208 : (112295819033/200000000000:ℝ) ≤ prefixEval [1,1,3,1,1,3] middleAlpha ∧ prefixEval [1,1,3,1,1,3] middleAlpha ≤ (561479095167/1000000000000:ℝ) := by
  suffices hh : (112295819033/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,1,1,3] middleAlpha) ≤ (561479095167/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (14248081663/8000000000:ℝ) (1781010207877/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_207.1, bound_207.2]
  · norm_num
  · norm_num

private theorem bound_209 : (390399438311/1000000000000:ℝ) ≤ prefixEval [2,1,1,3,1,1,3] middleAlpha ∧ prefixEval [2,1,1,3,1,1,3] middleAlpha ≤ (48799929789/125000000000:ℝ) := by
  suffices hh : (390399438311/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,1,1,3] middleAlpha) ≤ (48799929789/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (512295819033/200000000000:ℝ) (2561479095167/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_208.1, bound_208.2]
  · norm_num
  · norm_num

private theorem bound_210 : (18852051/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,1,1,3] ∧ middleWidth [2,1,1,3,1,1,3] ≤ (18852053/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_205.2, bound_209.1])]
  constructor <;> linarith only [bound_205.1, bound_205.2, bound_209.1, bound_209.2]

private theorem bound_211 : ¬ (middleWidth [2,1,1,3,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,2,1,1,1,1,3]) := by linarith only [bound_210.1, bound_174.2]

private theorem bound_212 : (383254315573/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1,3] middleRho ∧ prefixEval [2,1,1,1,1,3] middleRho ≤ (15330172623/40000000000:ℝ) := by
  suffices hh : (383254315573/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,1,1,3] middleRho) ≤ (15330172623/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1304616751023/500000000000:ℝ) (81538546939/31250000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_185.1, bound_185.2]
  · norm_num
  · norm_num

private theorem bound_213 : (57035248699/250000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1,3] middleRho ∧ prefixEval [4,2,1,1,1,1,3] middleRho ≤ (228140994797/1000000000000:ℝ) := by
  suffices hh : (57035248699/250000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,1,1,3] middleRho) ≤ (228140994797/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4383254315573/1000000000000:ℝ) (175330172623/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_212.1, bound_212.2]
  · norm_num
  · norm_num

private theorem bound_214 : middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,3,1,1] middleAlpha + prefixEval [4,2,1,1,1,1,3] middleRho := by
  norm_num [middleE3, bound_211]

private theorem bound_215 : (923704316211/200000000000:ℝ) ≤ middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) ∧ middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) ≤ (4618521581057/1000000000000:ℝ) := by
  rw [bound_214]
  constructor <;> linarith only [bound_121.1, bound_121.2, bound_213.1, bound_213.2]

private theorem bound_216 : (621461960691/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,1,3] middleBeta ∧ prefixEval [1,1,1,1,1,3] middleBeta ≤ (621461960693/1000000000000:ℝ) := by
  suffices hh : (621461960691/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,1,1,3] middleBeta) ≤ (621461960693/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1609108945117/1000000000000:ℝ) (1609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_168.1, bound_168.2]
  · norm_num
  · norm_num

private theorem bound_217 : (381466530887/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,1,1,1,3] middleBeta ≤ (381466530889/1000000000000:ℝ) := by
  suffices hh : (381466530887/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1,1,1,3] middleBeta) ≤ (381466530889/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2621461960691/1000000000000:ℝ) (2621461960693/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_216.1, bound_216.2]
  · norm_num
  · norm_num

private theorem bound_218 : (114117041971/500000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1,1,3] middleBeta ∧ prefixEval [4,2,1,1,1,1,1,3] middleBeta ≤ (228234083943/1000000000000:ℝ) := by
  suffices hh : (114117041971/500000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1,1,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,1,1,1,3] middleBeta) ≤ (228234083943/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4381466530887/1000000000000:ℝ) (4381466530889/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_217.1, bound_217.2]
  · norm_num
  · norm_num

private theorem bound_219 : (620982012391/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,1,1,3] middleAlpha ≤ (620982012393/1000000000000:ℝ) := by
  suffices hh : (620982012391/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,1,1,3] middleAlpha) ≤ (620982012393/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1610352602883/1000000000000:ℝ) (322070520577/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_171.1, bound_171.2]
  · norm_num
  · norm_num

private theorem bound_220 : (23846024011/62500000000:ℝ) ≤ prefixEval [2,1,1,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,1,1,1,3] middleAlpha ≤ (381536384177/1000000000000:ℝ) := by
  suffices hh : (23846024011/62500000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1,1,1,3] middleAlpha) ≤ (381536384177/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2620982012391/1000000000000:ℝ) (2620982012393/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_219.1, bound_219.2]
  · norm_num
  · norm_num

private theorem bound_221 : (114115222643/500000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1,1,3] middleAlpha ∧ prefixEval [4,2,1,1,1,1,1,3] middleAlpha ≤ (228230445287/1000000000000:ℝ) := by
  suffices hh : (114115222643/500000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,1,1,1,3] middleAlpha) ≤ (228230445287/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (273846024011/62500000000:ℝ) (4381536384177/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_220.1, bound_220.2]
  · norm_num
  · norm_num

private theorem bound_222 : (727731/200000000000:ℝ) ≤ middleWidth [4,2,1,1,1,1,1,3] ∧ middleWidth [4,2,1,1,1,1,1,3] ≤ (3638657/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_218.1, bound_221.2])]
  constructor <;> linarith only [bound_218.1, bound_218.2, bound_221.1, bound_221.2]

private theorem bound_223 : ¬ (middleWidth [2,1,1,3,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,2,1,1,1,1,1,3]) := by linarith only [bound_158.1, bound_222.2]

private theorem bound_224 : (77676732333/125000000000:ℝ) ≤ prefixEval [1,1,1,1,1,3] middleRho ∧ prefixEval [1,1,1,1,1,3] middleRho ≤ (310706929333/500000000000:ℝ) := by
  suffices hh : (77676732333/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,1,1,1,3] middleRho) ≤ (310706929333/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (804616751023/500000000000:ℝ) (50288546939/31250000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_185.1, bound_185.2]
  · norm_num
  · norm_num

private theorem bound_225 : (76294706133/200000000000:ℝ) ≤ prefixEval [2,1,1,1,1,1,3] middleRho ∧ prefixEval [2,1,1,1,1,1,3] middleRho ≤ (190736765333/500000000000:ℝ) := by
  suffices hh : (76294706133/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,1,1,1,3] middleRho) ≤ (190736765333/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (327676732333/125000000000:ℝ) (1310706929333/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_224.1, bound_224.2]
  · norm_num
  · norm_num

private theorem bound_226 : (114116859659/500000000000:ℝ) ≤ prefixEval [4,2,1,1,1,1,1,3] middleRho ∧ prefixEval [4,2,1,1,1,1,1,3] middleRho ≤ (228233719319/1000000000000:ℝ) := by
  suffices hh : (114116859659/500000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,1,1,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,1,1,1,3] middleRho) ≤ (228233719319/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (876294706133/200000000000:ℝ) (2190736765333/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_225.1, bound_225.2]
  · norm_num
  · norm_num

private theorem bound_227 : middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,3,1,1] middleBeta + prefixEval [4,2,1,1,1,1,1,3] middleRho := by
  norm_num [middleE13, bound_223]

private theorem bound_228 : (4618803632353/1000000000000:ℝ) ≤ middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) ∧ middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore) ≤ (923760726471/200000000000:ℝ) := by
  rw [bound_227]
  constructor <;> linarith only [bound_115.1, bound_115.2, bound_226.1, bound_226.2]

private theorem bound_229 : middleEqualBounds (⟨[4,2,1,1,1,1],[2,1,1,3,1,1]⟩ : MiddleCore) = (middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore), middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_201]

private theorem bound_230 : middleBounds (⟨[2,1,1,3,1,1],[4,2,1,1,1]⟩ : MiddleCore) = (middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,1,1]⟩ : MiddleCore), middleE3 (⟨[4,2,1,1,1],[2,1,1,3,1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_131, bound_192, bound_229]

private theorem bound_231 : (227883607047/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2] middleBeta ∧ prefixEval [4,2,1,1,2] middleBeta ≤ (28485450881/125000000000:ℝ) := by
  suffices hh : (227883607047/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2] middleBeta) ≤ (28485450881/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (137131408463/31250000000:ℝ) (2194102535409/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_064.1, bound_064.2]
  · norm_num
  · norm_num

private theorem bound_232 : (56999123439/250000000000:ℝ) ≤ prefixEval [4,2,1,1,2] middleAlpha ∧ prefixEval [4,2,1,1,2] middleAlpha ≤ (227996493757/1000000000000:ℝ) := by
  suffices hh : (56999123439/250000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2] middleAlpha) ≤ (227996493757/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4386032361837/1000000000000:ℝ) (4386032361839/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_068.1, bound_068.2]
  · norm_num
  · norm_num

private theorem bound_233 : (28221677/250000000000:ℝ) ≤ middleWidth [4,2,1,1,2] ∧ middleWidth [4,2,1,1,2] ≤ (11288671/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_231.2, bound_232.1])]
  constructor <;> linarith only [bound_231.1, bound_231.2, bound_232.1, bound_232.2]

private theorem bound_234 : middleWidth [4,2,1,1,2] ≤ middleWidth [2,1,1,3,1,1] := by linarith only [bound_233.2, bound_122.1]

private theorem bound_235 : middleNormalized (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore) = (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_234, ite_true]

private theorem bound_236 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1] middleBeta ∧ prefixEval [2,1] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1] middleBeta) ∧ 1 / (2 + prefixEval [1] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_110.1, bound_110.2]
  · norm_num
  · norm_num

private theorem bound_237 : (359481785611/500000000000:ℝ) ≤ prefixEval [1,2,1] middleBeta ∧ prefixEval [1,2,1] middleBeta ≤ (89870446403/125000000000:ℝ) := by
  suffices hh : (359481785611/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1] middleBeta) ∧ 1 / (1 + prefixEval [2,1] middleBeta) ≤ (89870446403/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1390891054881/1000000000000:ℝ) (1390891054883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_236.1, bound_236.2]
  · norm_num
  · norm_num

private theorem bound_238 : (581745894293/1000000000000:ℝ) ≤ prefixEval [1,1,2,1] middleBeta ∧ prefixEval [1,1,2,1] middleBeta ≤ (116349178859/200000000000:ℝ) := by
  suffices hh : (581745894293/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1] middleBeta) ∧ 1 / (1 + prefixEval [1,2,1] middleBeta) ≤ (116349178859/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (859481785611/500000000000:ℝ) (214870446403/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_237.1, bound_237.2]
  · norm_num
  · norm_num

private theorem bound_239 : (24208424283/62500000000:ℝ) ≤ prefixEval [2,1,1,2,1] middleBeta ∧ prefixEval [2,1,1,2,1] middleBeta ≤ (387334788529/1000000000000:ℝ) := by
  suffices hh : (24208424283/62500000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,1] middleBeta) ≤ (387334788529/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2581745894293/1000000000000:ℝ) (516349178859/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_238.1, bound_238.2]
  · norm_num
  · norm_num

private theorem bound_240 : (227928810587/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1] middleBeta ∧ prefixEval [4,2,1,1,2,1] middleBeta ≤ (56982202647/250000000000:ℝ) := by
  suffices hh : (227928810587/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2,1] middleBeta) ≤ (56982202647/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (274208424283/62500000000:ℝ) (4387334788529/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_239.1, bound_239.2]
  · norm_num
  · norm_num

private theorem bound_241 : (71651513899/200000000000:ℝ) ≤ prefixEval [2,1] middleAlpha ∧ prefixEval [2,1] middleAlpha ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1] middleAlpha) ∧ 1 / (2 + prefixEval [1] middleAlpha) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (2791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_116.1, bound_116.2]
  · norm_num
  · norm_num

private theorem bound_242 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2,1] middleAlpha ∧ prefixEval [1,2,1] middleAlpha ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1] middleAlpha) ∧ 1 / (1 + prefixEval [2,1] middleAlpha) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_241.1, bound_241.2]
  · norm_num
  · norm_num

private theorem bound_243 : (287979054337/500000000000:ℝ) ≤ prefixEval [1,1,2,1] middleAlpha ∧ prefixEval [1,1,2,1] middleAlpha ≤ (143989527169/250000000000:ℝ) := by
  suffices hh : (287979054337/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,2,1] middleAlpha) ≤ (143989527169/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1736237384173/1000000000000:ℝ) (69449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_242.1, bound_242.2]
  · norm_num
  · norm_num

private theorem bound_244 : (12131408463/31250000000:ℝ) ≤ prefixEval [2,1,1,2,1] middleAlpha ∧ prefixEval [2,1,1,2,1] middleAlpha ≤ (194102535409/500000000000:ℝ) := by
  suffices hh : (12131408463/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2,1] middleAlpha) ≤ (194102535409/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1287979054337/500000000000:ℝ) (643989527169/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_243.1, bound_243.2]
  · norm_num
  · norm_num

private theorem bound_245 : (227883607047/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1] middleAlpha ∧ prefixEval [4,2,1,1,2,1] middleAlpha ≤ (28485450881/125000000000:ℝ) := by
  suffices hh : (227883607047/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2,1] middleAlpha) ≤ (28485450881/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (137131408463/31250000000:ℝ) (2194102535409/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_244.1, bound_244.2]
  · norm_num
  · norm_num

private theorem bound_246 : (45203539/1000000000000:ℝ) ≤ middleWidth [4,2,1,1,2,1] ∧ middleWidth [4,2,1,1,2,1] ≤ (45203541/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_240.1, bound_245.2])]
  constructor <;> linarith only [bound_240.1, bound_240.2, bound_245.1, bound_245.2]

private theorem bound_247 : middleWidth [4,2,1,1,2,1] ≤ middleWidth [2,1,1,3,1,1] := by linarith only [bound_246.2, bound_122.1]

private theorem bound_248 : middleNormalized (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) = (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_247, ite_true]

private theorem bound_249 : (227883607047/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,3] middleBeta ∧ prefixEval [4,2,1,1,2,1,3] middleBeta ≤ (28485450881/125000000000:ℝ) := by
  suffices hh : (227883607047/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2,1,3] middleBeta) ≤ (28485450881/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (137131408463/31250000000:ℝ) (2194102535409/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_094.1, bound_094.2]
  · norm_num
  · norm_num

private theorem bound_250 : (227888306889/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,3] middleAlpha ∧ prefixEval [4,2,1,1,2,1,3] middleAlpha ≤ (22788830689/100000000000:ℝ) := by
  suffices hh : (227888306889/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2,1,3] middleAlpha) ≤ (22788830689/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2194057285451/500000000000:ℝ) (4388114570903/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_098.1, bound_098.2]
  · norm_num
  · norm_num

private theorem bound_251 : (4699841/1000000000000:ℝ) ≤ middleWidth [4,2,1,1,2,1,3] ∧ middleWidth [4,2,1,1,2,1,3] ≤ (4699843/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_249.2, bound_250.1])]
  constructor <;> linarith only [bound_249.1, bound_249.2, bound_250.1, bound_250.2]

private theorem bound_252 : ¬ (middleWidth [2,1,1,3,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,2,1,1,2,1,3]) := by linarith only [bound_210.1, bound_251.2]

private theorem bound_253 : (358593221417/1000000000000:ℝ) ≤ prefixEval [2,1,3] middleRho ∧ prefixEval [2,1,3] middleRho ≤ (179296610709/500000000000:ℝ) := by
  suffices hh : (358593221417/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleRho) ∧ 1 / (2 + prefixEval [1,3] middleRho) ≤ (179296610709/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1394337567297/500000000000:ℝ) (557735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_052.1, bound_052.2]
  · norm_num
  · norm_num

private theorem bound_254 : (368027745257/500000000000:ℝ) ≤ prefixEval [1,2,1,3] middleRho ∧ prefixEval [1,2,1,3] middleRho ≤ (147211098103/200000000000:ℝ) := by
  suffices hh : (368027745257/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleRho) ∧ 1 / (1 + prefixEval [2,1,3] middleRho) ≤ (147211098103/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1358593221417/1000000000000:ℝ) (679296610709/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_253.1, bound_253.2]
  · norm_num
  · norm_num

private theorem bound_255 : (57601845417/100000000000:ℝ) ≤ prefixEval [1,1,2,1,3] middleRho ∧ prefixEval [1,1,2,1,3] middleRho ≤ (576018454171/1000000000000:ℝ) := by
  suffices hh : (57601845417/100000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,2,1,3] middleRho) ≤ (576018454171/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (868027745257/500000000000:ℝ) (347211098103/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_254.1, bound_254.2]
  · norm_num
  · norm_num

private theorem bound_256 : (97048994193/250000000000:ℝ) ≤ prefixEval [2,1,1,2,1,3] middleRho ∧ prefixEval [2,1,1,2,1,3] middleRho ≤ (388195976773/1000000000000:ℝ) := by
  suffices hh : (97048994193/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,2,1,3] middleRho) ≤ (388195976773/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (257601845417/100000000000:ℝ) (2576018454171/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_255.1, bound_255.2]
  · norm_num
  · norm_num

private theorem bound_257 : (22788407931/100000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,3] middleRho ∧ prefixEval [4,2,1,1,2,1,3] middleRho ≤ (227884079311/1000000000000:ℝ) := by
  suffices hh : (22788407931/100000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,2,1,3] middleRho) ≤ (227884079311/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1097048994193/250000000000:ℝ) (4388195976773/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_256.1, bound_256.2]
  · norm_num
  · norm_num

private theorem bound_258 : middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,3,1,1] middleAlpha + prefixEval [4,2,1,1,2,1,3] middleRho := by
  norm_num [middleE3, bound_252]

private theorem bound_259 : (4618264665569/1000000000000:ℝ) ≤ middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) ∧ middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) ≤ (4618264665571/1000000000000:ℝ) := by
  rw [bound_258]
  constructor <;> linarith only [bound_121.1, bound_121.2, bound_257.1, bound_257.2]

private theorem bound_260 : (359481785611/500000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleBeta ∧ prefixEval [1,2,1,1,3] middleBeta ≤ (89870446403/125000000000:ℝ) := by
  suffices hh : (359481785611/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [2,1,1,3] middleBeta) ≤ (89870446403/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1390891054881/1000000000000:ℝ) (1390891054883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_004.1, bound_004.2]
  · norm_num
  · norm_num

private theorem bound_261 : (581745894293/1000000000000:ℝ) ≤ prefixEval [1,1,2,1,1,3] middleBeta ∧ prefixEval [1,1,2,1,1,3] middleBeta ≤ (116349178859/200000000000:ℝ) := by
  suffices hh : (581745894293/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,2,1,1,3] middleBeta) ≤ (116349178859/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (859481785611/500000000000:ℝ) (214870446403/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_260.1, bound_260.2]
  · norm_num
  · norm_num

private theorem bound_262 : (24208424283/62500000000:ℝ) ≤ prefixEval [2,1,1,2,1,1,3] middleBeta ∧ prefixEval [2,1,1,2,1,1,3] middleBeta ≤ (387334788529/1000000000000:ℝ) := by
  suffices hh : (24208424283/62500000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,1,1,3] middleBeta) ≤ (387334788529/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2581745894293/1000000000000:ℝ) (516349178859/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_261.1, bound_261.2]
  · norm_num
  · norm_num

private theorem bound_263 : (227928810587/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,1,3] middleBeta ∧ prefixEval [4,2,1,1,2,1,1,3] middleBeta ≤ (56982202647/250000000000:ℝ) := by
  suffices hh : (227928810587/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,1,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2,1,1,3] middleBeta) ≤ (56982202647/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (274208424283/62500000000:ℝ) (4387334788529/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_262.1, bound_262.2]
  · norm_num
  · norm_num

private theorem bound_264 : (17990175099/25000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleAlpha ∧ prefixEval [1,2,1,1,3] middleAlpha ≤ (719607003961/1000000000000:ℝ) := by
  suffices hh : (17990175099/25000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,1,1,3] middleAlpha) ≤ (719607003961/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (277929479423/200000000000:ℝ) (347411849279/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_009.1, bound_009.2]
  · norm_num
  · norm_num

private theorem bound_265 : (290764109967/500000000000:ℝ) ≤ prefixEval [1,1,2,1,1,3] middleAlpha ∧ prefixEval [1,1,2,1,1,3] middleAlpha ≤ (116305643987/200000000000:ℝ) := by
  suffices hh : (290764109967/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,2,1,1,3] middleAlpha) ≤ (116305643987/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (42990175099/25000000000:ℝ) (1719607003961/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_264.1, bound_264.2]
  · norm_num
  · norm_num

private theorem bound_266 : (193683724291/500000000000:ℝ) ≤ prefixEval [2,1,1,2,1,1,3] middleAlpha ∧ prefixEval [2,1,1,2,1,1,3] middleAlpha ≤ (387367448583/1000000000000:ℝ) := by
  suffices hh : (193683724291/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2,1,1,3] middleAlpha) ≤ (387367448583/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1290764109967/500000000000:ℝ) (516305643987/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_265.1, bound_265.2]
  · norm_num
  · norm_num

private theorem bound_267 : (11396355693/50000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,1,3] middleAlpha ∧ prefixEval [4,2,1,1,2,1,1,3] middleAlpha ≤ (227927113861/1000000000000:ℝ) := by
  suffices hh : (11396355693/50000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2,1,1,3] middleAlpha) ≤ (227927113861/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2193683724291/500000000000:ℝ) (4387367448583/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_266.1, bound_266.2]
  · norm_num
  · norm_num

private theorem bound_268 : (848363/500000000000:ℝ) ≤ middleWidth [4,2,1,1,2,1,1,3] ∧ middleWidth [4,2,1,1,2,1,1,3] ≤ (212091/125000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_263.1, bound_267.2])]
  constructor <;> linarith only [bound_263.1, bound_263.2, bound_267.1, bound_267.2]

private theorem bound_269 : ¬ (middleWidth [2,1,1,3,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,2,1,1,2,1,1,3]) := by linarith only [bound_158.1, bound_268.2]

private theorem bound_270 : (12211453061/31250000000:ℝ) ≤ prefixEval [2,1,1,3] middleRho ∧ prefixEval [2,1,1,3] middleRho ≤ (390766497953/1000000000000:ℝ) := by
  suffices hh : (12211453061/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3] middleRho) ≤ (390766497953/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1279536507401/500000000000:ℝ) (2559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_160.1, bound_160.2]
  · norm_num
  · norm_num

private theorem bound_271 : (719027961539/1000000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleRho ∧ prefixEval [1,2,1,1,3] middleRho ≤ (35951398077/50000000000:ℝ) := by
  suffices hh : (719027961539/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [2,1,1,3] middleRho) ≤ (35951398077/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (43461453061/31250000000:ℝ) (1390766497953/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_270.1, bound_270.2]
  · norm_num
  · norm_num

private theorem bound_272 : (116344820721/200000000000:ℝ) ≤ prefixEval [1,1,2,1,1,3] middleRho ∧ prefixEval [1,1,2,1,1,3] middleRho ≤ (581724103607/1000000000000:ℝ) := by
  suffices hh : (116344820721/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,2,1,1,3] middleRho) ≤ (581724103607/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1719027961539/1000000000000:ℝ) (85951398077/50000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_271.1, bound_271.2]
  · norm_num
  · norm_num

private theorem bound_273 : (193669028887/500000000000:ℝ) ≤ prefixEval [2,1,1,2,1,1,3] middleRho ∧ prefixEval [2,1,1,2,1,1,3] middleRho ≤ (15493522311/40000000000:ℝ) := by
  suffices hh : (193669028887/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,2,1,1,3] middleRho) ≤ (15493522311/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (516344820721/200000000000:ℝ) (2581724103607/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_272.1, bound_272.2]
  · norm_num
  · norm_num

private theorem bound_274 : (45585728149/200000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,1,3] middleRho ∧ prefixEval [4,2,1,1,2,1,1,3] middleRho ≤ (113964320373/500000000000:ℝ) := by
  suffices hh : (45585728149/200000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,1,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,2,1,1,3] middleRho) ≤ (113964320373/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2193669028887/500000000000:ℝ) (175493522311/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_273.1, bound_273.2]
  · norm_num
  · norm_num

private theorem bound_275 : middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,3,1,1] middleBeta + prefixEval [4,2,1,1,2,1,1,3] middleRho := by
  norm_num [middleE13, bound_269]

private theorem bound_276 : (230924927689/50000000000:ℝ) ≤ middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) ∧ middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) ≤ (2309249276891/500000000000:ℝ) := by
  rw [bound_275]
  constructor <;> linarith only [bound_115.1, bound_115.2, bound_274.1, bound_274.2]

private theorem bound_277 : middleEqualBounds (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore) = (middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore), middleE13 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_248]

private theorem bound_278 : ¬ (middleWidth [4,2,1,1,2] ≤ middleWidth [2,1,1,3,1,1,1]) := by linarith only [bound_233.1, bound_140.2]

private theorem bound_279 : middleNormalized (⟨[2,1,1,3,1,1,1],[4,2,1,1,2]⟩ : MiddleCore) = (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_278, ite_false]

private theorem bound_280 : (56999123439/250000000000:ℝ) ≤ prefixEval [4,2,1,1,2,3] middleBeta ∧ prefixEval [4,2,1,1,2,3] middleBeta ≤ (227996493757/1000000000000:ℝ) := by
  suffices hh : (56999123439/250000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2,3] middleBeta) ≤ (227996493757/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4386032361837/1000000000000:ℝ) (4386032361839/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_077.1, bound_077.2]
  · norm_num
  · norm_num

private theorem bound_281 : (113992921967/500000000000:ℝ) ≤ prefixEval [4,2,1,1,2,3] middleAlpha ∧ prefixEval [4,2,1,1,2,3] middleAlpha ≤ (45597168787/200000000000:ℝ) := by
  suffices hh : (113992921967/500000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2,3] middleAlpha) ≤ (45597168787/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1096559311251/250000000000:ℝ) (877247449001/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_081.1, bound_081.2]
  · norm_num
  · norm_num

private theorem bound_282 : (10649821/1000000000000:ℝ) ≤ middleWidth [4,2,1,1,2,3] ∧ middleWidth [4,2,1,1,2,3] ≤ (10649823/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_280.1, bound_281.2])]
  constructor <;> linarith only [bound_280.1, bound_280.2, bound_281.1, bound_281.2]

private theorem bound_283 : ¬ (middleWidth [4,2,1,1,2,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,1,1,1,3]) := by linarith only [bound_282.1, bound_158.2]

private theorem bound_284 : middleE3 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) = 4 + prefixEval [4,2,1,1,2] middleAlpha + prefixEval [2,1,1,3,1,1,1,3] middleRho := by
  norm_num [middleE3, bound_283]

private theorem bound_285 : (4618565660523/1000000000000:ℝ) ≤ middleE3 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) ∧ middleE3 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) ≤ (184742626421/40000000000:ℝ) := by
  rw [bound_284]
  constructor <;> linarith only [bound_232.1, bound_232.2, bound_165.1, bound_165.2]

private theorem bound_286 : ¬ (middleWidth [4,2,1,1,2,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,1,1,1,1,3]) := by linarith only [bound_251.1, bound_183.2]

private theorem bound_287 : middleE13 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) = 4 + prefixEval [4,2,1,1,2] middleBeta + prefixEval [2,1,1,3,1,1,1,1,3] middleRho := by
  norm_num [middleE13, bound_286]

private theorem bound_288 : (4618380689239/1000000000000:ℝ) ≤ middleE13 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) ∧ middleE13 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore) ≤ (2309190344621/500000000000:ℝ) := by
  rw [bound_287]
  constructor <;> linarith only [bound_231.1, bound_231.2, bound_189.1, bound_189.2]

private theorem bound_289 : middleEqualBounds (⟨[2,1,1,3,1,1,1],[4,2,1,1,2]⟩ : MiddleCore) = (middleE13 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore), middleE3 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_279]

private theorem bound_290 : middleBounds (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore) = (middleE3 (⟨[2,1,1,3,1,1],[4,2,1,1,2,1]⟩ : MiddleCore), middleE3 (⟨[4,2,1,1,2],[2,1,1,3,1,1,1]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_235, bound_277, bound_289]

private theorem bound_291 : (148886733567/500000000000:ℝ) ≤ prefixEval [3,2] middleBeta ∧ prefixEval [3,2] middleBeta ≤ (59554693427/200000000000:ℝ) := by
  suffices hh : (148886733567/500000000000:ℝ) ≤ 1 / (3 + prefixEval [2] middleBeta) ∧ 1 / (3 + prefixEval [2] middleBeta) ≤ (59554693427/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (671651513899/200000000000:ℝ) (419782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_061.1, bound_061.2]
  · norm_num
  · norm_num

private theorem bound_292 : (96318813079/125000000000:ℝ) ≤ prefixEval [1,3,2] middleBeta ∧ prefixEval [1,3,2] middleBeta ≤ (385275252317/500000000000:ℝ) := by
  suffices hh : (96318813079/125000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2] middleBeta) ∧ 1 / (1 + prefixEval [3,2] middleBeta) ≤ (385275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (648886733567/500000000000:ℝ) (259554693427/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_291.1, bound_291.2]
  · norm_num
  · norm_num

private theorem bound_293 : (564796088777/1000000000000:ℝ) ≤ prefixEval [1,1,3,2] middleBeta ∧ prefixEval [1,1,3,2] middleBeta ≤ (282398044389/500000000000:ℝ) := by
  suffices hh : (564796088777/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2] middleBeta) ≤ (282398044389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (221318813079/125000000000:ℝ) (885275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_292.1, bound_292.2]
  · norm_num
  · norm_num

private theorem bound_294 : (19494727171/50000000000:ℝ) ≤ prefixEval [2,1,1,3,2] middleBeta ∧ prefixEval [2,1,1,3,2] middleBeta ≤ (389894543421/1000000000000:ℝ) := by
  suffices hh : (19494727171/50000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2] middleBeta) ≤ (389894543421/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2564796088777/1000000000000:ℝ) (1282398044389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_293.1, bound_293.2]
  · norm_num
  · norm_num

private theorem bound_295 : (36318813079/125000000000:ℝ) ≤ prefixEval [3,2] middleAlpha ∧ prefixEval [3,2] middleAlpha ≤ (145275252317/500000000000:ℝ) := by
  suffices hh : (36318813079/125000000000:ℝ) ≤ 1 / (3 + prefixEval [2] middleAlpha) ∧ 1 / (3 + prefixEval [2] middleAlpha) ≤ (145275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (430217803813/125000000000:ℝ) (688348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_065.1, bound_065.2]
  · norm_num
  · norm_num

private theorem bound_296 : (774863127331/1000000000000:ℝ) ≤ prefixEval [1,3,2] middleAlpha ∧ prefixEval [1,3,2] middleAlpha ≤ (774863127333/1000000000000:ℝ) := by
  suffices hh : (774863127331/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2] middleAlpha) ∧ 1 / (1 + prefixEval [3,2] middleAlpha) ≤ (774863127333/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (161318813079/125000000000:ℝ) (645275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_295.1, bound_295.2]
  · norm_num
  · norm_num

private theorem bound_297 : (563423728061/1000000000000:ℝ) ≤ prefixEval [1,1,3,2] middleAlpha ∧ prefixEval [1,1,3,2] middleAlpha ≤ (281711864031/500000000000:ℝ) := by
  suffices hh : (563423728061/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,2] middleAlpha) ≤ (281711864031/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1774863127331/1000000000000:ℝ) (1774863127333/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_296.1, bound_296.2]
  · norm_num
  · norm_num

private theorem bound_298 : (12190727447/31250000000:ℝ) ≤ prefixEval [2,1,1,3,2] middleAlpha ∧ prefixEval [2,1,1,3,2] middleAlpha ≤ (78020655661/200000000000:ℝ) := by
  suffices hh : (12190727447/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,2] middleAlpha) ≤ (78020655661/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2563423728061/1000000000000:ℝ) (1281711864031/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_297.1, bound_297.2]
  · norm_num
  · norm_num

private theorem bound_299 : (208734883/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,2] ∧ middleWidth [2,1,1,3,2] ≤ (41746977/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_294.2, bound_298.1])]
  constructor <;> linarith only [bound_294.1, bound_294.2, bound_298.1, bound_298.2]

private theorem bound_300 : ¬ (middleWidth [4,2,1,1,1] ≤ middleWidth [2,1,1,3,2]) := by linarith only [bound_129.1, bound_299.2]

private theorem bound_301 : middleNormalized (⟨[2,1,1,3,2],[4,2,1,1,1]⟩ : MiddleCore) = (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_300, ite_false]

private theorem bound_302 : middleWidth [2,1,1,3,2] ≤ middleWidth [4,2,1,1,1] := by linarith only [bound_299.2, bound_129.1]

private theorem bound_303 : middleNormalized (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) = (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_302, ite_true]

private theorem bound_304 : (36318813079/125000000000:ℝ) ≤ prefixEval [3,2,3] middleBeta ∧ prefixEval [3,2,3] middleBeta ≤ (145275252317/500000000000:ℝ) := by
  suffices hh : (36318813079/125000000000:ℝ) ≤ 1 / (3 + prefixEval [2,3] middleBeta) ∧ 1 / (3 + prefixEval [2,3] middleBeta) ≤ (145275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (430217803813/125000000000:ℝ) (688348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_074.1, bound_074.2]
  · norm_num
  · norm_num

private theorem bound_305 : (774863127331/1000000000000:ℝ) ≤ prefixEval [1,3,2,3] middleBeta ∧ prefixEval [1,3,2,3] middleBeta ≤ (774863127333/1000000000000:ℝ) := by
  suffices hh : (774863127331/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,3] middleBeta) ∧ 1 / (1 + prefixEval [3,2,3] middleBeta) ≤ (774863127333/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (161318813079/125000000000:ℝ) (645275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_304.1, bound_304.2]
  · norm_num
  · norm_num

private theorem bound_306 : (563423728061/1000000000000:ℝ) ≤ prefixEval [1,1,3,2,3] middleBeta ∧ prefixEval [1,1,3,2,3] middleBeta ≤ (281711864031/500000000000:ℝ) := by
  suffices hh : (563423728061/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2,3] middleBeta) ≤ (281711864031/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1774863127331/1000000000000:ℝ) (1774863127333/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_305.1, bound_305.2]
  · norm_num
  · norm_num

private theorem bound_307 : (12190727447/31250000000:ℝ) ≤ prefixEval [2,1,1,3,2,3] middleBeta ∧ prefixEval [2,1,1,3,2,3] middleBeta ≤ (78020655661/200000000000:ℝ) := by
  suffices hh : (12190727447/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2,3] middleBeta) ≤ (78020655661/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2563423728061/1000000000000:ℝ) (1281711864031/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_306.1, bound_306.2]
  · norm_num
  · norm_num

private theorem bound_308 : (291241457151/1000000000000:ℝ) ≤ prefixEval [3,2,3] middleAlpha ∧ prefixEval [3,2,3] middleAlpha ≤ (568830971/1953125000:ℝ) := by
  suffices hh : (291241457151/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [2,3] middleAlpha) ∧ 1 / (3 + prefixEval [2,3] middleAlpha) ≤ (568830971/1953125000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (17167885537/5000000000:ℝ) (3433577107401/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_078.1, bound_078.2]
  · norm_num
  · norm_num

private theorem bound_309 : (387224246271/500000000000:ℝ) ≤ prefixEval [1,3,2,3] middleAlpha ∧ prefixEval [1,3,2,3] middleAlpha ≤ (189074339/244140625:ℝ) := by
  suffices hh : (387224246271/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,2,3] middleAlpha) ≤ (189074339/244140625:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1291241457151/1000000000000:ℝ) (2521955971/1953125000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_308.1, bound_308.2]
  · norm_num
  · norm_num

private theorem bound_310 : (70444422887/125000000000:ℝ) ≤ prefixEval [1,1,3,2,3] middleAlpha ∧ prefixEval [1,1,3,2,3] middleAlpha ≤ (563555383097/1000000000000:ℝ) := by
  suffices hh : (70444422887/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,2,3] middleAlpha) ≤ (563555383097/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (887224246271/500000000000:ℝ) (433214964/244140625:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_309.1, bound_309.2]
  · norm_num
  · norm_num

private theorem bound_311 : (78016648799/200000000000:ℝ) ≤ prefixEval [2,1,1,3,2,3] middleAlpha ∧ prefixEval [2,1,1,3,2,3] middleAlpha ≤ (97520810999/250000000000:ℝ) := by
  suffices hh : (78016648799/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,2,3] middleAlpha) ≤ (97520810999/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (320444422887/125000000000:ℝ) (2563555383097/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_310.1, bound_310.2]
  · norm_num
  · norm_num

private theorem bound_312 : (5008577/250000000000:ℝ) ≤ middleWidth [2,1,1,3,2,3] ∧ middleWidth [2,1,1,3,2,3] ≤ (2003431/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_307.1, bound_311.2])]
  constructor <;> linarith only [bound_307.1, bound_307.2, bound_311.1, bound_311.2]

private theorem bound_313 : middleWidth [4,2,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,2,3] := by linarith only [bound_149.2, bound_312.1]

private theorem bound_314 : (189293070667/500000000000:ℝ) ≤ prefixEval [2,1,1,1,3] middleRho ∧ prefixEval [2,1,1,1,3] middleRho ≤ (47323267667/125000000000:ℝ) := by
  suffices hh : (189293070667/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,1,3] middleRho) ≤ (47323267667/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1320703389291/500000000000:ℝ) (330175847323/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_161.1, bound_161.2]
  · norm_num
  · norm_num

private theorem bound_315 : (14274014027/62500000000:ℝ) ≤ prefixEval [4,2,1,1,1,3] middleRho ∧ prefixEval [4,2,1,1,1,3] middleRho ≤ (228384224433/1000000000000:ℝ) := by
  suffices hh : (14274014027/62500000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,1,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,1,3] middleRho) ≤ (228384224433/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2189293070667/500000000000:ℝ) (547323267667/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_314.1, bound_314.2]
  · norm_num
  · norm_num

private theorem bound_316 : (18253281351/62500000000:ℝ) ≤ prefixEval [3,2,2] middleBeta ∧ prefixEval [3,2,2] middleBeta ≤ (292052501617/1000000000000:ℝ) := by
  suffices hh : (18253281351/62500000000:ℝ) ≤ 1 / (3 + prefixEval [2,2] middleBeta) ∧ 1 / (3 + prefixEval [2,2] middleBeta) ≤ (292052501617/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (856010472831/250000000000:ℝ) (136961675653/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_085.1, bound_085.2]
  · norm_num
  · norm_num

private theorem bound_317 : (193490589343/250000000000:ℝ) ≤ prefixEval [1,3,2,2] middleBeta ∧ prefixEval [1,3,2,2] middleBeta ≤ (773962357373/1000000000000:ℝ) := by
  suffices hh : (193490589343/250000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,2] middleBeta) ∧ 1 / (1 + prefixEval [3,2,2] middleBeta) ≤ (773962357373/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (80753281351/62500000000:ℝ) (1292052501617/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_316.1, bound_316.2]
  · norm_num
  · norm_num

private theorem bound_318 : (112741963869/200000000000:ℝ) ≤ prefixEval [1,1,3,2,2] middleBeta ∧ prefixEval [1,1,3,2,2] middleBeta ≤ (281854909673/500000000000:ℝ) := by
  suffices hh : (112741963869/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,2] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2,2] middleBeta) ≤ (281854909673/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (443490589343/250000000000:ℝ) (1773962357373/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_317.1, bound_317.2]
  · norm_num
  · norm_num

private theorem bound_319 : (97514936407/250000000000:ℝ) ≤ prefixEval [2,1,1,3,2,2] middleBeta ∧ prefixEval [2,1,1,3,2,2] middleBeta ≤ (390059745629/1000000000000:ℝ) := by
  suffices hh : (97514936407/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2,2] middleBeta) ≤ (390059745629/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (512741963869/200000000000:ℝ) (1281854909673/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_318.1, bound_318.2]
  · norm_num
  · norm_num

private theorem bound_320 : middleE3 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) = 4 + prefixEval [4,2,1,1,1,3] middleRho + prefixEval [2,1,1,3,2,2] middleBeta := by
  norm_num [middleE3, bound_313]

private theorem bound_321 : (230922198503/50000000000:ℝ) ≤ middleE3 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) ∧ middleE3 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) ≤ (2309221985031/500000000000:ℝ) := by
  rw [bound_320]
  constructor <;> linarith only [bound_315.1, bound_315.2, bound_319.1, bound_319.2]

private theorem bound_322 : (148886733567/500000000000:ℝ) ≤ prefixEval [3,2,1,3] middleBeta ∧ prefixEval [3,2,1,3] middleBeta ≤ (59554693427/200000000000:ℝ) := by
  suffices hh : (148886733567/500000000000:ℝ) ≤ 1 / (3 + prefixEval [2,1,3] middleBeta) ∧ 1 / (3 + prefixEval [2,1,3] middleBeta) ≤ (59554693427/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (671651513899/200000000000:ℝ) (419782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_091.1, bound_091.2]
  · norm_num
  · norm_num

private theorem bound_323 : (96318813079/125000000000:ℝ) ≤ prefixEval [1,3,2,1,3] middleBeta ∧ prefixEval [1,3,2,1,3] middleBeta ≤ (385275252317/500000000000:ℝ) := by
  suffices hh : (96318813079/125000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [3,2,1,3] middleBeta) ≤ (385275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (648886733567/500000000000:ℝ) (259554693427/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_322.1, bound_322.2]
  · norm_num
  · norm_num

private theorem bound_324 : (564796088777/1000000000000:ℝ) ≤ prefixEval [1,1,3,2,1,3] middleBeta ∧ prefixEval [1,1,3,2,1,3] middleBeta ≤ (282398044389/500000000000:ℝ) := by
  suffices hh : (564796088777/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2,1,3] middleBeta) ≤ (282398044389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (221318813079/125000000000:ℝ) (885275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_323.1, bound_323.2]
  · norm_num
  · norm_num

private theorem bound_325 : (19494727171/50000000000:ℝ) ≤ prefixEval [2,1,1,3,2,1,3] middleBeta ∧ prefixEval [2,1,1,3,2,1,3] middleBeta ≤ (389894543421/1000000000000:ℝ) := by
  suffices hh : (19494727171/50000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2,1,3] middleBeta) ≤ (389894543421/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2564796088777/1000000000000:ℝ) (1282398044389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_324.1, bound_324.2]
  · norm_num
  · norm_num

private theorem bound_326 : (297477144579/1000000000000:ℝ) ≤ prefixEval [3,2,1,3] middleAlpha ∧ prefixEval [3,2,1,3] middleAlpha ≤ (14873857229/50000000000:ℝ) := by
  suffices hh : (297477144579/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [2,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [2,1,3] middleAlpha) ≤ (14873857229/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1680801396377/500000000000:ℝ) (840400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_095.1, bound_095.2]
  · norm_num
  · norm_num

private theorem bound_327 : (770726485763/1000000000000:ℝ) ≤ prefixEval [1,3,2,1,3] middleAlpha ∧ prefixEval [1,3,2,1,3] middleAlpha ≤ (192681621441/250000000000:ℝ) := by
  suffices hh : (770726485763/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,2,1,3] middleAlpha) ≤ (192681621441/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1297477144579/1000000000000:ℝ) (64873857229/50000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_326.1, bound_326.2]
  · norm_num
  · norm_num

private theorem bound_328 : (282369978661/500000000000:ℝ) ≤ prefixEval [1,1,3,2,1,3] middleAlpha ∧ prefixEval [1,1,3,2,1,3] middleAlpha ≤ (564739957323/1000000000000:ℝ) := by
  suffices hh : (282369978661/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,2,1,3] middleAlpha) ≤ (564739957323/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1770726485763/1000000000000:ℝ) (442681621441/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_327.1, bound_327.2]
  · norm_num
  · norm_num

private theorem bound_329 : (48737884573/125000000000:ℝ) ≤ prefixEval [2,1,1,3,2,1,3] middleAlpha ∧ prefixEval [2,1,1,3,2,1,3] middleAlpha ≤ (77980615317/200000000000:ℝ) := by
  suffices hh : (48737884573/125000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,2,1,3] middleAlpha) ≤ (77980615317/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1282369978661/500000000000:ℝ) (2564739957323/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_328.1, bound_328.2]
  · norm_num
  · norm_num

private theorem bound_330 : (8533163/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,2,1,3] ∧ middleWidth [2,1,1,3,2,1,3] ≤ (1706633/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_325.2, bound_329.1])]
  constructor <;> linarith only [bound_325.1, bound_325.2, bound_329.1, bound_329.2]

private theorem bound_331 : middleWidth [4,2,1,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [2,1,1,3,2,1,3] := by linarith only [bound_174.2, bound_330.1]

private theorem bound_332 : (148567863717/500000000000:ℝ) ≤ prefixEval [3,2,1,2] middleBeta ∧ prefixEval [3,2,1,2] middleBeta ≤ (59427145487/200000000000:ℝ) := by
  suffices hh : (148567863717/500000000000:ℝ) ≤ 1 / (3 + prefixEval [2,1,2] middleBeta) ∧ 1 / (3 + prefixEval [2,1,2] middleBeta) ≤ (59427145487/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (336546536707/100000000000:ℝ) (3365465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_102.1, bound_102.2]
  · norm_num
  · norm_num

private theorem bound_333 : (385464673761/500000000000:ℝ) ≤ prefixEval [1,3,2,1,2] middleBeta ∧ prefixEval [1,3,2,1,2] middleBeta ≤ (192732336881/250000000000:ℝ) := by
  suffices hh : (385464673761/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,1,2] middleBeta) ∧ 1 / (1 + prefixEval [3,2,1,2] middleBeta) ≤ (192732336881/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (648567863717/500000000000:ℝ) (259427145487/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_332.1, bound_332.2]
  · norm_num
  · norm_num

private theorem bound_334 : (112935053157/200000000000:ℝ) ≤ prefixEval [1,1,3,2,1,2] middleBeta ∧ prefixEval [1,1,3,2,1,2] middleBeta ≤ (282337632893/500000000000:ℝ) := by
  suffices hh : (112935053157/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,1,2] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2,1,2] middleBeta) ≤ (282337632893/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (885464673761/500000000000:ℝ) (442732336881/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_333.1, bound_333.2]
  · norm_num
  · norm_num

private theorem bound_335 : (15596516461/40000000000:ℝ) ≤ prefixEval [2,1,1,3,2,1,2] middleBeta ∧ prefixEval [2,1,1,3,2,1,2] middleBeta ≤ (194956455763/500000000000:ℝ) := by
  suffices hh : (15596516461/40000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2,1,2] middleBeta) ≤ (194956455763/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (512935053157/200000000000:ℝ) (1282337632893/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_334.1, bound_334.2]
  · norm_num
  · norm_num

private theorem bound_336 : middleE13 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) = 4 + prefixEval [4,2,1,1,1,1,3] middleRho + prefixEval [2,1,1,3,2,1,2] middleBeta := by
  norm_num [middleE13, bound_331]

private theorem bound_337 : (4618053906321/1000000000000:ℝ) ≤ middleE13 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) ∧ middleE13 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) ≤ (4618053906323/1000000000000:ℝ) := by
  rw [bound_336]
  constructor <;> linarith only [bound_213.1, bound_213.2, bound_335.1, bound_335.2]

private theorem bound_338 : middleEqualBounds (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore) = (middleE13 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore), middleE3 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_303]

private theorem bound_339 : middleBounds (⟨[2,1,1,3,2],[4,2,1,1,1]⟩ : MiddleCore) = (middleE13 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore), middleE3 (⟨[4,2,1,1,1],[2,1,1,3,2]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_301, bound_338]

private theorem root_5 : middleRootCertificate 5 := by
  change middleRegular (⟨[2,1,1,3],[4,3]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,3],[4,3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,3],[4,3]⟩ : MiddleCore)).1 < middleInnerLeft 5 ∧ middleInnerRight 5 < (middleBounds (⟨[2,1,1,3],[4,3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_010.1]
    · linarith only [bound_013.1]
  constructor
  · have h62 : (933469578103/500000000000:ℝ) ≤ middleWidth [4,3] / middleWidth [2,1,1,3] ∧ middleWidth [4,3] / middleWidth [2,1,1,3] ≤ (1866939162319/1000000000000:ℝ) := by
      apply div_est _ _ (290229173/125000000000:ℝ) (1160916693/500000000000:ℝ) (248731553/200000000000:ℝ) (155457221/125000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_013 bound_010 <;> norm_num
    simp only [middleRatio, bound_015]
    linarith only [h62.2]
  rw [bound_060]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_038.2]
  · linarith only [bound_058.1]



private theorem root_6 : middleRootCertificate 6 := by
  change middleRegular (⟨[2,1,1,2],[4,3]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,2],[4,3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,2],[4,3]⟩ : MiddleCore)).1 < middleInnerLeft 6 ∧ middleInnerRight 6 < (middleBounds (⟨[2,1,1,2],[4,3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_069.1]
    · linarith only [bound_013.1]
  constructor
  · have h74 : (534317620147/500000000000:ℝ) ≤ middleWidth [4,3] / middleWidth [2,1,1,2] ∧ middleWidth [4,3] / middleWidth [2,1,1,2] ≤ (534317621591/500000000000:ℝ) := by
      apply div_est _ _ (290229173/125000000000:ℝ) (1160916693/500000000000:ℝ) (2172708977/1000000000000:ℝ) (2172708981/1000000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_013 bound_069 <;> norm_num
    simp only [middleRatio, bound_071]
    linarith only [h74.2]
  rw [bound_109]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_090.2]
  · linarith only [bound_107.1]



private theorem root_7 : middleRootCertificate 7 := by
  change middleRegular (⟨[2,1,1,3,1,1],[4,2,1,1,1]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,3,1,1],[4,2,1,1,1]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,3,1,1],[4,2,1,1,1]⟩ : MiddleCore)).1 < middleInnerLeft 7 ∧ middleInnerRight 7 < (middleBounds (⟨[2,1,1,3,1,1],[4,2,1,1,1]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_122.1]
    · linarith only [bound_129.1]
  constructor
  · have h133 : (65149506031/50000000000:ℝ) ≤ middleWidth [4,2,1,1,1] / middleWidth [2,1,1,3,1,1] ∧ middleWidth [4,2,1,1,1] / middleWidth [2,1,1,3,1,1] ≤ (26059802899/20000000000:ℝ) := by
      apply div_est _ _ (6167273/25000000000:ℝ) (123345461/500000000000:ℝ) (7573071/40000000000:ℝ) (189326777/1000000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_129 bound_122 <;> norm_num
    simp only [middleRatio, bound_131]
    linarith only [h133.2]
  rw [bound_230]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_215.2]
  · linarith only [bound_167.1]



private theorem root_8 : middleRootCertificate 8 := by
  change middleRegular (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore)).1 < middleInnerLeft 8 ∧ middleInnerRight 8 < (middleBounds (⟨[2,1,1,3,1,1],[4,2,1,1,2]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_122.1]
    · linarith only [bound_233.1]
  constructor
  · have h164 : (1677139629633/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,1,1] / middleWidth [4,2,1,1,2] ∧ middleWidth [2,1,1,3,1,1] / middleWidth [4,2,1,1,2] ≤ (335427935413/200000000000:ℝ) := by
      apply div_est _ _ (7573071/40000000000:ℝ) (189326777/1000000000000:ℝ) (28221677/250000000000:ℝ) (11288671/100000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_122 bound_233 <;> norm_num
    simp only [middleRatio, bound_235]
    linarith only [h164.2]
  rw [bound_290]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_259.2]
  · linarith only [bound_285.1]



private theorem root_9 : middleRootCertificate 9 := by
  change middleRegular (⟨[2,1,1,3,2],[4,2,1,1,1]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,3,2],[4,2,1,1,1]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,3,2],[4,2,1,1,1]⟩ : MiddleCore)).1 < middleInnerLeft 9 ∧ middleInnerRight 9 < (middleBounds (⟨[2,1,1,3,2],[4,2,1,1,1]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_299.1]
    · linarith only [bound_129.1]
  constructor
  · have h100 : (590919241889/500000000000:ℝ) ≤ middleWidth [4,2,1,1,1] / middleWidth [2,1,1,3,2] ∧ middleWidth [4,2,1,1,1] / middleWidth [2,1,1,3,2] ≤ (295459626171/250000000000:ℝ) := by
      apply div_est _ _ (6167273/25000000000:ℝ) (123345461/500000000000:ℝ) (208734883/1000000000000:ℝ) (41746977/200000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_129 bound_299 <;> norm_num
    simp only [middleRatio, bound_301]
    linarith only [h100.2]
  rw [bound_339]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_337.2]
  · linarith only [bound_321.1]


end M8Sep10InitialRoots2Opt

theorem solution : ∀ i : Fin 15, 5 ≤ i.val → i.val < 10 → middleRootCertificate i := by
  intro i hlo hi
  fin_cases i <;> norm_num at hlo <;> norm_num at hi <;> first | exact M8Sep10InitialRoots2Opt.root_5 | exact M8Sep10InitialRoots2Opt.root_6 | exact M8Sep10InitialRoots2Opt.root_7 | exact M8Sep10InitialRoots2Opt.root_8 | exact M8Sep10InitialRoots2Opt.root_9
#print axioms solution
