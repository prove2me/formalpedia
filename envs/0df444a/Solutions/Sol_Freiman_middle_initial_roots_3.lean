-- Prove2me | solution 1 for Freiman.middle_initial_roots_3
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:51:48.029042+00:00
-- url     : https://prove2.me/submissions/73c8352f-58a8-4df3-bceb-0b829430604b

import Theorems.Thm_Freiman_middle_width_identity
import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
open Freiman
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
namespace M8Sep10InitialRoots3Opt

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

private theorem bound_002 : (148886733567/500000000000:ℝ) ≤ prefixEval [3,2] middleBeta ∧ prefixEval [3,2] middleBeta ≤ (59554693427/200000000000:ℝ) := by
  suffices hh : (148886733567/500000000000:ℝ) ≤ 1 / (3 + prefixEval [2] middleBeta) ∧ 1 / (3 + prefixEval [2] middleBeta) ≤ (59554693427/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (671651513899/200000000000:ℝ) (419782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_003 : (96318813079/125000000000:ℝ) ≤ prefixEval [1,3,2] middleBeta ∧ prefixEval [1,3,2] middleBeta ≤ (385275252317/500000000000:ℝ) := by
  suffices hh : (96318813079/125000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2] middleBeta) ∧ 1 / (1 + prefixEval [3,2] middleBeta) ≤ (385275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (648886733567/500000000000:ℝ) (259554693427/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_004 : (564796088777/1000000000000:ℝ) ≤ prefixEval [1,1,3,2] middleBeta ∧ prefixEval [1,1,3,2] middleBeta ≤ (282398044389/500000000000:ℝ) := by
  suffices hh : (564796088777/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2] middleBeta) ≤ (282398044389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (221318813079/125000000000:ℝ) (885275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_003.1, bound_003.2]
  · norm_num
  · norm_num

private theorem bound_005 : (19494727171/50000000000:ℝ) ≤ prefixEval [2,1,1,3,2] middleBeta ∧ prefixEval [2,1,1,3,2] middleBeta ≤ (389894543421/1000000000000:ℝ) := by
  suffices hh : (19494727171/50000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2] middleBeta) ≤ (389894543421/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2564796088777/1000000000000:ℝ) (1282398044389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_004.1, bound_004.2]
  · norm_num
  · norm_num

private theorem bound_006 : (10550504633/40000000000:ℝ) ≤ middleAlpha ∧ middleAlpha ≤ (131881307913/500000000000:ℝ) := by
  dsimp only [middleAlpha]
  constructor <;> linarith only [sqrt_21_bounds.1, sqrt_21_bounds.2]

private theorem bound_007 : (55217803813/125000000000:ℝ) ≤ prefixEval [2] middleAlpha ∧ prefixEval [2] middleAlpha ≤ (88348486101/200000000000:ℝ) := by
  suffices hh : (55217803813/125000000000:ℝ) ≤ 1 / (2 + middleAlpha) ∧ 1 / (2 + middleAlpha) ≤ (88348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (90550504633/40000000000:ℝ) (1131881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_008 : (36318813079/125000000000:ℝ) ≤ prefixEval [3,2] middleAlpha ∧ prefixEval [3,2] middleAlpha ≤ (145275252317/500000000000:ℝ) := by
  suffices hh : (36318813079/125000000000:ℝ) ≤ 1 / (3 + prefixEval [2] middleAlpha) ∧ 1 / (3 + prefixEval [2] middleAlpha) ≤ (145275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (430217803813/125000000000:ℝ) (688348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_007.1, bound_007.2]
  · norm_num
  · norm_num

private theorem bound_009 : (774863127331/1000000000000:ℝ) ≤ prefixEval [1,3,2] middleAlpha ∧ prefixEval [1,3,2] middleAlpha ≤ (774863127333/1000000000000:ℝ) := by
  suffices hh : (774863127331/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2] middleAlpha) ∧ 1 / (1 + prefixEval [3,2] middleAlpha) ≤ (774863127333/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (161318813079/125000000000:ℝ) (645275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_008.1, bound_008.2]
  · norm_num
  · norm_num

private theorem bound_010 : (563423728061/1000000000000:ℝ) ≤ prefixEval [1,1,3,2] middleAlpha ∧ prefixEval [1,1,3,2] middleAlpha ≤ (281711864031/500000000000:ℝ) := by
  suffices hh : (563423728061/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,2] middleAlpha) ≤ (281711864031/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1774863127331/1000000000000:ℝ) (1774863127333/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_009.1, bound_009.2]
  · norm_num
  · norm_num

private theorem bound_011 : (12190727447/31250000000:ℝ) ≤ prefixEval [2,1,1,3,2] middleAlpha ∧ prefixEval [2,1,1,3,2] middleAlpha ≤ (78020655661/200000000000:ℝ) := by
  suffices hh : (12190727447/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,2] middleAlpha) ≤ (78020655661/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2563423728061/1000000000000:ℝ) (1281711864031/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_010.1, bound_010.2]
  · norm_num
  · norm_num

private theorem bound_012 : (208734883/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,2] ∧ middleWidth [2,1,1,3,2] ≤ (41746977/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_005.2, bound_011.1])]
  constructor <;> linarith only [bound_005.1, bound_005.2, bound_011.1, bound_011.2]

private theorem bound_013 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2] middleBeta ∧ prefixEval [1,2] middleBeta ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2] middleBeta) ∧ 1 / (1 + prefixEval [2] middleBeta) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_001.1, bound_001.2]
  · norm_num
  · norm_num

private theorem bound_014 : (287979054337/500000000000:ℝ) ≤ prefixEval [1,1,2] middleBeta ∧ prefixEval [1,1,2] middleBeta ≤ (143989527169/250000000000:ℝ) := by
  suffices hh : (287979054337/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2] middleBeta) ∧ 1 / (1 + prefixEval [1,2] middleBeta) ≤ (143989527169/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1736237384173/1000000000000:ℝ) (69449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_013.1, bound_013.2]
  · norm_num
  · norm_num

private theorem bound_015 : (12131408463/31250000000:ℝ) ≤ prefixEval [2,1,1,2] middleBeta ∧ prefixEval [2,1,1,2] middleBeta ≤ (194102535409/500000000000:ℝ) := by
  suffices hh : (12131408463/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2] middleBeta) ≤ (194102535409/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1287979054337/500000000000:ℝ) (643989527169/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_014.1, bound_014.2]
  · norm_num
  · norm_num

private theorem bound_016 : (227883607047/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2] middleBeta ∧ prefixEval [4,2,1,1,2] middleBeta ≤ (28485450881/125000000000:ℝ) := by
  suffices hh : (227883607047/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2] middleBeta) ≤ (28485450881/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (137131408463/31250000000:ℝ) (2194102535409/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_015.1, bound_015.2]
  · norm_num
  · norm_num

private theorem bound_017 : (346802583749/500000000000:ℝ) ≤ prefixEval [1,2] middleAlpha ∧ prefixEval [1,2] middleAlpha ≤ (693605167499/1000000000000:ℝ) := by
  suffices hh : (346802583749/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2] middleAlpha) ∧ 1 / (1 + prefixEval [2] middleAlpha) ≤ (693605167499/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (180217803813/125000000000:ℝ) (288348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_007.1, bound_007.2]
  · norm_num
  · norm_num

private theorem bound_018 : (590456393963/1000000000000:ℝ) ≤ prefixEval [1,1,2] middleAlpha ∧ prefixEval [1,1,2] middleAlpha ≤ (118091278793/200000000000:ℝ) := by
  suffices hh : (590456393963/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2] middleAlpha) ∧ 1 / (1 + prefixEval [1,2] middleAlpha) ≤ (118091278793/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (846802583749/500000000000:ℝ) (1693605167499/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_017.1, bound_017.2]
  · norm_num
  · norm_num

private theorem bound_019 : (386032361837/1000000000000:ℝ) ≤ prefixEval [2,1,1,2] middleAlpha ∧ prefixEval [2,1,1,2] middleAlpha ≤ (386032361839/1000000000000:ℝ) := by
  suffices hh : (386032361837/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2] middleAlpha) ≤ (386032361839/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2590456393963/1000000000000:ℝ) (518091278793/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_018.1, bound_018.2]
  · norm_num
  · norm_num

private theorem bound_020 : (56999123439/250000000000:ℝ) ≤ prefixEval [4,2,1,1,2] middleAlpha ∧ prefixEval [4,2,1,1,2] middleAlpha ≤ (227996493757/1000000000000:ℝ) := by
  suffices hh : (56999123439/250000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2] middleAlpha) ≤ (227996493757/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4386032361837/1000000000000:ℝ) (4386032361839/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_019.1, bound_019.2]
  · norm_num
  · norm_num

private theorem bound_021 : (28221677/250000000000:ℝ) ≤ middleWidth [4,2,1,1,2] ∧ middleWidth [4,2,1,1,2] ≤ (11288671/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_016.2, bound_020.1])]
  constructor <;> linarith only [bound_016.1, bound_016.2, bound_020.1, bound_020.2]

private theorem bound_022 : middleWidth [4,2,1,1,2] ≤ middleWidth [2,1,1,3,2] := by linarith only [bound_021.2, bound_012.1]

private theorem bound_023 : middleNormalized (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) = (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_022, ite_true]

private theorem bound_024 : (10550504633/40000000000:ℝ) ≤ prefixEval [3] middleBeta ∧ prefixEval [3] middleBeta ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + middleBeta) ∧ 1 / (3 + middleBeta) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (1895643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_025 : (55217803813/125000000000:ℝ) ≤ prefixEval [2,3] middleBeta ∧ prefixEval [2,3] middleBeta ≤ (88348486101/200000000000:ℝ) := by
  suffices hh : (55217803813/125000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleBeta) ∧ 1 / (2 + prefixEval [3] middleBeta) ≤ (88348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (90550504633/40000000000:ℝ) (2263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_026 : (36318813079/125000000000:ℝ) ≤ prefixEval [3,2,3] middleBeta ∧ prefixEval [3,2,3] middleBeta ≤ (145275252317/500000000000:ℝ) := by
  suffices hh : (36318813079/125000000000:ℝ) ≤ 1 / (3 + prefixEval [2,3] middleBeta) ∧ 1 / (3 + prefixEval [2,3] middleBeta) ≤ (145275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (430217803813/125000000000:ℝ) (688348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_025.1, bound_025.2]
  · norm_num
  · norm_num

private theorem bound_027 : (774863127331/1000000000000:ℝ) ≤ prefixEval [1,3,2,3] middleBeta ∧ prefixEval [1,3,2,3] middleBeta ≤ (774863127333/1000000000000:ℝ) := by
  suffices hh : (774863127331/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,3] middleBeta) ∧ 1 / (1 + prefixEval [3,2,3] middleBeta) ≤ (774863127333/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (161318813079/125000000000:ℝ) (645275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_026.1, bound_026.2]
  · norm_num
  · norm_num

private theorem bound_028 : (563423728061/1000000000000:ℝ) ≤ prefixEval [1,1,3,2,3] middleBeta ∧ prefixEval [1,1,3,2,3] middleBeta ≤ (281711864031/500000000000:ℝ) := by
  suffices hh : (563423728061/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2,3] middleBeta) ≤ (281711864031/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1774863127331/1000000000000:ℝ) (1774863127333/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_027.1, bound_027.2]
  · norm_num
  · norm_num

private theorem bound_029 : (12190727447/31250000000:ℝ) ≤ prefixEval [2,1,1,3,2,3] middleBeta ∧ prefixEval [2,1,1,3,2,3] middleBeta ≤ (78020655661/200000000000:ℝ) := by
  suffices hh : (12190727447/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2,3] middleBeta) ≤ (78020655661/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2563423728061/1000000000000:ℝ) (1281711864031/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_028.1, bound_028.2]
  · norm_num
  · norm_num

private theorem bound_030 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3] middleAlpha ∧ prefixEval [3] middleAlpha ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + middleAlpha) ∧ 1 / (3 + middleAlpha) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (1631881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_031 : (2167885537/5000000000:ℝ) ≤ prefixEval [2,3] middleAlpha ∧ prefixEval [2,3] middleAlpha ≤ (433577107401/1000000000000:ℝ) := by
  suffices hh : (2167885537/5000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleAlpha) ∧ 1 / (2 + prefixEval [3] middleAlpha) ≤ (433577107401/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2306394832501/1000000000000:ℝ) (1153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_030.1, bound_030.2]
  · norm_num
  · norm_num

private theorem bound_032 : (291241457151/1000000000000:ℝ) ≤ prefixEval [3,2,3] middleAlpha ∧ prefixEval [3,2,3] middleAlpha ≤ (568830971/1953125000:ℝ) := by
  suffices hh : (291241457151/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [2,3] middleAlpha) ∧ 1 / (3 + prefixEval [2,3] middleAlpha) ≤ (568830971/1953125000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (17167885537/5000000000:ℝ) (3433577107401/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_031.1, bound_031.2]
  · norm_num
  · norm_num

private theorem bound_033 : (387224246271/500000000000:ℝ) ≤ prefixEval [1,3,2,3] middleAlpha ∧ prefixEval [1,3,2,3] middleAlpha ≤ (189074339/244140625:ℝ) := by
  suffices hh : (387224246271/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,2,3] middleAlpha) ≤ (189074339/244140625:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1291241457151/1000000000000:ℝ) (2521955971/1953125000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_032.1, bound_032.2]
  · norm_num
  · norm_num

private theorem bound_034 : (70444422887/125000000000:ℝ) ≤ prefixEval [1,1,3,2,3] middleAlpha ∧ prefixEval [1,1,3,2,3] middleAlpha ≤ (563555383097/1000000000000:ℝ) := by
  suffices hh : (70444422887/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,2,3] middleAlpha) ≤ (563555383097/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (887224246271/500000000000:ℝ) (433214964/244140625:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_033.1, bound_033.2]
  · norm_num
  · norm_num

private theorem bound_035 : (78016648799/200000000000:ℝ) ≤ prefixEval [2,1,1,3,2,3] middleAlpha ∧ prefixEval [2,1,1,3,2,3] middleAlpha ≤ (97520810999/250000000000:ℝ) := by
  suffices hh : (78016648799/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,2,3] middleAlpha) ≤ (97520810999/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (320444422887/125000000000:ℝ) (2563555383097/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_034.1, bound_034.2]
  · norm_num
  · norm_num

private theorem bound_036 : (5008577/250000000000:ℝ) ≤ middleWidth [2,1,1,3,2,3] ∧ middleWidth [2,1,1,3,2,3] ≤ (2003431/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_029.1, bound_035.2])]
  constructor <;> linarith only [bound_029.1, bound_029.2, bound_035.1, bound_035.2]

private theorem bound_037 : (346802583749/500000000000:ℝ) ≤ prefixEval [1,2,3] middleBeta ∧ prefixEval [1,2,3] middleBeta ≤ (693605167499/1000000000000:ℝ) := by
  suffices hh : (346802583749/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleBeta) ∧ 1 / (1 + prefixEval [2,3] middleBeta) ≤ (693605167499/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (180217803813/125000000000:ℝ) (288348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_025.1, bound_025.2]
  · norm_num
  · norm_num

private theorem bound_038 : (590456393963/1000000000000:ℝ) ≤ prefixEval [1,1,2,3] middleBeta ∧ prefixEval [1,1,2,3] middleBeta ≤ (118091278793/200000000000:ℝ) := by
  suffices hh : (590456393963/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,3] middleBeta) ∧ 1 / (1 + prefixEval [1,2,3] middleBeta) ≤ (118091278793/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (846802583749/500000000000:ℝ) (1693605167499/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_037.1, bound_037.2]
  · norm_num
  · norm_num

private theorem bound_039 : (386032361837/1000000000000:ℝ) ≤ prefixEval [2,1,1,2,3] middleBeta ∧ prefixEval [2,1,1,2,3] middleBeta ≤ (386032361839/1000000000000:ℝ) := by
  suffices hh : (386032361837/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,3] middleBeta) ≤ (386032361839/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2590456393963/1000000000000:ℝ) (518091278793/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_038.1, bound_038.2]
  · norm_num
  · norm_num

private theorem bound_040 : (56999123439/250000000000:ℝ) ≤ prefixEval [4,2,1,1,2,3] middleBeta ∧ prefixEval [4,2,1,1,2,3] middleBeta ≤ (227996493757/1000000000000:ℝ) := by
  suffices hh : (56999123439/250000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2,3] middleBeta) ≤ (227996493757/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4386032361837/1000000000000:ℝ) (4386032361839/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_039.1, bound_039.2]
  · norm_num
  · norm_num

private theorem bound_041 : (697555781853/1000000000000:ℝ) ≤ prefixEval [1,2,3] middleAlpha ∧ prefixEval [1,2,3] middleAlpha ≤ (348777890927/500000000000:ℝ) := by
  suffices hh : (697555781853/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,3] middleAlpha) ≤ (348777890927/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (7167885537/5000000000:ℝ) (1433577107401/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_031.1, bound_031.2]
  · norm_num
  · norm_num

private theorem bound_042 : (58908226209/100000000000:ℝ) ≤ prefixEval [1,1,2,3] middleAlpha ∧ prefixEval [1,1,2,3] middleAlpha ≤ (147270565523/250000000000:ℝ) := by
  suffices hh : (58908226209/100000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,2,3] middleAlpha) ≤ (147270565523/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1697555781853/1000000000000:ℝ) (848777890927/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_041.1, bound_041.2]
  · norm_num
  · norm_num

private theorem bound_043 : (96559311251/250000000000:ℝ) ≤ prefixEval [2,1,1,2,3] middleAlpha ∧ prefixEval [2,1,1,2,3] middleAlpha ≤ (77247449001/200000000000:ℝ) := by
  suffices hh : (96559311251/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2,3] middleAlpha) ≤ (77247449001/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (258908226209/100000000000:ℝ) (647270565523/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_042.1, bound_042.2]
  · norm_num
  · norm_num

private theorem bound_044 : (113992921967/500000000000:ℝ) ≤ prefixEval [4,2,1,1,2,3] middleAlpha ∧ prefixEval [4,2,1,1,2,3] middleAlpha ≤ (45597168787/200000000000:ℝ) := by
  suffices hh : (113992921967/500000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2,3] middleAlpha) ≤ (45597168787/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1096559311251/250000000000:ℝ) (877247449001/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_043.1, bound_043.2]
  · norm_num
  · norm_num

private theorem bound_045 : (10649821/1000000000000:ℝ) ≤ middleWidth [4,2,1,1,2,3] ∧ middleWidth [4,2,1,1,2,3] ≤ (10649823/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_040.1, bound_044.2])]
  constructor <;> linarith only [bound_040.1, bound_040.2, bound_044.1, bound_044.2]

private theorem bound_046 : ¬ (middleWidth [2,1,1,3,2,3] ≤ (7/5:ℝ) * middleWidth [4,2,1,1,2,3]) := by linarith only [bound_036.1, bound_045.2]

private theorem bound_047 : (45753175473/62500000000:ℝ) ≤ middleRho ∧ middleRho ≤ (732050807569/1000000000000:ℝ) := by
  dsimp only [middleRho]
  constructor <;> linarith only [sqrt_3_bounds.1, sqrt_3_bounds.2]

private theorem bound_048 : (267949192431/1000000000000:ℝ) ≤ prefixEval [3] middleRho ∧ prefixEval [3] middleRho ≤ (16746824527/62500000000:ℝ) := by
  suffices hh : (267949192431/1000000000000:ℝ) ≤ 1 / (3 + middleRho) ∧ 1 / (3 + middleRho) ≤ (16746824527/62500000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (233253175473/62500000000:ℝ) (3732050807569/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_047.1, bound_047.2]
  · norm_num
  · norm_num

private theorem bound_049 : (440926985197/1000000000000:ℝ) ≤ prefixEval [2,3] middleRho ∧ prefixEval [2,3] middleRho ≤ (220463492599/500000000000:ℝ) := by
  suffices hh : (440926985197/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [3] middleRho) ∧ 1 / (2 + prefixEval [3] middleRho) ≤ (220463492599/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2267949192431/1000000000000:ℝ) (141746824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_050 : (173499422641/250000000000:ℝ) ≤ prefixEval [1,2,3] middleRho ∧ prefixEval [1,2,3] middleRho ≤ (346998845283/500000000000:ℝ) := by
  suffices hh : (173499422641/250000000000:ℝ) ≤ 1 / (1 + prefixEval [2,3] middleRho) ∧ 1 / (1 + prefixEval [2,3] middleRho) ≤ (346998845283/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1440926985197/1000000000000:ℝ) (720463492599/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_049.1, bound_049.2]
  · norm_num
  · norm_num

private theorem bound_051 : (14757989423/25000000000:ℝ) ≤ prefixEval [1,1,2,3] middleRho ∧ prefixEval [1,1,2,3] middleRho ≤ (295159788461/500000000000:ℝ) := by
  suffices hh : (14757989423/25000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,3] middleRho) ∧ 1 / (1 + prefixEval [1,2,3] middleRho) ≤ (295159788461/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (423499422641/250000000000:ℝ) (846998845283/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_050.1, bound_050.2]
  · norm_num
  · norm_num

private theorem bound_052 : (15442110061/40000000000:ℝ) ≤ prefixEval [2,1,1,2,3] middleRho ∧ prefixEval [2,1,1,2,3] middleRho ≤ (193026375763/500000000000:ℝ) := by
  suffices hh : (15442110061/40000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,2,3] middleRho) ≤ (193026375763/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (64757989423/25000000000:ℝ) (1295159788461/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_051.1, bound_051.2]
  · norm_num
  · norm_num

private theorem bound_053 : (1781214327/7812500000:ℝ) ≤ prefixEval [4,2,1,1,2,3] middleRho ∧ prefixEval [4,2,1,1,2,3] middleRho ≤ (227995433857/1000000000000:ℝ) := by
  suffices hh : (1781214327/7812500000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,2,3] middleRho) ≤ (227995433857/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (175442110061/40000000000:ℝ) (2193026375763/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_052.1, bound_052.2]
  · norm_num
  · norm_num

private theorem bound_054 : middleE3 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,3,2] middleAlpha + prefixEval [4,2,1,1,2,3] middleRho := by
  norm_num [middleE3, bound_046]

private theorem bound_055 : (28863116951/6250000000:ℝ) ≤ middleE3 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) ∧ middleE3 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) ≤ (2309049356081/500000000000:ℝ) := by
  rw [bound_054]
  constructor <;> linarith only [bound_011.1, bound_011.2, bound_053.1, bound_053.2]

private theorem bound_056 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1,3] middleBeta ∧ prefixEval [1,3] middleBeta ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleBeta) ∧ 1 / (1 + prefixEval [3] middleBeta) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (1263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_057 : (71651513899/200000000000:ℝ) ≤ prefixEval [2,1,3] middleBeta ∧ prefixEval [2,1,3] middleBeta ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,3] middleBeta) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (2791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_056.1, bound_056.2]
  · norm_num
  · norm_num

private theorem bound_058 : (148886733567/500000000000:ℝ) ≤ prefixEval [3,2,1,3] middleBeta ∧ prefixEval [3,2,1,3] middleBeta ≤ (59554693427/200000000000:ℝ) := by
  suffices hh : (148886733567/500000000000:ℝ) ≤ 1 / (3 + prefixEval [2,1,3] middleBeta) ∧ 1 / (3 + prefixEval [2,1,3] middleBeta) ≤ (59554693427/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (671651513899/200000000000:ℝ) (419782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_057.1, bound_057.2]
  · norm_num
  · norm_num

private theorem bound_059 : (96318813079/125000000000:ℝ) ≤ prefixEval [1,3,2,1,3] middleBeta ∧ prefixEval [1,3,2,1,3] middleBeta ≤ (385275252317/500000000000:ℝ) := by
  suffices hh : (96318813079/125000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [3,2,1,3] middleBeta) ≤ (385275252317/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (648886733567/500000000000:ℝ) (259554693427/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_058.1, bound_058.2]
  · norm_num
  · norm_num

private theorem bound_060 : (564796088777/1000000000000:ℝ) ≤ prefixEval [1,1,3,2,1,3] middleBeta ∧ prefixEval [1,1,3,2,1,3] middleBeta ≤ (282398044389/500000000000:ℝ) := by
  suffices hh : (564796088777/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3,2,1,3] middleBeta) ≤ (282398044389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (221318813079/125000000000:ℝ) (885275252317/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_059.1, bound_059.2]
  · norm_num
  · norm_num

private theorem bound_061 : (19494727171/50000000000:ℝ) ≤ prefixEval [2,1,1,3,2,1,3] middleBeta ∧ prefixEval [2,1,1,3,2,1,3] middleBeta ≤ (389894543421/1000000000000:ℝ) := by
  suffices hh : (19494727171/50000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3,2,1,3] middleBeta) ≤ (389894543421/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2564796088777/1000000000000:ℝ) (1282398044389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_060.1, bound_060.2]
  · norm_num
  · norm_num

private theorem bound_062 : (76546536707/100000000000:ℝ) ≤ prefixEval [1,3] middleAlpha ∧ prefixEval [1,3] middleAlpha ≤ (765465367071/1000000000000:ℝ) := by
  suffices hh : (76546536707/100000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleAlpha) ∧ 1 / (1 + prefixEval [3] middleAlpha) ≤ (765465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1306394832501/1000000000000:ℝ) (653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_030.1, bound_030.2]
  · norm_num
  · norm_num

private theorem bound_063 : (180801396377/500000000000:ℝ) ≤ prefixEval [2,1,3] middleAlpha ∧ prefixEval [2,1,3] middleAlpha ≤ (90400698189/250000000000:ℝ) := by
  suffices hh : (180801396377/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,3] middleAlpha) ≤ (90400698189/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (276546536707/100000000000:ℝ) (2765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_062.1, bound_062.2]
  · norm_num
  · norm_num

private theorem bound_064 : (297477144579/1000000000000:ℝ) ≤ prefixEval [3,2,1,3] middleAlpha ∧ prefixEval [3,2,1,3] middleAlpha ≤ (14873857229/50000000000:ℝ) := by
  suffices hh : (297477144579/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [2,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [2,1,3] middleAlpha) ≤ (14873857229/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1680801396377/500000000000:ℝ) (840400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_063.1, bound_063.2]
  · norm_num
  · norm_num

private theorem bound_065 : (770726485763/1000000000000:ℝ) ≤ prefixEval [1,3,2,1,3] middleAlpha ∧ prefixEval [1,3,2,1,3] middleAlpha ≤ (192681621441/250000000000:ℝ) := by
  suffices hh : (770726485763/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [3,2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [3,2,1,3] middleAlpha) ≤ (192681621441/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1297477144579/1000000000000:ℝ) (64873857229/50000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_064.1, bound_064.2]
  · norm_num
  · norm_num

private theorem bound_066 : (282369978661/500000000000:ℝ) ≤ prefixEval [1,1,3,2,1,3] middleAlpha ∧ prefixEval [1,1,3,2,1,3] middleAlpha ≤ (564739957323/1000000000000:ℝ) := by
  suffices hh : (282369978661/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3,2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3,2,1,3] middleAlpha) ≤ (564739957323/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1770726485763/1000000000000:ℝ) (442681621441/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_065.1, bound_065.2]
  · norm_num
  · norm_num

private theorem bound_067 : (48737884573/125000000000:ℝ) ≤ prefixEval [2,1,1,3,2,1,3] middleAlpha ∧ prefixEval [2,1,1,3,2,1,3] middleAlpha ≤ (77980615317/200000000000:ℝ) := by
  suffices hh : (48737884573/125000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3,2,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3,2,1,3] middleAlpha) ≤ (77980615317/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1282369978661/500000000000:ℝ) (2564739957323/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_066.1, bound_066.2]
  · norm_num
  · norm_num

private theorem bound_068 : (8533163/1000000000000:ℝ) ≤ middleWidth [2,1,1,3,2,1,3] ∧ middleWidth [2,1,1,3,2,1,3] ≤ (1706633/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_061.2, bound_067.1])]
  constructor <;> linarith only [bound_061.1, bound_061.2, bound_067.1, bound_067.2]

private theorem bound_069 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2,1,3] middleBeta ∧ prefixEval [1,2,1,3] middleBeta ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [2,1,3] middleBeta) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_057.1, bound_057.2]
  · norm_num
  · norm_num

private theorem bound_070 : (287979054337/500000000000:ℝ) ≤ prefixEval [1,1,2,1,3] middleBeta ∧ prefixEval [1,1,2,1,3] middleBeta ≤ (143989527169/250000000000:ℝ) := by
  suffices hh : (287979054337/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,2,1,3] middleBeta) ≤ (143989527169/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1736237384173/1000000000000:ℝ) (69449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_069.1, bound_069.2]
  · norm_num
  · norm_num

private theorem bound_071 : (12131408463/31250000000:ℝ) ≤ prefixEval [2,1,1,2,1,3] middleBeta ∧ prefixEval [2,1,1,2,1,3] middleBeta ≤ (194102535409/500000000000:ℝ) := by
  suffices hh : (12131408463/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,2,1,3] middleBeta) ≤ (194102535409/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1287979054337/500000000000:ℝ) (643989527169/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_070.1, bound_070.2]
  · norm_num
  · norm_num

private theorem bound_072 : (227883607047/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,3] middleBeta ∧ prefixEval [4,2,1,1,2,1,3] middleBeta ≤ (28485450881/125000000000:ℝ) := by
  suffices hh : (227883607047/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,3] middleBeta) ∧ 1 / (4 + prefixEval [2,1,1,2,1,3] middleBeta) ≤ (28485450881/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (137131408463/31250000000:ℝ) (2194102535409/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_071.1, bound_071.2]
  · norm_num
  · norm_num

private theorem bound_073 : (734428575881/1000000000000:ℝ) ≤ prefixEval [1,2,1,3] middleAlpha ∧ prefixEval [1,2,1,3] middleAlpha ≤ (734428575883/1000000000000:ℝ) := by
  suffices hh : (734428575881/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,1,3] middleAlpha) ≤ (734428575883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (680801396377/500000000000:ℝ) (340400698189/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_063.1, bound_063.2]
  · norm_num
  · norm_num

private theorem bound_074 : (57655876633/100000000000:ℝ) ≤ prefixEval [1,1,2,1,3] middleAlpha ∧ prefixEval [1,1,2,1,3] middleAlpha ≤ (144139691583/250000000000:ℝ) := by
  suffices hh : (57655876633/100000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,2,1,3] middleAlpha) ≤ (144139691583/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1734428575881/1000000000000:ℝ) (1734428575883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_073.1, bound_073.2]
  · norm_num
  · norm_num

private theorem bound_075 : (194057285451/500000000000:ℝ) ≤ prefixEval [2,1,1,2,1,3] middleAlpha ∧ prefixEval [2,1,1,2,1,3] middleAlpha ≤ (388114570903/1000000000000:ℝ) := by
  suffices hh : (194057285451/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,2,1,3] middleAlpha) ≤ (388114570903/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (257655876633/100000000000:ℝ) (644139691583/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_074.1, bound_074.2]
  · norm_num
  · norm_num

private theorem bound_076 : (227888306889/1000000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,3] middleAlpha ∧ prefixEval [4,2,1,1,2,1,3] middleAlpha ≤ (22788830689/100000000000:ℝ) := by
  suffices hh : (227888306889/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [2,1,1,2,1,3] middleAlpha) ≤ (22788830689/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2194057285451/500000000000:ℝ) (4388114570903/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_075.1, bound_075.2]
  · norm_num
  · norm_num

private theorem bound_077 : (4699841/1000000000000:ℝ) ≤ middleWidth [4,2,1,1,2,1,3] ∧ middleWidth [4,2,1,1,2,1,3] ≤ (4699843/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_072.2, bound_076.1])]
  constructor <;> linarith only [bound_072.1, bound_072.2, bound_076.1, bound_076.2]

private theorem bound_078 : ¬ (middleWidth [2,1,1,3,2,1,3] ≤ (7/5:ℝ) * middleWidth [4,2,1,1,2,1,3]) := by linarith only [bound_068.1, bound_077.2]

private theorem bound_079 : (394337567297/500000000000:ℝ) ≤ prefixEval [1,3] middleRho ∧ prefixEval [1,3] middleRho ≤ (157735026919/200000000000:ℝ) := by
  suffices hh : (394337567297/500000000000:ℝ) ≤ 1 / (1 + prefixEval [3] middleRho) ∧ 1 / (1 + prefixEval [3] middleRho) ≤ (157735026919/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1267949192431/1000000000000:ℝ) (79246824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_080 : (358593221417/1000000000000:ℝ) ≤ prefixEval [2,1,3] middleRho ∧ prefixEval [2,1,3] middleRho ≤ (179296610709/500000000000:ℝ) := by
  suffices hh : (358593221417/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,3] middleRho) ∧ 1 / (2 + prefixEval [1,3] middleRho) ≤ (179296610709/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1394337567297/500000000000:ℝ) (557735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_079.1, bound_079.2]
  · norm_num
  · norm_num

private theorem bound_081 : (368027745257/500000000000:ℝ) ≤ prefixEval [1,2,1,3] middleRho ∧ prefixEval [1,2,1,3] middleRho ≤ (147211098103/200000000000:ℝ) := by
  suffices hh : (368027745257/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,3] middleRho) ∧ 1 / (1 + prefixEval [2,1,3] middleRho) ≤ (147211098103/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1358593221417/1000000000000:ℝ) (679296610709/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_080.1, bound_080.2]
  · norm_num
  · norm_num

private theorem bound_082 : (57601845417/100000000000:ℝ) ≤ prefixEval [1,1,2,1,3] middleRho ∧ prefixEval [1,1,2,1,3] middleRho ≤ (576018454171/1000000000000:ℝ) := by
  suffices hh : (57601845417/100000000000:ℝ) ≤ 1 / (1 + prefixEval [1,2,1,3] middleRho) ∧ 1 / (1 + prefixEval [1,2,1,3] middleRho) ≤ (576018454171/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (868027745257/500000000000:ℝ) (347211098103/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_081.1, bound_081.2]
  · norm_num
  · norm_num

private theorem bound_083 : (97048994193/250000000000:ℝ) ≤ prefixEval [2,1,1,2,1,3] middleRho ∧ prefixEval [2,1,1,2,1,3] middleRho ≤ (388195976773/1000000000000:ℝ) := by
  suffices hh : (97048994193/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,2,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,2,1,3] middleRho) ≤ (388195976773/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (257601845417/100000000000:ℝ) (2576018454171/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_082.1, bound_082.2]
  · norm_num
  · norm_num

private theorem bound_084 : (22788407931/100000000000:ℝ) ≤ prefixEval [4,2,1,1,2,1,3] middleRho ∧ prefixEval [4,2,1,1,2,1,3] middleRho ≤ (227884079311/1000000000000:ℝ) := by
  suffices hh : (22788407931/100000000000:ℝ) ≤ 1 / (4 + prefixEval [2,1,1,2,1,3] middleRho) ∧ 1 / (4 + prefixEval [2,1,1,2,1,3] middleRho) ≤ (227884079311/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1097048994193/250000000000:ℝ) (4388195976773/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_083.1, bound_083.2]
  · norm_num
  · norm_num

private theorem bound_085 : middleE13 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,3,2] middleBeta + prefixEval [4,2,1,1,2,1,3] middleRho := by
  norm_num [middleE13, bound_078]

private theorem bound_086 : (461777862273/100000000000:ℝ) ≤ middleE13 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) ∧ middleE13 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) ≤ (1154444655683/250000000000:ℝ) := by
  rw [bound_085]
  constructor <;> linarith only [bound_005.1, bound_005.2, bound_084.1, bound_084.2]

private theorem bound_087 : middleEqualBounds (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) = (middleE13 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore), middleE3 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_023]

private theorem bound_088 : middleBounds (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) = (middleE13 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore), middleE3 (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_023, bound_087]

private theorem bound_089 : (111651513899/200000000000:ℝ) ≤ prefixEval [1] middleBeta ∧ prefixEval [1] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + middleBeta) ∧ 1 / (1 + middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (895643923739/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_000.1, bound_000.2]
  · norm_num
  · norm_num

private theorem bound_090 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1] middleBeta ∧ prefixEval [1,1] middleBeta ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1] middleBeta) ∧ 1 / (1 + prefixEval [1] middleBeta) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_089.1, bound_089.2]
  · norm_num
  · norm_num

private theorem bound_091 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1] middleBeta ∧ prefixEval [1,1,1] middleBeta ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1] middleBeta) ∧ 1 / (1 + prefixEval [1,1] middleBeta) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_090.1, bound_090.2]
  · norm_num
  · norm_num

private theorem bound_092 : (383272611851/1000000000000:ℝ) ≤ prefixEval [2,1,1,1] middleBeta ∧ prefixEval [2,1,1,1] middleBeta ≤ (95818152963/250000000000:ℝ) := by
  suffices hh : (383272611851/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1] middleBeta) ≤ (95818152963/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2609108945117/1000000000000:ℝ) (2609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_091.1, bound_091.2]
  · norm_num
  · norm_num

private theorem bound_093 : (791287847477/1000000000000:ℝ) ≤ prefixEval [1] middleAlpha ∧ prefixEval [1] middleAlpha ≤ (791287847479/1000000000000:ℝ) := by
  suffices hh : (791287847477/1000000000000:ℝ) ≤ 1 / (1 + middleAlpha) ∧ 1 / (1 + middleAlpha) ≤ (791287847479/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (50550504633/40000000000:ℝ) (631881307913/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_006.1, bound_006.2]
  · norm_num
  · norm_num

private theorem bound_094 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1] middleAlpha ∧ prefixEval [1,1] middleAlpha ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1] middleAlpha) ∧ 1 / (1 + prefixEval [1] middleAlpha) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_093.1, bound_093.2]
  · norm_num
  · norm_num

private theorem bound_095 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1,1] middleAlpha ∧ prefixEval [1,1,1] middleAlpha ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1] middleAlpha) ∧ 1 / (1 + prefixEval [1,1] middleAlpha) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_094.1, bound_094.2]
  · norm_num
  · norm_num

private theorem bound_096 : (378538039307/1000000000000:ℝ) ≤ prefixEval [2,1,1,1] middleAlpha ∧ prefixEval [2,1,1,1] middleAlpha ≤ (378538039309/1000000000000:ℝ) := by
  suffices hh : (378538039307/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1] middleAlpha) ≤ (378538039309/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (330217803813/125000000000:ℝ) (528348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_095.1, bound_095.2]
  · norm_num
  · norm_num

private theorem bound_097 : (2367286271/500000000000:ℝ) ≤ middleWidth [2,1,1,1] ∧ middleWidth [2,1,1,1] ≤ (946914509/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_092.1, bound_096.2])]
  constructor <;> linarith only [bound_092.1, bound_092.2, bound_096.1, bound_096.2]

private theorem bound_098 : (234534632929/1000000000000:ℝ) ≤ prefixEval [4,3] middleBeta ∧ prefixEval [4,3] middleBeta ≤ (23453463293/100000000000:ℝ) := by
  suffices hh : (234534632929/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3] middleBeta) ∧ 1 / (4 + prefixEval [3] middleBeta) ≤ (23453463293/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (170550504633/40000000000:ℝ) (4263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_099 : (29026599943/125000000000:ℝ) ≤ prefixEval [4,3] middleAlpha ∧ prefixEval [4,3] middleAlpha ≤ (46442559909/200000000000:ℝ) := by
  suffices hh : (29026599943/125000000000:ℝ) ≤ 1 / (4 + prefixEval [3] middleAlpha) ∧ 1 / (4 + prefixEval [3] middleAlpha) ≤ (46442559909/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4306394832501/1000000000000:ℝ) (2153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_030.1, bound_030.2]
  · norm_num
  · norm_num

private theorem bound_100 : (290229173/125000000000:ℝ) ≤ middleWidth [4,3] ∧ middleWidth [4,3] ≤ (1160916693/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_098.1, bound_099.2])]
  constructor <;> linarith only [bound_098.1, bound_098.2, bound_099.1, bound_099.2]

private theorem bound_101 : middleWidth [4,3] ≤ middleWidth [2,1,1,1] := by linarith only [bound_100.2, bound_097.1]

private theorem bound_102 : middleNormalized (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) = (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_101, ite_true]

private theorem bound_103 : (111651513899/200000000000:ℝ) ≤ prefixEval [1,1,3] middleBeta ∧ prefixEval [1,1,3] middleBeta ≤ (69782196187/125000000000:ℝ) := by
  suffices hh : (111651513899/200000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,3] middleBeta) ≤ (69782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1791287847477/1000000000000:ℝ) (1791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_056.1, bound_056.2]
  · norm_num
  · norm_num

private theorem bound_104 : (80217803813/125000000000:ℝ) ≤ prefixEval [1,1,1,3] middleBeta ∧ prefixEval [1,1,1,3] middleBeta ≤ (128348486101/200000000000:ℝ) := by
  suffices hh : (80217803813/125000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,3] middleBeta) ≤ (128348486101/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (311651513899/200000000000:ℝ) (194782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_103.1, bound_103.2]
  · norm_num
  · norm_num

private theorem bound_105 : (378538039307/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,1,3] middleBeta ≤ (378538039309/1000000000000:ℝ) := by
  suffices hh : (378538039307/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1,3] middleBeta) ≤ (378538039309/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (330217803813/125000000000:ℝ) (528348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_104.1, bound_104.2]
  · norm_num
  · norm_num

private theorem bound_106 : (566422892599/1000000000000:ℝ) ≤ prefixEval [1,1,3] middleAlpha ∧ prefixEval [1,1,3] middleAlpha ≤ (2832114463/5000000000:ℝ) := by
  suffices hh : (566422892599/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,3] middleAlpha) ≤ (2832114463/5000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (176546536707/100000000000:ℝ) (1765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_062.1, bound_062.2]
  · norm_num
  · norm_num

private theorem bound_107 : (159599301811/250000000000:ℝ) ≤ prefixEval [1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,3] middleAlpha ≤ (319198603623/500000000000:ℝ) := by
  suffices hh : (159599301811/250000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,3] middleAlpha) ≤ (319198603623/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1566422892599/1000000000000:ℝ) (7832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_106.1, bound_106.2]
  · norm_num
  · norm_num

private theorem bound_108 : (379017987607/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,1,3] middleAlpha ≤ (47377248451/125000000000:ℝ) := by
  suffices hh : (379017987607/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1,3] middleAlpha) ≤ (47377248451/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (659599301811/250000000000:ℝ) (1319198603623/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_107.1, bound_107.2]
  · norm_num
  · norm_num

private theorem bound_109 : (239974149/500000000000:ℝ) ≤ middleWidth [2,1,1,1,3] ∧ middleWidth [2,1,1,1,3] ≤ (479948301/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_105.2, bound_108.1])]
  constructor <;> linarith only [bound_105.1, bound_105.2, bound_108.1, bound_108.2]

private theorem bound_110 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3,3] middleBeta ∧ prefixEval [3,3] middleBeta ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleBeta) ∧ 1 / (3 + prefixEval [3] middleBeta) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (3263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_024.1, bound_024.2]
  · norm_num
  · norm_num

private theorem bound_111 : (29026599943/125000000000:ℝ) ≤ prefixEval [4,3,3] middleBeta ∧ prefixEval [4,3,3] middleBeta ≤ (46442559909/200000000000:ℝ) := by
  suffices hh : (29026599943/125000000000:ℝ) ≤ 1 / (4 + prefixEval [3,3] middleBeta) ∧ 1 / (4 + prefixEval [3,3] middleBeta) ≤ (46442559909/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4306394832501/1000000000000:ℝ) (2153197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_110.1, bound_110.2]
  · norm_num
  · norm_num

private theorem bound_112 : (151222109073/500000000000:ℝ) ≤ prefixEval [3,3] middleAlpha ∧ prefixEval [3,3] middleAlpha ≤ (302444218147/1000000000000:ℝ) := by
  suffices hh : (151222109073/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleAlpha) ∧ 1 / (3 + prefixEval [3] middleAlpha) ≤ (302444218147/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3306394832501/1000000000000:ℝ) (1653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_030.1, bound_030.2]
  · norm_num
  · norm_num

private theorem bound_113 : (116213011639/500000000000:ℝ) ≤ prefixEval [4,3,3] middleAlpha ∧ prefixEval [4,3,3] middleAlpha ≤ (232426023279/1000000000000:ℝ) := by
  suffices hh : (116213011639/500000000000:ℝ) ≤ 1 / (4 + prefixEval [3,3] middleAlpha) ∧ 1 / (4 + prefixEval [3,3] middleAlpha) ≤ (232426023279/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2151222109073/500000000000:ℝ) (4302444218147/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_112.1, bound_112.2]
  · norm_num
  · norm_num

private theorem bound_114 : (213223733/1000000000000:ℝ) ≤ middleWidth [4,3,3] ∧ middleWidth [4,3,3] ≤ (42644747/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_111.2, bound_113.1])]
  constructor <;> linarith only [bound_111.1, bound_111.2, bound_113.1, bound_113.2]

private theorem bound_115 : ¬ (middleWidth [2,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,3,3]) := by linarith only [bound_109.1, bound_114.2]

private theorem bound_116 : (153001154717/500000000000:ℝ) ≤ prefixEval [3,3] middleRho ∧ prefixEval [3,3] middleRho ≤ (61200461887/200000000000:ℝ) := by
  suffices hh : (153001154717/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3] middleRho) ∧ 1 / (3 + prefixEval [3] middleRho) ≤ (61200461887/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3267949192431/1000000000000:ℝ) (204246824527/62500000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_048.1, bound_048.2]
  · norm_num
  · norm_num

private theorem bound_117 : (23223396741/100000000000:ℝ) ≤ prefixEval [4,3,3] middleRho ∧ prefixEval [4,3,3] middleRho ≤ (232233967411/1000000000000:ℝ) := by
  suffices hh : (23223396741/100000000000:ℝ) ≤ 1 / (4 + prefixEval [3,3] middleRho) ∧ 1 / (4 + prefixEval [3,3] middleRho) ≤ (232233967411/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2153001154717/500000000000:ℝ) (861200461887/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_116.1, bound_116.2]
  · norm_num
  · norm_num

private theorem bound_118 : middleE3 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,1] middleAlpha + prefixEval [4,3,3] middleRho := by
  norm_num [middleE3, bound_115]

private theorem bound_119 : (4610772006717/1000000000000:ℝ) ≤ middleE3 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) ∧ middleE3 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) ≤ (14408662521/3125000000:ℝ) := by
  rw [bound_118]
  constructor <;> linarith only [bound_096.1, bound_096.2, bound_117.1, bound_117.2]

private theorem bound_120 : (609108945117/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleBeta ∧ prefixEval [1,1,1,1,3] middleBeta ≤ (609108945119/1000000000000:ℝ) := by
  suffices hh : (609108945117/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [1,1,1,3] middleBeta) ≤ (609108945119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (205217803813/125000000000:ℝ) (328348486101/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_104.1, bound_104.2]
  · norm_num
  · norm_num

private theorem bound_121 : (383272611851/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1,3] middleBeta ∧ prefixEval [2,1,1,1,1,3] middleBeta ≤ (95818152963/250000000000:ℝ) := by
  suffices hh : (383272611851/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,1,1,3] middleBeta) ≤ (95818152963/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2609108945117/1000000000000:ℝ) (2609108945119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_120.1, bound_120.2]
  · norm_num
  · norm_num

private theorem bound_122 : (610352602883/1000000000000:ℝ) ≤ prefixEval [1,1,1,1,3] middleAlpha ∧ prefixEval [1,1,1,1,3] middleAlpha ≤ (122070520577/200000000000:ℝ) := by
  suffices hh : (610352602883/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [1,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [1,1,1,3] middleAlpha) ≤ (122070520577/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (409599301811/250000000000:ℝ) (819198603623/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_107.1, bound_107.2]
  · norm_num
  · norm_num

private theorem bound_123 : (383090008183/1000000000000:ℝ) ≤ prefixEval [2,1,1,1,1,3] middleAlpha ∧ prefixEval [2,1,1,1,1,3] middleAlpha ≤ (47886251023/125000000000:ℝ) := by
  suffices hh : (383090008183/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,1,1,3] middleAlpha) ≤ (47886251023/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2610352602883/1000000000000:ℝ) (522070520577/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_122.1, bound_122.2]
  · norm_num
  · norm_num

private theorem bound_124 : (182603667/1000000000000:ℝ) ≤ middleWidth [2,1,1,1,1,3] ∧ middleWidth [2,1,1,1,1,3] ≤ (182603669/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_121.1, bound_123.2])]
  constructor <;> linarith only [bound_121.1, bound_121.2, bound_123.1, bound_123.2]

private theorem bound_125 : (10550504633/40000000000:ℝ) ≤ prefixEval [3,1,3] middleBeta ∧ prefixEval [3,1,3] middleBeta ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,3] middleBeta) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (3791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_056.1, bound_056.2]
  · norm_num
  · norm_num

private theorem bound_126 : (234534632929/1000000000000:ℝ) ≤ prefixEval [4,3,1,3] middleBeta ∧ prefixEval [4,3,1,3] middleBeta ≤ (23453463293/100000000000:ℝ) := by
  suffices hh : (234534632929/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,3] middleBeta) ∧ 1 / (4 + prefixEval [3,1,3] middleBeta) ≤ (23453463293/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (170550504633/40000000000:ℝ) (4263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_125.1, bound_125.2]
  · norm_num
  · norm_num

private theorem bound_127 : (265571424117/1000000000000:ℝ) ≤ prefixEval [3,1,3] middleAlpha ∧ prefixEval [3,1,3] middleAlpha ≤ (265571424119/1000000000000:ℝ) := by
  suffices hh : (265571424117/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,3] middleAlpha) ≤ (265571424119/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (376546536707/100000000000:ℝ) (3765465367071/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_062.1, bound_062.2]
  · norm_num
  · norm_num

private theorem bound_128 : (234435178917/1000000000000:ℝ) ≤ prefixEval [4,3,1,3] middleAlpha ∧ prefixEval [4,3,1,3] middleAlpha ≤ (117217589459/500000000000:ℝ) := by
  suffices hh : (234435178917/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [3,1,3] middleAlpha) ≤ (117217589459/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4265571424117/1000000000000:ℝ) (4265571424119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_127.1, bound_127.2]
  · norm_num
  · norm_num

private theorem bound_129 : (99454011/1000000000000:ℝ) ≤ middleWidth [4,3,1,3] ∧ middleWidth [4,3,1,3] ≤ (99454013/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_126.1, bound_128.2])]
  constructor <;> linarith only [bound_126.1, bound_126.2, bound_128.1, bound_128.2]

private theorem bound_130 : ¬ (middleWidth [2,1,1,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,3,1,3]) := by linarith only [bound_124.1, bound_129.2]

private theorem bound_131 : (52788901897/200000000000:ℝ) ≤ prefixEval [3,1,3] middleRho ∧ prefixEval [3,1,3] middleRho ≤ (131972254743/500000000000:ℝ) := by
  suffices hh : (52788901897/200000000000:ℝ) ≤ 1 / (3 + prefixEval [1,3] middleRho) ∧ 1 / (3 + prefixEval [1,3] middleRho) ≤ (131972254743/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1894337567297/500000000000:ℝ) (757735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_079.1, bound_079.2]
  · norm_num
  · norm_num

private theorem bound_132 : (234524628023/1000000000000:ℝ) ≤ prefixEval [4,3,1,3] middleRho ∧ prefixEval [4,3,1,3] middleRho ≤ (29315578503/125000000000:ℝ) := by
  suffices hh : (234524628023/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,3] middleRho) ∧ 1 / (4 + prefixEval [3,1,3] middleRho) ≤ (29315578503/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (852788901897/200000000000:ℝ) (2131972254743/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_131.1, bound_131.2]
  · norm_num
  · norm_num

private theorem bound_133 : middleE13 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) = 4 + prefixEval [2,1,1,1] middleBeta + prefixEval [4,3,1,3] middleRho := by
  norm_num [middleE13, bound_130]

private theorem bound_134 : (2308898619937/500000000000:ℝ) ≤ middleE13 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) ∧ middleE13 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) ≤ (1154449309969/250000000000:ℝ) := by
  rw [bound_133]
  constructor <;> linarith only [bound_092.1, bound_092.2, bound_132.1, bound_132.2]

private theorem bound_135 : middleEqualBounds (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) = (middleE3 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore), middleE13 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_102]

private theorem bound_136 : middleBounds (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) = (middleE3 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore), middleE13 (⟨[2,1,1,1],[4,3]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_102, bound_135]

private theorem bound_137 : (1975307177/500000000000:ℝ) ≤ middleWidth [3,3] ∧ middleWidth [3,3] ≤ (987653589/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_110.1, bound_112.2])]
  constructor <;> linarith only [bound_110.1, bound_110.2, bound_112.1, bound_112.2]

private theorem bound_138 : middleWidth [3,3] ≤ middleWidth [3,3] := le_rfl

private theorem bound_139 : middleNormalized (⟨[3,3],[3,3]⟩ : MiddleCore) = (⟨[3,3],[3,3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_138, ite_true]

private theorem bound_140 : (151222109073/500000000000:ℝ) ≤ prefixEval [3,3,3] middleBeta ∧ prefixEval [3,3,3] middleBeta ≤ (302444218147/1000000000000:ℝ) := by
  suffices hh : (151222109073/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3,3] middleBeta) ∧ 1 / (3 + prefixEval [3,3] middleBeta) ≤ (302444218147/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3306394832501/1000000000000:ℝ) (1653197416251/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_110.1, bound_110.2]
  · norm_num
  · norm_num

private theorem bound_141 : (302806023037/1000000000000:ℝ) ≤ prefixEval [3,3,3] middleAlpha ∧ prefixEval [3,3,3] middleAlpha ≤ (151403011519/500000000000:ℝ) := by
  suffices hh : (302806023037/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3,3] middleAlpha) ∧ 1 / (3 + prefixEval [3,3] middleAlpha) ≤ (151403011519/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1651222109073/500000000000:ℝ) (3302444218147/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_112.1, bound_112.2]
  · norm_num
  · norm_num

private theorem bound_142 : (36180489/100000000000:ℝ) ≤ middleWidth [3,3,3] ∧ middleWidth [3,3,3] ≤ (90451223/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_140.2, bound_141.1])]
  constructor <;> linarith only [bound_140.1, bound_140.2, bound_141.1, bound_141.2]

private theorem bound_143 : middleWidth [3,3,3] ≤ (7/5:ℝ) * middleWidth [3,3,3] := by linarith only [bound_142.2, bound_142.1]

private theorem bound_144 : (302480127477/1000000000000:ℝ) ≤ prefixEval [3,3,3] middleRho ∧ prefixEval [3,3,3] middleRho ≤ (151240063739/500000000000:ℝ) := by
  suffices hh : (302480127477/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3,3] middleRho) ∧ 1 / (3 + prefixEval [3,3] middleRho) ≤ (151240063739/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1653001154717/500000000000:ℝ) (661200461887/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_116.1, bound_116.2]
  · norm_num
  · norm_num

private theorem bound_145 : (75808724429/250000000000:ℝ) ≤ prefixEval [3,3,2] middleBeta ∧ prefixEval [3,3,2] middleBeta ≤ (303234897717/1000000000000:ℝ) := by
  suffices hh : (75808724429/250000000000:ℝ) ≤ 1 / (3 + prefixEval [3,2] middleBeta) ∧ 1 / (3 + prefixEval [3,2] middleBeta) ≤ (303234897717/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1648886733567/500000000000:ℝ) (659554693427/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_146 : middleE3 (⟨[3,3],[3,3]⟩ : MiddleCore) = 4 + prefixEval [3,3,3] middleRho + prefixEval [3,3,2] middleBeta := by
  norm_num [middleE3, bound_143]

private theorem bound_147 : (4605715025193/1000000000000:ℝ) ≤ middleE3 (⟨[3,3],[3,3]⟩ : MiddleCore) ∧ middleE3 (⟨[3,3],[3,3]⟩ : MiddleCore) ≤ (921143005039/200000000000:ℝ) := by
  rw [bound_146]
  constructor <;> linarith only [bound_144.1, bound_144.2, bound_145.1, bound_145.2]

private theorem bound_148 : (306394832501/1000000000000:ℝ) ≤ prefixEval [3,3,1,3] middleBeta ∧ prefixEval [3,3,1,3] middleBeta ≤ (153197416251/500000000000:ℝ) := by
  suffices hh : (306394832501/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3,1,3] middleBeta) ∧ 1 / (3 + prefixEval [3,1,3] middleBeta) ≤ (153197416251/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (130550504633/40000000000:ℝ) (3263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_125.1, bound_125.2]
  · norm_num
  · norm_num

private theorem bound_149 : (153112559813/500000000000:ℝ) ≤ prefixEval [3,3,1,3] middleAlpha ∧ prefixEval [3,3,1,3] middleAlpha ≤ (306225119627/1000000000000:ℝ) := by
  suffices hh : (153112559813/500000000000:ℝ) ≤ 1 / (3 + prefixEval [3,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [3,1,3] middleAlpha) ≤ (306225119627/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3265571424117/1000000000000:ℝ) (3265571424119/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_127.1, bound_127.2]
  · norm_num
  · norm_num

private theorem bound_150 : (84856437/500000000000:ℝ) ≤ middleWidth [3,3,1,3] ∧ middleWidth [3,3,1,3] ≤ (42428219/250000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_148.1, bound_149.2])]
  constructor <;> linarith only [bound_148.1, bound_148.2, bound_149.1, bound_149.2]

private theorem bound_151 : middleWidth [3,3,1,3] ≤ (7/5:ℝ) * middleWidth [3,3,1,3] := by linarith only [bound_150.2, bound_150.1]

private theorem bound_152 : (306377757677/1000000000000:ℝ) ≤ prefixEval [3,3,1,3] middleRho ∧ prefixEval [3,3,1,3] middleRho ≤ (153188878839/500000000000:ℝ) := by
  suffices hh : (306377757677/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [3,1,3] middleRho) ∧ 1 / (3 + prefixEval [3,1,3] middleRho) ≤ (153188878839/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (652788901897/200000000000:ℝ) (1631972254743/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_131.1, bound_131.2]
  · norm_num
  · norm_num

private theorem bound_153 : (267648946567/1000000000000:ℝ) ≤ prefixEval [3,1,2] middleBeta ∧ prefixEval [3,1,2] middleBeta ≤ (33456118321/125000000000:ℝ) := by
  suffices hh : (267648946567/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,2] middleBeta) ∧ 1 / (3 + prefixEval [1,2] middleBeta) ≤ (33456118321/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3736237384173/1000000000000:ℝ) (149449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_013.1, bound_013.2]
  · norm_num
  · norm_num

private theorem bound_154 : (38253803283/125000000000:ℝ) ≤ prefixEval [3,3,1,2] middleBeta ∧ prefixEval [3,3,1,2] middleBeta ≤ (61206085253/200000000000:ℝ) := by
  suffices hh : (38253803283/125000000000:ℝ) ≤ 1 / (3 + prefixEval [3,1,2] middleBeta) ∧ 1 / (3 + prefixEval [3,1,2] middleBeta) ≤ (61206085253/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3267648946567/1000000000000:ℝ) (408456118321/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_153.1, bound_153.2]
  · norm_num
  · norm_num

private theorem bound_155 : middleE13 (⟨[3,3],[3,3]⟩ : MiddleCore) = 4 + prefixEval [3,3,1,3] middleRho + prefixEval [3,3,1,2] middleBeta := by
  norm_num [middleE13, bound_151]

private theorem bound_156 : (4612408183941/1000000000000:ℝ) ≤ middleE13 (⟨[3,3],[3,3]⟩ : MiddleCore) ∧ middleE13 (⟨[3,3],[3,3]⟩ : MiddleCore) ≤ (4612408183943/1000000000000:ℝ) := by
  rw [bound_155]
  constructor <;> linarith only [bound_152.1, bound_152.2, bound_154.1, bound_154.2]

private theorem bound_157 : middleEqualBounds (⟨[3,3],[3,3]⟩ : MiddleCore) = (middleE3 (⟨[3,3],[3,3]⟩ : MiddleCore), middleE13 (⟨[3,3],[3,3]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_139]

private theorem bound_158 : middleBounds (⟨[3,3],[3,3]⟩ : MiddleCore) = (middleE3 (⟨[3,3],[3,3]⟩ : MiddleCore), middleE13 (⟨[3,3],[3,3]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_139, bound_157]

private theorem bound_159 : (36546536707/100000000000:ℝ) ≤ prefixEval [2,1,2] middleBeta ∧ prefixEval [2,1,2] middleBeta ≤ (365465367071/1000000000000:ℝ) := by
  suffices hh : (36546536707/100000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2] middleBeta) ∧ 1 / (2 + prefixEval [1,2] middleBeta) ≤ (365465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2736237384173/1000000000000:ℝ) (109449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_013.1, bound_013.2]
  · norm_num
  · norm_num

private theorem bound_160 : (371249659031/1000000000000:ℝ) ≤ prefixEval [2,1,2] middleAlpha ∧ prefixEval [2,1,2] middleAlpha ≤ (46406207379/125000000000:ℝ) := by
  suffices hh : (371249659031/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2] middleAlpha) ∧ 1 / (2 + prefixEval [1,2] middleAlpha) ≤ (46406207379/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1346802583749/500000000000:ℝ) (2693605167499/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_017.1, bound_017.2]
  · norm_num
  · norm_num

private theorem bound_161 : (144607299/25000000000:ℝ) ≤ middleWidth [2,1,2] ∧ middleWidth [2,1,2] ≤ (2892145981/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_159.2, bound_160.1])]
  constructor <;> linarith only [bound_159.1, bound_159.2, bound_160.1, bound_160.2]

private theorem bound_162 : middleWidth [4,3] ≤ middleWidth [2,1,2] := by linarith only [bound_100.2, bound_161.1]

private theorem bound_163 : middleNormalized (⟨[2,1,2],[4,3]⟩ : MiddleCore) = (⟨[2,1,2],[4,3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_162, ite_true]

private theorem bound_164 : (281036428777/1000000000000:ℝ) ≤ prefixEval [3,1] middleBeta ∧ prefixEval [3,1] middleBeta ≤ (140518214389/500000000000:ℝ) := by
  suffices hh : (281036428777/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1] middleBeta) ∧ 1 / (3 + prefixEval [1] middleBeta) ≤ (140518214389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (711651513899/200000000000:ℝ) (444782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_089.1, bound_089.2]
  · norm_num
  · norm_num

private theorem bound_165 : (116794147473/500000000000:ℝ) ≤ prefixEval [4,3,1] middleBeta ∧ prefixEval [4,3,1] middleBeta ≤ (233588294947/1000000000000:ℝ) := by
  suffices hh : (116794147473/500000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1] middleBeta) ∧ 1 / (4 + prefixEval [3,1] middleBeta) ≤ (233588294947/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4281036428777/1000000000000:ℝ) (2140518214389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_164.1, bound_164.2]
  · norm_num
  · norm_num

private theorem bound_166 : (10550504633/40000000000:ℝ) ≤ prefixEval [3,1] middleAlpha ∧ prefixEval [3,1] middleAlpha ≤ (263762615827/1000000000000:ℝ) := by
  suffices hh : (10550504633/40000000000:ℝ) ≤ 1 / (3 + prefixEval [1] middleAlpha) ∧ 1 / (3 + prefixEval [1] middleAlpha) ≤ (263762615827/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3791287847477/1000000000000:ℝ) (3791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_093.1, bound_093.2]
  · norm_num
  · norm_num

private theorem bound_167 : (234534632929/1000000000000:ℝ) ≤ prefixEval [4,3,1] middleAlpha ∧ prefixEval [4,3,1] middleAlpha ≤ (23453463293/100000000000:ℝ) := by
  suffices hh : (234534632929/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1] middleAlpha) ∧ 1 / (4 + prefixEval [3,1] middleAlpha) ≤ (23453463293/100000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (170550504633/40000000000:ℝ) (4263762615827/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_166.1, bound_166.2]
  · norm_num
  · norm_num

private theorem bound_168 : (473168991/500000000000:ℝ) ≤ middleWidth [4,3,1] ∧ middleWidth [4,3,1] ≤ (14786531/15625000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_165.2, bound_167.1])]
  constructor <;> linarith only [bound_165.1, bound_165.2, bound_167.1, bound_167.2]

private theorem bound_169 : middleWidth [4,3,1] ≤ middleWidth [2,1,2] := by linarith only [bound_168.2, bound_161.1]

private theorem bound_170 : middleNormalized (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) = (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_169, ite_true]

private theorem bound_171 : (371249659031/1000000000000:ℝ) ≤ prefixEval [2,1,2,3] middleBeta ∧ prefixEval [2,1,2,3] middleBeta ≤ (46406207379/125000000000:ℝ) := by
  suffices hh : (371249659031/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,3] middleBeta) ∧ 1 / (2 + prefixEval [1,2,3] middleBeta) ≤ (46406207379/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1346802583749/500000000000:ℝ) (2693605167499/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_037.1, bound_037.2]
  · norm_num
  · norm_num

private theorem bound_172 : (185352978931/500000000000:ℝ) ≤ prefixEval [2,1,2,3] middleAlpha ∧ prefixEval [2,1,2,3] middleAlpha ≤ (370705957863/1000000000000:ℝ) := by
  suffices hh : (185352978931/500000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,2,3] middleAlpha) ≤ (370705957863/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2697555781853/1000000000000:ℝ) (1348777890927/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_041.1, bound_041.2]
  · norm_num
  · norm_num

private theorem bound_173 : (33981323/62500000000:ℝ) ≤ middleWidth [2,1,2,3] ∧ middleWidth [2,1,2,3] ≤ (54370117/100000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_171.1, bound_172.2])]
  constructor <;> linarith only [bound_171.1, bound_171.2, bound_172.1, bound_172.2]

private theorem bound_174 : ¬ (middleWidth [2,1,2,3] ≤ (7/5:ℝ) * middleWidth [4,3,1,3]) := by linarith only [bound_173.1, bound_129.2]

private theorem bound_175 : middleE3 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) = 4 + prefixEval [2,1,2] middleAlpha + prefixEval [4,3,1,3] middleRho := by
  norm_num [middleE3, bound_174]

private theorem bound_176 : (2302887143527/500000000000:ℝ) ≤ middleE3 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) ∧ middleE3 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) ≤ (287860892941/62500000000:ℝ) := by
  rw [bound_175]
  constructor <;> linarith only [bound_160.1, bound_160.2, bound_132.1, bound_132.2]

private theorem bound_177 : (36546536707/100000000000:ℝ) ≤ prefixEval [2,1,2,1,3] middleBeta ∧ prefixEval [2,1,2,1,3] middleBeta ≤ (365465367071/1000000000000:ℝ) := by
  suffices hh : (36546536707/100000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,2,1,3] middleBeta) ≤ (365465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2736237384173/1000000000000:ℝ) (109449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_069.1, bound_069.2]
  · norm_num
  · norm_num

private theorem bound_178 : (91426780061/250000000000:ℝ) ≤ prefixEval [2,1,2,1,3] middleAlpha ∧ prefixEval [2,1,2,1,3] middleAlpha ≤ (73141424049/200000000000:ℝ) := by
  suffices hh : (91426780061/250000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,2,1,3] middleAlpha) ≤ (73141424049/200000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2734428575881/1000000000000:ℝ) (2734428575883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_073.1, bound_073.2]
  · norm_num
  · norm_num

private theorem bound_179 : (241753173/1000000000000:ℝ) ≤ middleWidth [2,1,2,1,3] ∧ middleWidth [2,1,2,1,3] ≤ (9670127/40000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_177.2, bound_178.1])]
  constructor <;> linarith only [bound_177.1, bound_177.2, bound_178.1, bound_178.2]

private theorem bound_180 : (281036428777/1000000000000:ℝ) ≤ prefixEval [3,1,1,3] middleBeta ∧ prefixEval [3,1,1,3] middleBeta ≤ (140518214389/500000000000:ℝ) := by
  suffices hh : (281036428777/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleBeta) ∧ 1 / (3 + prefixEval [1,1,3] middleBeta) ≤ (140518214389/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (711651513899/200000000000:ℝ) (444782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_103.1, bound_103.2]
  · norm_num
  · norm_num

private theorem bound_181 : (116794147473/500000000000:ℝ) ≤ prefixEval [4,3,1,1,3] middleBeta ∧ prefixEval [4,3,1,1,3] middleBeta ≤ (233588294947/1000000000000:ℝ) := by
  suffices hh : (116794147473/500000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,1,3] middleBeta) ∧ 1 / (4 + prefixEval [3,1,1,3] middleBeta) ≤ (233588294947/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4281036428777/1000000000000:ℝ) (2140518214389/500000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_180.1, bound_180.2]
  · norm_num
  · norm_num

private theorem bound_182 : (280392996039/1000000000000:ℝ) ≤ prefixEval [3,1,1,3] middleAlpha ∧ prefixEval [3,1,1,3] middleAlpha ≤ (7009824901/25000000000:ℝ) := by
  suffices hh : (280392996039/1000000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (3 + prefixEval [1,1,3] middleAlpha) ≤ (7009824901/25000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (3566422892599/1000000000000:ℝ) (17832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_106.1, bound_106.2]
  · norm_num
  · norm_num

private theorem bound_183 : (1460146301/6250000000:ℝ) ≤ prefixEval [4,3,1,1,3] middleAlpha ∧ prefixEval [4,3,1,1,3] middleAlpha ≤ (233623408161/1000000000000:ℝ) := by
  suffices hh : (1460146301/6250000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,1,3] middleAlpha) ∧ 1 / (4 + prefixEval [3,1,1,3] middleAlpha) ≤ (233623408161/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4280392996039/1000000000000:ℝ) (107009824901/25000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_182.1, bound_182.2]
  · norm_num
  · norm_num

private theorem bound_184 : (35113213/1000000000000:ℝ) ≤ middleWidth [4,3,1,1,3] ∧ middleWidth [4,3,1,1,3] ≤ (7022643/200000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_181.2, bound_183.1])]
  constructor <;> linarith only [bound_181.1, bound_181.2, bound_183.1, bound_183.2]

private theorem bound_185 : ¬ (middleWidth [2,1,2,1,3] ≤ (7/5:ℝ) * middleWidth [4,3,1,1,3]) := by linarith only [bound_179.1, bound_184.2]

private theorem bound_186 : (279536507401/500000000000:ℝ) ≤ prefixEval [1,1,3] middleRho ∧ prefixEval [1,1,3] middleRho ≤ (559073014803/1000000000000:ℝ) := by
  suffices hh : (279536507401/500000000000:ℝ) ≤ 1 / (1 + prefixEval [1,3] middleRho) ∧ 1 / (1 + prefixEval [1,3] middleRho) ≤ (559073014803/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (894337567297/500000000000:ℝ) (357735026919/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_079.1, bound_079.2]
  · norm_num
  · norm_num

private theorem bound_187 : (14048601923/50000000000:ℝ) ≤ prefixEval [3,1,1,3] middleRho ∧ prefixEval [3,1,1,3] middleRho ≤ (280972038461/1000000000000:ℝ) := by
  suffices hh : (14048601923/50000000000:ℝ) ≤ 1 / (3 + prefixEval [1,1,3] middleRho) ∧ 1 / (3 + prefixEval [1,1,3] middleRho) ≤ (280972038461/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1779536507401/500000000000:ℝ) (3559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_186.1, bound_186.2]
  · norm_num
  · norm_num

private theorem bound_188 : (233591808359/1000000000000:ℝ) ≤ prefixEval [4,3,1,1,3] middleRho ∧ prefixEval [4,3,1,1,3] middleRho ≤ (5839795209/25000000000:ℝ) := by
  suffices hh : (233591808359/1000000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,1,3] middleRho) ∧ 1 / (4 + prefixEval [3,1,1,3] middleRho) ≤ (5839795209/25000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (214048601923/50000000000:ℝ) (4280972038461/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_187.1, bound_187.2]
  · norm_num
  · norm_num

private theorem bound_189 : middleE13 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) = 4 + prefixEval [2,1,2] middleBeta + prefixEval [4,3,1,1,3] middleRho := by
  norm_num [middleE13, bound_185]

private theorem bound_190 : (4599057175429/1000000000000:ℝ) ≤ middleE13 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) ∧ middleE13 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) ≤ (4599057175431/1000000000000:ℝ) := by
  rw [bound_189]
  constructor <;> linarith only [bound_159.1, bound_159.2, bound_188.1, bound_188.2]

private theorem bound_191 : middleEqualBounds (⟨[2,1,2],[4,3,1]⟩ : MiddleCore) = (middleE13 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore), middleE3 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_170]

private theorem bound_192 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1] middleBeta ∧ prefixEval [2,1] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1] middleBeta) ∧ 1 / (2 + prefixEval [1] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_089.1, bound_089.2]
  · norm_num
  · norm_num

private theorem bound_193 : (359481785611/500000000000:ℝ) ≤ prefixEval [1,2,1] middleBeta ∧ prefixEval [1,2,1] middleBeta ≤ (89870446403/125000000000:ℝ) := by
  suffices hh : (359481785611/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1] middleBeta) ∧ 1 / (1 + prefixEval [2,1] middleBeta) ≤ (89870446403/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1390891054881/1000000000000:ℝ) (1390891054883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_192.1, bound_192.2]
  · norm_num
  · norm_num

private theorem bound_194 : (73557440091/200000000000:ℝ) ≤ prefixEval [2,1,2,1] middleBeta ∧ prefixEval [2,1,2,1] middleBeta ≤ (45973400057/125000000000:ℝ) := by
  suffices hh : (73557440091/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1] middleBeta) ∧ 1 / (2 + prefixEval [1,2,1] middleBeta) ≤ (45973400057/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1359481785611/500000000000:ℝ) (339870446403/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_193.1, bound_193.2]
  · norm_num
  · norm_num

private theorem bound_195 : (71651513899/200000000000:ℝ) ≤ prefixEval [2,1] middleAlpha ∧ prefixEval [2,1] middleAlpha ≤ (44782196187/125000000000:ℝ) := by
  suffices hh : (71651513899/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1] middleAlpha) ∧ 1 / (2 + prefixEval [1] middleAlpha) ≤ (44782196187/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2791287847477/1000000000000:ℝ) (2791287847479/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_093.1, bound_093.2]
  · norm_num
  · norm_num

private theorem bound_196 : (736237384173/1000000000000:ℝ) ≤ prefixEval [1,2,1] middleAlpha ∧ prefixEval [1,2,1] middleAlpha ≤ (29449495367/40000000000:ℝ) := by
  suffices hh : (736237384173/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1] middleAlpha) ∧ 1 / (1 + prefixEval [2,1] middleAlpha) ≤ (29449495367/40000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (271651513899/200000000000:ℝ) (169782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_195.1, bound_195.2]
  · norm_num
  · norm_num

private theorem bound_197 : (36546536707/100000000000:ℝ) ≤ prefixEval [2,1,2,1] middleAlpha ∧ prefixEval [2,1,2,1] middleAlpha ≤ (365465367071/1000000000000:ℝ) := by
  suffices hh : (36546536707/100000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1] middleAlpha) ∧ 1 / (2 + prefixEval [1,2,1] middleAlpha) ≤ (365465367071/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2736237384173/1000000000000:ℝ) (109449495367/40000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_196.1, bound_196.2]
  · norm_num
  · norm_num

private theorem bound_198 : (290229173/125000000000:ℝ) ≤ middleWidth [2,1,2,1] ∧ middleWidth [2,1,2,1] ≤ (1160916693/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_194.1, bound_197.2])]
  constructor <;> linarith only [bound_194.1, bound_194.2, bound_197.1, bound_197.2]

private theorem bound_199 : middleWidth [4,3] ≤ middleWidth [2,1,2,1] := by
  apply le_of_eq
  rw [middle_width_identity, middle_width_identity]
  congr 1
  norm_num [middleParameter, middleCD, middleAlpha, middleBeta]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
  nlinarith

private theorem bound_200 : middleNormalized (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) = (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_199, ite_true]

private theorem bound_201 : middleWidth [2,1,2,1,3] ≤ (7/5:ℝ) * middleWidth [4,3,3] := by linarith only [bound_179.2, bound_114.1]

private theorem bound_202 : (3654896633/10000000000:ℝ) ≤ prefixEval [2,1,2,1,3] middleRho ∧ prefixEval [2,1,2,1,3] middleRho ≤ (365489663301/1000000000000:ℝ) := by
  suffices hh : (3654896633/10000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,2,1,3] middleRho) ≤ (365489663301/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1368027745257/500000000000:ℝ) (547211098103/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_081.1, bound_081.2]
  · norm_num
  · norm_num

private theorem bound_203 : (116339310069/500000000000:ℝ) ≤ prefixEval [4,3,2] middleBeta ∧ prefixEval [4,3,2] middleBeta ≤ (232678620139/1000000000000:ℝ) := by
  suffices hh : (116339310069/500000000000:ℝ) ≤ 1 / (4 + prefixEval [3,2] middleBeta) ∧ 1 / (4 + prefixEval [3,2] middleBeta) ≤ (232678620139/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2148886733567/500000000000:ℝ) (859554693427/200000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_002.1, bound_002.2]
  · norm_num
  · norm_num

private theorem bound_204 : middleE3 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) = 4 + prefixEval [2,1,2,1,3] middleRho + prefixEval [4,3,2] middleBeta := by
  norm_num [middleE3, bound_201]

private theorem bound_205 : (2299084141719/500000000000:ℝ) ≤ middleE3 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) ∧ middleE3 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) ≤ (57477103543/12500000000:ℝ) := by
  rw [bound_204]
  constructor <;> linarith only [bound_202.1, bound_202.2, bound_203.1, bound_203.2]

private theorem bound_206 : (390891054881/1000000000000:ℝ) ≤ prefixEval [2,1,1,3] middleBeta ∧ prefixEval [2,1,1,3] middleBeta ≤ (390891054883/1000000000000:ℝ) := by
  suffices hh : (390891054881/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,1,3] middleBeta) ≤ (390891054883/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (511651513899/200000000000:ℝ) (319782196187/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_103.1, bound_103.2]
  · norm_num
  · norm_num

private theorem bound_207 : (359481785611/500000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleBeta ∧ prefixEval [1,2,1,1,3] middleBeta ≤ (89870446403/125000000000:ℝ) := by
  suffices hh : (359481785611/500000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleBeta) ∧ 1 / (1 + prefixEval [2,1,1,3] middleBeta) ≤ (89870446403/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1390891054881/1000000000000:ℝ) (1390891054883/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_206.1, bound_206.2]
  · norm_num
  · norm_num

private theorem bound_208 : (73557440091/200000000000:ℝ) ≤ prefixEval [2,1,2,1,1,3] middleBeta ∧ prefixEval [2,1,2,1,1,3] middleBeta ≤ (45973400057/125000000000:ℝ) := by
  suffices hh : (73557440091/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1,1,3] middleBeta) ∧ 1 / (2 + prefixEval [1,2,1,1,3] middleBeta) ≤ (45973400057/125000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1359481785611/500000000000:ℝ) (339870446403/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_207.1, bound_207.2]
  · norm_num
  · norm_num

private theorem bound_209 : (77929479423/200000000000:ℝ) ≤ prefixEval [2,1,1,3] middleAlpha ∧ prefixEval [2,1,1,3] middleAlpha ≤ (97411849279/250000000000:ℝ) := by
  suffices hh : (77929479423/200000000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,1,3] middleAlpha) ≤ (97411849279/250000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2566422892599/1000000000000:ℝ) (12832114463/5000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_106.1, bound_106.2]
  · norm_num
  · norm_num

private theorem bound_210 : (17990175099/25000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleAlpha ∧ prefixEval [1,2,1,1,3] middleAlpha ≤ (719607003961/1000000000000:ℝ) := by
  suffices hh : (17990175099/25000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleAlpha) ∧ 1 / (1 + prefixEval [2,1,1,3] middleAlpha) ≤ (719607003961/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (277929479423/200000000000:ℝ) (347411849279/250000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_209.1, bound_209.2]
  · norm_num
  · norm_num

private theorem bound_211 : (367700185557/1000000000000:ℝ) ≤ prefixEval [2,1,2,1,1,3] middleAlpha ∧ prefixEval [2,1,2,1,1,3] middleAlpha ≤ (183850092779/500000000000:ℝ) := by
  suffices hh : (367700185557/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1,1,3] middleAlpha) ∧ 1 / (2 + prefixEval [1,2,1,1,3] middleAlpha) ≤ (183850092779/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (67990175099/25000000000:ℝ) (2719607003961/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_210.1, bound_210.2]
  · norm_num
  · norm_num

private theorem bound_212 : (87014897/1000000000000:ℝ) ≤ middleWidth [2,1,2,1,1,3] ∧ middleWidth [2,1,2,1,1,3] ≤ (87014899/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonneg (by linarith only [bound_208.1, bound_211.2])]
  constructor <;> linarith only [bound_208.1, bound_208.2, bound_211.1, bound_211.2]

private theorem bound_213 : middleWidth [2,1,2,1,1,3] ≤ (7/5:ℝ) * middleWidth [4,3,1,3] := by linarith only [bound_212.2, bound_129.1]

private theorem bound_214 : (12211453061/31250000000:ℝ) ≤ prefixEval [2,1,1,3] middleRho ∧ prefixEval [2,1,1,3] middleRho ≤ (390766497953/1000000000000:ℝ) := by
  suffices hh : (12211453061/31250000000:ℝ) ≤ 1 / (2 + prefixEval [1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,1,3] middleRho) ≤ (390766497953/1000000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (1279536507401/500000000000:ℝ) (2559073014803/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_186.1, bound_186.2]
  · norm_num
  · norm_num

private theorem bound_215 : (719027961539/1000000000000:ℝ) ≤ prefixEval [1,2,1,1,3] middleRho ∧ prefixEval [1,2,1,1,3] middleRho ≤ (35951398077/50000000000:ℝ) := by
  suffices hh : (719027961539/1000000000000:ℝ) ≤ 1 / (1 + prefixEval [2,1,1,3] middleRho) ∧ 1 / (1 + prefixEval [2,1,1,3] middleRho) ≤ (35951398077/50000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (43461453061/31250000000:ℝ) (1390766497953/1000000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_214.1, bound_214.2]
  · norm_num
  · norm_num

private theorem bound_216 : (367778490749/1000000000000:ℝ) ≤ prefixEval [2,1,2,1,1,3] middleRho ∧ prefixEval [2,1,2,1,1,3] middleRho ≤ (1471113963/4000000000:ℝ) := by
  suffices hh : (367778490749/1000000000000:ℝ) ≤ 1 / (2 + prefixEval [1,2,1,1,3] middleRho) ∧ 1 / (2 + prefixEval [1,2,1,1,3] middleRho) ≤ (1471113963/4000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (2719027961539/1000000000000:ℝ) (135951398077/50000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_215.1, bound_215.2]
  · norm_num
  · norm_num

private theorem bound_217 : (58580263543/250000000000:ℝ) ≤ prefixEval [4,3,1,2] middleBeta ∧ prefixEval [4,3,1,2] middleBeta ≤ (117160527087/500000000000:ℝ) := by
  suffices hh : (58580263543/250000000000:ℝ) ≤ 1 / (4 + prefixEval [3,1,2] middleBeta) ∧ 1 / (4 + prefixEval [3,1,2] middleBeta) ≤ (117160527087/500000000000:ℝ) by simpa only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one] using hh
  apply inv_est _ (4267648946567/1000000000000:ℝ) (533456118321/125000000000:ℝ) _ _ (by norm_num)
  · constructor <;> linarith only [bound_153.1, bound_153.2]
  · norm_num
  · norm_num

private theorem bound_218 : middleE13 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) = 4 + prefixEval [2,1,2,1,1,3] middleRho + prefixEval [4,3,1,2] middleBeta := by
  norm_num [middleE13, bound_213]

private theorem bound_219 : (4602099544921/1000000000000:ℝ) ≤ middleE13 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) ∧ middleE13 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) ≤ (1150524886231/250000000000:ℝ) := by
  rw [bound_218]
  constructor <;> linarith only [bound_216.1, bound_216.2, bound_217.1, bound_217.2]

private theorem bound_220 : middleEqualBounds (⟨[2,1,2,1],[4,3]⟩ : MiddleCore) = (middleE3 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore), middleE13 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_200]

private theorem bound_221 : middleBounds (⟨[2,1,2],[4,3]⟩ : MiddleCore) = (middleE3 (⟨[2,1,2,1],[4,3]⟩ : MiddleCore), middleE3 (⟨[2,1,2],[4,3,1]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_163, bound_191, bound_220]

private theorem bound_222 : (21316108337/500000000000:ℝ) ≤ middleWidth [3] ∧ middleWidth [3] ≤ (42632216677/1000000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_024.2, bound_030.1])]
  constructor <;> linarith only [bound_024.1, bound_024.2, bound_030.1, bound_030.2]

private theorem bound_223 : middleWidth [3] ≤ middleWidth [3] := le_rfl

private theorem bound_224 : middleNormalized (⟨[3],[3]⟩ : MiddleCore) = (⟨[3],[3]⟩ : MiddleCore) := by
  simp only [middleNormalized, bound_223, ite_true]

private theorem bound_225 : middleWidth [3,3] ≤ (7/5:ℝ) * middleWidth [3,3] := by linarith only [bound_137.2, bound_137.1]

private theorem bound_226 : middleE3 (⟨[3],[3]⟩ : MiddleCore) = 4 + prefixEval [3,3] middleRho + prefixEval [3,2] middleBeta := by
  norm_num [middleE3, bound_225]

private theorem bound_227 : (575471972071/125000000000:ℝ) ≤ middleE3 (⟨[3],[3]⟩ : MiddleCore) ∧ middleE3 (⟨[3],[3]⟩ : MiddleCore) ≤ (460377577657/100000000000:ℝ) := by
  rw [bound_226]
  constructor <;> linarith only [bound_116.1, bound_116.2, bound_002.1, bound_002.2]

private theorem bound_228 : (180880829/100000000000:ℝ) ≤ middleWidth [3,1,3] ∧ middleWidth [3,1,3] ≤ (904404147/500000000000:ℝ) := by
  unfold middleWidth
  rw [abs_of_nonpos (by linarith only [bound_125.2, bound_127.1])]
  constructor <;> linarith only [bound_125.1, bound_125.2, bound_127.1, bound_127.2]

private theorem bound_229 : middleWidth [3,1,3] ≤ (7/5:ℝ) * middleWidth [3,1,3] := by linarith only [bound_228.2, bound_228.1]

private theorem bound_230 : middleE13 (⟨[3],[3]⟩ : MiddleCore) = 4 + prefixEval [3,1,3] middleRho + prefixEval [3,1,2] middleBeta := by
  norm_num [middleE13, bound_229]

private theorem bound_231 : (1132898364013/250000000000:ℝ) ≤ middleE13 (⟨[3],[3]⟩ : MiddleCore) ∧ middleE13 (⟨[3],[3]⟩ : MiddleCore) ≤ (2265796728027/500000000000:ℝ) := by
  rw [bound_230]
  constructor <;> linarith only [bound_131.1, bound_131.2, bound_153.1, bound_153.2]

private theorem bound_232 : middleEqualBounds (⟨[3],[3]⟩ : MiddleCore) = (middleE13 (⟨[3],[3]⟩ : MiddleCore), middleE3 (⟨[3],[3]⟩ : MiddleCore)) := by
  norm_num [middleEqualBounds, bound_224]

private theorem bound_233 : middleBounds (⟨[3],[3]⟩ : MiddleCore) = (middleE13 (⟨[3],[3]⟩ : MiddleCore), middleE3 (⟨[3],[3]⟩ : MiddleCore)) := by
  norm_num [middleBounds, bound_224, bound_232]

private theorem root_10 : middleRootCertificate 10 := by
  change middleRegular (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore)).1 < middleInnerLeft 10 ∧ middleInnerRight 10 < (middleBounds (⟨[2,1,1,3,2],[4,2,1,1,2]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_012.1]
    · linarith only [bound_021.1]
  constructor
  · have h90 : (369813032907/200000000000:ℝ) ≤ middleWidth [2,1,1,3,2] / middleWidth [4,2,1,1,2] ∧ middleWidth [2,1,1,3,2] / middleWidth [4,2,1,1,2] ≤ (462266303753/250000000000:ℝ) := by
      apply div_est _ _ (208734883/1000000000000:ℝ) (41746977/200000000000:ℝ) (28221677/250000000000:ℝ) (11288671/100000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_012 bound_021 <;> norm_num
    simp only [middleRatio, bound_023]
    linarith only [h90.2]
  rw [bound_088]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_086.2]
  · linarith only [bound_055.1]



private theorem root_11 : middleRootCertificate 11 := by
  change middleRegular (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,1,1],[4,3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,1,1],[4,3]⟩ : MiddleCore)).1 < middleInnerLeft 11 ∧ middleInnerRight 11 < (middleBounds (⟨[2,1,1,1],[4,3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_097.1]
    · linarith only [bound_100.1]
  constructor
  · have h58 : (2039152581123/1000000000000:ℝ) ≤ middleWidth [2,1,1,1] / middleWidth [4,3] ∧ middleWidth [2,1,1,1] / middleWidth [4,3] ≤ (509788146043/250000000000:ℝ) := by
      apply div_est _ _ (2367286271/500000000000:ℝ) (946914509/200000000000:ℝ) (290229173/125000000000:ℝ) (1160916693/500000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_097 bound_100 <;> norm_num
    simp only [middleRatio, bound_102]
    linarith only [h58.2]
  rw [bound_136]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_119.2]
  · linarith only [bound_134.1]



private theorem root_12 : middleRootCertificate 12 := by
  change middleRegular (⟨[3,3],[3,3]⟩ : MiddleCore) ∧ middleRatio (⟨[3,3],[3,3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[3,3],[3,3]⟩ : MiddleCore)).1 < middleInnerLeft 12 ∧ middleInnerRight 12 < (middleBounds (⟨[3,3],[3,3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_137.1]
    · linarith only [bound_137.1]
  constructor
  · have h41 : (999999999493/1000000000000:ℝ) ≤ middleWidth [3,3] / middleWidth [3,3] ∧ middleWidth [3,3] / middleWidth [3,3] ≤ (1000000000507/1000000000000:ℝ) := by
      apply div_est _ _ (1975307177/500000000000:ℝ) (987653589/250000000000:ℝ) (1975307177/500000000000:ℝ) (987653589/250000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_137 bound_137 <;> norm_num
    simp only [middleRatio, bound_139]
    linarith only [h41.2]
  rw [bound_158]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_147.2]
  · linarith only [bound_156.1]



private theorem root_13 : middleRootCertificate 13 := by
  change middleRegular (⟨[2,1,2],[4,3]⟩ : MiddleCore) ∧ middleRatio (⟨[2,1,2],[4,3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[2,1,2],[4,3]⟩ : MiddleCore)).1 < middleInnerLeft 13 ∧ middleInnerRight 13 < (middleBounds (⟨[2,1,2],[4,3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_161.1]
    · linarith only [bound_100.1]
  constructor
  · have h108 : (622815141999/250000000000:ℝ) ≤ middleWidth [2,1,2] / middleWidth [4,3] ∧ middleWidth [2,1,2] / middleWidth [4,3] ≤ (498252114201/200000000000:ℝ) := by
      apply div_est _ _ (144607299/25000000000:ℝ) (2892145981/500000000000:ℝ) (290229173/125000000000:ℝ) (1160916693/500000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_161 bound_100 <;> norm_num
    simp only [middleRatio, bound_163]
    linarith only [h108.2]
  rw [bound_221]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_205.2]
  · linarith only [bound_176.1]



private theorem root_14 : middleRootCertificate 14 := by
  change middleRegular (⟨[3],[3]⟩ : MiddleCore) ∧ middleRatio (⟨[3],[3]⟩ : MiddleCore) < (19/5:ℝ) ∧ (middleBounds (⟨[3],[3]⟩ : MiddleCore)).1 < middleInnerLeft 14 ∧ middleInnerRight 14 < (middleBounds (⟨[3],[3]⟩ : MiddleCore)).2
  constructor
  · unfold middleRegular
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num [middleParameter, middleCD]
    · norm_num [middleParameter, middleCD]
    · linarith only [bound_222.1]
    · linarith only [bound_222.1]
  constructor
  · have h33 : (999999999929/1000000000000:ℝ) ≤ middleWidth [3] / middleWidth [3] ∧ middleWidth [3] / middleWidth [3] ≤ (1000000000071/1000000000000:ℝ) := by
      apply div_est _ _ (21316108337/500000000000:ℝ) (42632216677/1000000000000:ℝ) (21316108337/500000000000:ℝ) (42632216677/1000000000000:ℝ) _ _ (by norm_num) (by norm_num) bound_222 bound_222 <;> norm_num
    simp only [middleRatio, bound_224]
    linarith only [h33.2]
  rw [bound_233]
  norm_num [middleInnerLeft, middleInnerRight] 
  constructor
  · linarith only [bound_231.2]
  · linarith only [bound_227.1]


end M8Sep10InitialRoots3Opt

theorem solution : ∀ i : Fin 15, 10 ≤ i.val → i.val < 15 → middleRootCertificate i := by
  intro i hlo hi
  fin_cases i <;> norm_num at hlo <;> norm_num at hi <;> first | exact M8Sep10InitialRoots3Opt.root_10 | exact M8Sep10InitialRoots3Opt.root_11 | exact M8Sep10InitialRoots3Opt.root_12 | exact M8Sep10InitialRoots3Opt.root_13 | exact M8Sep10InitialRoots3Opt.root_14
#print axioms solution
