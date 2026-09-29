-- Prove2me | solution 1 for Freiman.lower_bridge_C_comparison
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:15.439905+00:00
-- url     : https://prove2.me/submissions/a19673bd-cc71-40a7-bef9-019444df832b

import Theorems.Thm_Freiman_lower_initial_family_normalization
import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib
set_option maxHeartbeats 2000000
noncomputable section
namespace OtherBridge
open Freiman
theorem pe_append : ∀ (u v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x)
  | [], v, x => rfl
  | a :: u, v, x => by
      simp only [List.cons_append, prefixEval, pe_append u v x]

theorem wm_eq (w : List ℕ+) : lowerInitialWordMatrix w =
    List.foldl (fun m (d : ℕ) => lowerInitialMatMul m ⟨0,1,1,(d : ℝ)⟩)
      ⟨1,0,0,1⟩ (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerInitialWordMatrix
  rw [hbind]

theorem wm_append (w : List ℕ+) (a : ℕ+) :
    lowerInitialWordMatrix (w ++ [a])
      = lowerInitialMatMul (lowerInitialWordMatrix w) ⟨0,1,1,((a : ℕ) : ℝ)⟩ := by
  rw [wm_eq, wm_eq, List.map_append, List.foldl_append]
  simp


private theorem mat_assoc (a b c : LowerInitialMatrix) :
    lowerInitialMatMul (lowerInitialMatMul a b) c = lowerInitialMatMul a (lowerInitialMatMul b c) := by
  cases a; cases b; cases c
  unfold lowerInitialMatMul
  congr 1 <;> ring

private theorem wm_append_all (u v : List ℕ+) :
    lowerInitialWordMatrix (u ++ v) =
      lowerInitialMatMul (lowerInitialWordMatrix u) (lowerInitialWordMatrix v) := by
  induction v using List.reverseRecOn with
  | nil => simp [wm_eq, lowerInitialMatMul]
  | append_singleton v a ih =>
      rw [← List.append_assoc, wm_append, ih, wm_append, mat_assoc]

private theorem scale_mul (s : ℝ) (a b : LowerInitialMatrix) :
    lowerInitialMatMul (lowerInitialMatScale s a) b = lowerInitialMatScale s (lowerInitialMatMul a b) := by
  cases a; cases b
  unfold lowerInitialMatScale lowerInitialMatMul
  congr 1 <;> ring

private theorem widthDen_scale (s : ℝ) (a : LowerInitialMatrix) :
    lowerBridgeWidthDen (lowerInitialMatScale s a) = s^2 * lowerBridgeWidthDen a := by
  unfold lowerBridgeWidthDen lowerInitialMatDen lowerInitialMatScale
  ring

private theorem alpha_pos : 0 < lowerAlpha := by
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h := Real.sqrt_nonneg 21
  unfold lowerAlpha
  nlinarith

private theorem gap_pos : 0 < lowerBeta - lowerAlpha := by
  have hs : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h := Real.sqrt_nonneg 21
  unfold lowerBeta lowerAlpha
  nlinarith

private theorem beta_pos : 0 < lowerBeta := by linarith [alpha_pos, gap_pos]

abbrev FractionProperty : Prop := ∀ (w : List ℕ+) (t : ℝ), 0 < t →
  prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
  0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
  (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
    (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length

private theorem den_pos (hf : FractionProperty) (w : List ℕ+) :
    0 < lowerBridgeWidthDen (lowerInitialWordMatrix w) :=
  mul_pos (hf w _ alpha_pos).2.1 (hf w _ beta_pos).2.1

private theorem cross_diff (a b x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (a/y-b/x)*(x*y) = a*x-b*y := by
  field_simp
  try ring

private theorem width_formula (hf : FractionProperty) (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) / lowerBridgeWidthDen (lowerInitialWordMatrix w) := by
  obtain ⟨ha, hda, hdet⟩ := hf w _ alpha_pos
  obtain ⟨hb, hdb, _⟩ := hf w _ beta_pos
  have hdiff : prefixEval w lowerBeta - prefixEval w lowerAlpha =
      ((lowerBeta-lowerAlpha) * (-1:ℝ)^w.length) /
        lowerBridgeWidthDen (lowerInitialWordMatrix w) := by
    apply (eq_div_iff (ne_of_gt (den_pos hf w))).2
    rw [ha, hb]
    unfold lowerInitialMatEval lowerBridgeWidthDen lowerInitialMatDen
    unfold lowerInitialMatDen at hda hdb
    rw [cross_diff _ _ _ _ (ne_of_gt hda) (ne_of_gt hdb), ← hdet]
    ring
  rw [lowerWidth, hdiff, abs_div, abs_mul, abs_of_pos gap_pos,
    abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos (den_pos hf w)]

private theorem width_reverse (hf : FractionProperty) (u v : List ℕ+) (s : ℝ) (hs : 0 < s)
    (a b : LowerInitialMatrix) (hu : lowerInitialWordMatrix u = lowerInitialMatScale s a)
    (hv : lowerInitialWordMatrix v = lowerInitialMatScale s b)
    (hd : lowerBridgeWidthDen a < lowerBridgeWidthDen b) : lowerWidth v < lowerWidth u := by
  have hdu := den_pos hf u
  have hdv := den_pos hf v
  have hdiff : lowerBridgeWidthDen (lowerInitialWordMatrix u) <
      lowerBridgeWidthDen (lowerInitialWordMatrix v) := by
    rw [hu, hv, widthDen_scale, widthDen_scale]
    exact mul_lt_mul_of_pos_left hd (sq_pos_of_pos hs)
  rw [width_formula hf, width_formula hf]
  apply (div_lt_div_iff₀ hdv hdu).2
  nlinarith [mul_pos gap_pos (sub_pos.mpr hdiff)]

private theorem bridge_link (c : LowerBridgeCase) (n k : ℕ)
    (hm : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0) :
    ∃ s : ℝ, 0 < s ∧
      lowerInitialWordMatrix (lowerBridgePair c n k).1 =
        lowerInitialMatScale s (lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k)).1 ∧
      lowerInitialWordMatrix (lowerBridgePair c n k).2 =
        lowerInitialMatScale s (lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k)).2 := by
  have hms : lowerInitialSeamMatrices (lowerBridgeSeamCase c) (lowerInitialX n)
      (lowerInitialY (lowerBridgeK c k)) (lowerInitialY 0) =
      lowerBridgeMatrices c (lowerInitialX n) (lowerInitialY k) := by
    cases c <;> simp [lowerBridgeMatrices, lowerBridgeK, lowerBridgeFamily,
      lowerBridgeSeamCase, lowerInitialSeamFamily, lowerInitialY, lowerInitialV]
  have h := hm.2
  change ∃ s : ℝ, 0 < s ∧
    lowerInitialWordMatrix (lowerBridgePair c n k).1 =
      lowerInitialMatScale s (lowerInitialSeamMatrices (lowerBridgeSeamCase c) (lowerInitialX n)
        (lowerInitialY (lowerBridgeK c k)) (lowerInitialY 0)).1 ∧
    lowerInitialWordMatrix (lowerBridgePair c n k).2 =
      lowerInitialMatScale s (lowerInitialSeamMatrices (lowerBridgeSeamCase c) (lowerInitialX n)
        (lowerInitialY (lowerBridgeK c k)) (lowerInitialY 0)).2 at h
  rwa [hms] at h

end OtherBridge
open Freiman OtherBridge

namespace OtherBridge
theorem wf : ∀ (w : List ℕ+) (t : ℝ), 0 < t →
    prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
    0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
    (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
    (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro t ht
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [prefixEval, wm_eq, lowerInitialMatEval, lowerInitialMatDen]
  | append_singleton w a ih =>
      intro t ht
      have hA : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast a.one_le
      have hAt : (0:ℝ) < ((a : ℕ) : ℝ) + t := by linarith
      have ht' : (0:ℝ) < 1 / (((a : ℕ) : ℝ) + t) := by positivity
      obtain ⟨e1, e2, e3⟩ := ih (1 / (((a : ℕ) : ℝ) + t)) ht'
      have hpe : prefixEval (w ++ [a]) t = prefixEval w (1 / (((a : ℕ) : ℝ) + t)) := by
        rw [pe_append]
        simp [prefixEval]
      have hlen : ((w ++ [a]).length : ℕ) = w.length + 1 := by simp
      rw [hpe, wm_append, hlen]
      set M := lowerInitialWordMatrix w with hMdef
      clear_value M
      obtain ⟨ma, mb, mc, md⟩ := M
      simp only [lowerInitialMatMul, lowerInitialMatEval, lowerInitialMatDen, mul_zero, mul_one,
        zero_add, add_zero] at e1 e2 e3 ⊢
      have hden1 : (0:ℝ) < md * t + (mc + md * ((a : ℕ) : ℝ)) := by
        have h := mul_pos e2 hAt
        have hx : (mc * (1 / (((a : ℕ) : ℝ) + t)) + md) * (((a : ℕ) : ℝ) + t)
            = md * t + (mc + md * ((a : ℕ) : ℝ)) := by
          field_simp
          ring
        rw [hx] at h
        exact h
      refine ⟨?_, hden1, ?_⟩
      · rw [e1, div_eq_div_iff (ne_of_gt e2) (ne_of_gt hden1)]
        field_simp
        ring
      · rw [pow_succ, ← e3]
        ring
private theorem pe_pos : ∀ (w : List ℕ+) (t : ℝ), 0 < t → 0 < prefixEval w t
  | [], t, ht => by simpa [prefixEval] using ht
  | a :: w, t, ht => by
      rw [prefixEval]
      have h := pe_pos w t ht
      have ha : (0:ℝ) < ((a : ℕ):ℝ) := by exact_mod_cast a.pos
      positivity
private theorem tau_pos : 0 < lowerTau := by
  have h := Real.sqrt_nonneg 3
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold lowerTau
  nlinarith
private theorem pow_par (m n : ℕ) (h : m % 2 = n % 2) : (-1:ℝ)^m = (-1:ℝ)^n := by
  rcases Nat.even_or_odd m with he | ho
  · have hn : Even n := by rw [Nat.even_iff] at he ⊢; omega
    rw [he.neg_one_pow, hn.neg_one_pow]
  · have hn : Odd n := by rw [Nat.odd_iff] at ho ⊢; omega
    rw [ho.neg_one_pow, hn.neg_one_pow]
private theorem sq_pow_one (n : ℕ) : (-1:ℝ)^n * (-1:ℝ)^n = 1 := by
  rw [← pow_add]
  have h : Even (n+n) := ⟨n, by omega⟩
  exact h.neg_one_pow
private theorem difference_sign (hf : FractionProperty) (w : List ℕ+) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (prefixEval w y-prefixEval w x) *
      (lowerInitialMatDen (lowerInitialWordMatrix w) x * lowerInitialMatDen (lowerInitialWordMatrix w) y) =
      (y-x)*(-1:ℝ)^w.length := by
  obtain ⟨e1, dd1, det⟩ := hf w x hx
  obtain ⟨e2, dd2, _⟩ := hf w y hy
  rw [e1, e2]
  unfold lowerInitialMatEval lowerInitialMatDen at *
  rw [cross_diff _ _ _ _ (ne_of_gt dd1) (ne_of_gt dd2)]
  linear_combination (y-x)*det

private theorem ordered_prefix (w : List ℕ+) (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    0 < (-1:ℝ)^w.length * (prefixEval w b-prefixEval w a) := by
  have hden := mul_pos (wf w a ha).2.1 (wf w b (lt_trans ha hb)).2.1
  have hh := difference_sign wf w a b ha (lt_trans ha hb)
  have hprod : 0 < ((-1:ℝ)^w.length * (prefixEval w b-prefixEval w a)) *
      (lowerInitialMatDen (lowerInitialWordMatrix w) a * lowerInitialMatDen (lowerInitialWordMatrix w) b) := by
    calc _ = (b-a)*((-1:ℝ)^w.length * (-1:ℝ)^w.length) := by rw [mul_assoc, hh]; ring
         _ = b-a := by rw [sq_pow_one]; ring
         _ > 0 := sub_pos.mpr hb
  exact pos_of_mul_pos_left hprod hden.le
private theorem reverse_prefix (w : List ℕ+) (u v : List ℕ+) (hp : w.length%2=1)
    (h : prefixEval u lowerTau < prefixEval v lowerTau) :
    prefixEval (w++v) lowerTau < prefixEval (w++u) lowerTau := by
  have hh := ordered_prefix w (prefixEval u lowerTau) (prefixEval v lowerTau) (pe_pos _ _ tau_pos) h
  have hs : (-1:ℝ)^w.length = -1 := by
    have ho : Odd w.length := by rwa [Nat.odd_iff]
    exact ho.neg_one_pow
  rw [hs] at hh
  simp only [pe_append]
  linarith
end OtherBridge

private theorem bridge_inv (a b : ℝ) (hd : a^2 - 3*b^2 ≠ 0) :
    1/(a+b*Real.sqrt 3) = (a-b*Real.sqrt 3)/(a^2-3*b^2) := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hm : (a+b*Real.sqrt 3)*(a-b*Real.sqrt 3) = a^2 - 3*b^2 := by
    linear_combination -b^2 * hs
  have hp : a+b*Real.sqrt 3 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hm
    exact hd hm.symm
  apply (eq_div_iff hd).2
  rw [← hm, ← mul_assoc]
  field_simp

namespace OtherBridgeOrder
@[simp] private theorem rp_nil : prefixEval [] lowerTau = (-1 : ℝ) + 1 * Real.sqrt 3 := by simp only [prefixEval, lowerTau]; ring
@[simp] private theorem rp_3 : prefixEval [3] lowerTau = (2 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_nil]
  have harg : (3 : ℝ) + ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 3) = (2 : ℝ) + (1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (2 : ℝ) (1 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_3 : prefixEval [1,3] lowerTau = (1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_3]
  have harg : (1 : ℝ) + ((2 : ℝ) + (-1 : ℝ) * Real.sqrt 3) = (3 : ℝ) + (-1 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3 : ℝ) (-1 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_2_1_3 : prefixEval [2,1,3] lowerTau = (15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_3]
  have harg : (2 : ℝ) + ((1 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3) = (5 / 2 : ℝ) + (1 / 6 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (5 / 2 : ℝ) (1 / 6 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_3 : prefixEval [1,2,1,3] lowerTau = (52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_2_1_3]
  have harg : (1 : ℝ) + ((15 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3) = (52 / 37 : ℝ) + (-1 / 37 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (52 / 37 : ℝ) (-1 / 37 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_3_1_2_1_3 : prefixEval [3,1,2,1,3] lowerTau = (271 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_2_1_3]
  have harg : (3 : ℝ) + ((52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3) = (271 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (271 / 73 : ℝ) (1 / 73 : ℝ) (by norm_num)]
  norm_num
  ring

private theorem tail1 : prefixEval [3,1,2,1,3] lowerTau < prefixEval [1,2,1,3] lowerTau := by
  simp only [rp_3_1_2_1_3, rp_1_2_1_3]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
private theorem tail1short : prefixEval [3,1,2,1,3] lowerTau < prefixEval [1,3] lowerTau := by
  simp only [rp_3_1_2_1_3, rp_1_3]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
private theorem tail2 : prefixEval [2,1,3] lowerTau < prefixEval [1,2,1,3] lowerTau := by
  simp only [rp_2_1_3, rp_1_2_1_3]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
private theorem familyH_odd (f : LowerInitialFamily) (n k p : ℕ)
    (hp1 : (lowerNormalize (lowerFamilyPair f n k p)).1.length%2=1)
    (hp2 : (lowerNormalize (lowerFamilyPair f n k p)).2.length%2=1) :
    lowerFamilyH f n k p = Set.Icc
      (4 + prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).1 ++
        (if f=.auxB ∨ (f=.B ∧ k=0) then [1,3] else [1,2,1,3])) lowerTau +
        prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1,2,1,3]) lowerTau)
      (4 + prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [3,1,2,1,3]) lowerTau +
        prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).2 ++ [2,1,3]) lowerTau) := by
  have h1 : prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).1 ++
      (if f=.auxB ∨ (f=.B ∧ k=0) then [1,3] else [1,2,1,3])) lowerTau <
      prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).1 ++ [3,1,2,1,3]) lowerTau := by
    split
    · exact OtherBridge.reverse_prefix _ _ _ hp1 tail1short
    · exact OtherBridge.reverse_prefix _ _ _ hp1 tail1
  have h2 := OtherBridge.reverse_prefix _ _ _ hp2 tail2
  unfold lowerFamilyH
  dsimp only
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
private theorem repeat_len (n : ℕ) : (lowerRepeat lowerPeriod n).length = 6*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [lowerRepeat, List.replicate_succ, lowerPeriod, Nat.mul_succ] using ih
private theorem normalize_odd (p : LowerPair) (h1 : p.1.length%2=1) (h2 : p.2.length%2=1) :
    (lowerNormalize p).1.length%2=1 ∧ (lowerNormalize p).2.length%2=1 := by
  unfold lowerNormalize
  split
  · exact ⟨h1,h2⟩
  · exact ⟨h2,h1⟩
private theorem bridge_odd (c : LowerBridgeCase) (n : ℕ) (hf : lowerBridgeFamily c ≠ .C) :
    (lowerBridgePair c n 0).1.length%2=1 ∧ (lowerBridgePair c n 0).2.length%2=1 := by
  unfold lowerBridgePair
  apply normalize_odd <;>
    cases c <;> simp [lowerBridgeK, lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily] at hf ⊢ <;>
    simp [lowerFamilyPair, List.length_append, repeat_len, Nat.add_mod, Nat.mul_mod]

private theorem familyH_inf_odd (f : LowerInitialFamily) (n k p : ℕ)
    (hp1 : (lowerNormalize (lowerFamilyPair f n k p)).1.length%2=1)
    (hp2 : (lowerNormalize (lowerFamilyPair f n k p)).2.length%2=1) :
    sInf (lowerFamilyH f n k p) =
      4 + prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).1 ++
        (if f=.auxB ∨ (f=.B ∧ k=0) then [1,3] else [1,2,1,3])) lowerTau +
        prefixEval ((lowerNormalize (lowerFamilyPair f n k p)).2 ++ [1,2,1,3]) lowerTau := by
  have hne : (lowerFamilyH f n k p).Nonempty := by
    unfold lowerFamilyH
    exact Set.nonempty_Icc.mpr min_le_max
  rw [familyH_odd f n k p hp1 hp2] at hne ⊢
  exact csInf_Icc (Set.nonempty_Icc.mp hne)
end OtherBridgeOrder

namespace OtherBridgeC

private theorem ends_append (p t s : List ℕ+) (h : s.length ≤ t.length) :
    s.IsSuffix (p++t) ↔ s.IsSuffix t :=
  ⟨fun hh => List.suffix_of_suffix_length_le hh (List.suffix_append p t) h,
    fun hh => List.suffix_append_of_suffix hh⟩
private theorem tail_extend : prefixEval [1,2,1,3] lowerTau < prefixEval [1,3] lowerTau := by
  simp only [OtherBridgeOrder.rp_1_2_1_3, OtherBridgeOrder.rp_1_3]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
private theorem pair_order (p : LowerPair) (hp : p.1.length%2=p.2.length%2) :
    0 < (-1:ℝ)^p.1.length *
      ((4+prefixEval (p.1++[1,2,1,3]) lowerTau+prefixEval (p.2++[1,2,1,3]) lowerTau)-
       (4+prefixEval (p.1++[3,1,2,1,3]) lowerTau+prefixEval (p.2++[2,1,3]) lowerTau)) := by
  have h1 := OtherBridge.ordered_prefix p.1 _ _ (OtherBridge.pe_pos _ _ OtherBridge.tau_pos) OtherBridgeOrder.tail1
  have h2 := OtherBridge.ordered_prefix p.2 _ _ (OtherBridge.pe_pos _ _ OtherBridge.tau_pos) OtherBridgeOrder.tail2
  rw [OtherBridge.pow_par _ _ hp.symm] at h2
  simp only [OtherBridge.pe_append]
  nlinarith only [h1,h2]
private theorem endpoint_options (L R : List ℕ+) (hp : L.length%2 = (R.length+3)%2)
    (hw : lowerWidth (L++[1,3,1,2]) < lowerWidth (R++[2,1,3,1,2])) :
    lowerEndpoint (R++[2,1,3,1,2],L++[1,3,1,2]) (decide (L.length%2=0)) =
      4+prefixEval (L++[1,3,1,2,1,2,1,3]) lowerTau+prefixEval (R++[2,1,3,1,2,1,3]) lowerTau ∨
    lowerEndpoint (R++[2,1,3,1,2],L++[1,3,1,2]) (decide (L.length%2=0)) =
      4+prefixEval (L++[1,3,1,2,1,3]) lowerTau+prefixEval (R++[2,1,3,1,2,1,3]) lowerTau := by
  have hp' : (R.length+5)%2=L.length%2 := by omega
  rcases Nat.mod_two_eq_zero_or_one L.length with h0|h0
  · have hR : R.length%2=1 := by omega
    simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNormalize, lowerNaturalWords,
      lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ends_append, List.suffix_cons_iff,
      List.length_append, hR, h0, hw.le, not_le.mpr hw, Nat.add_mod, List.append_assoc]
    split_ifs
    · left; ring
    · right; ring
  · have hR : R.length%2=0 := by omega
    simp [lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNormalize, lowerNaturalWords,
      lowerNaturalShort, lowerEndpointSuffix, lowerEnds, ends_append, List.suffix_cons_iff,
      List.length_append, hR, h0, hw.le, not_le.mpr hw, Nat.add_mod, List.append_assoc]
    split_ifs
    · left; ring
    · right; ring
private theorem endpoint_sign (L R : List ℕ+) :
    0 < (-1:ℝ)^L.length *
      ((4+prefixEval (L++[1,3,1,2,1,3]) lowerTau+prefixEval (R++[2,1,3,1,2,1,3]) lowerTau)-
       (4+prefixEval (L++[1,3,1,2,1,2,1,3]) lowerTau+prefixEval (R++[2,1,3,1,2,1,3]) lowerTau)) := by
  have hh := OtherBridge.ordered_prefix (L++[1,3,1,2]) _ _
    (OtherBridge.pe_pos _ _ OtherBridge.tau_pos) tail_extend
  have hpow : (-1:ℝ)^(L++[1,3,1,2]).length=(-1:ℝ)^L.length := by
    apply OtherBridge.pow_par
    simp [Nat.add_mod]
  rw [hpow] at hh
  simp only [← OtherBridge.pe_append, List.append_assoc, List.cons_append, List.nil_append] at hh
  convert hh using 1 <;> ring

private theorem interval_bridge (even : Bool) (cx cy bx byy long short e : ℝ)
    (hC : 0 < (if even then 1 else -1)*(cy-cx))
    (hB : 0 < (if even then -1 else 1)*(byy-bx))
    (h1 : 0 < (if even then 1 else -1)*(long-byy))
    (h2 : 0 < (if even then 1 else -1)*(bx-cy))
    (hes : 0 < (if even then 1 else -1)*(short-long)) (he : e=long ∨ e=short) :
    (if even then Set.Icc e (sSup (Set.Icc (min cx cy) (max cx cy)))
      else Set.Icc (sInf (Set.Icc (min cx cy) (max cx cy))) e) ⊆
      Set.Icc (min bx byy) (max bx byy) := by
  cases even
  · simp only [Bool.false_eq_true, if_false] at *
    have hc : cy ≤ cx := by linarith
    have hb : bx ≤ byy := by linarith
    rw [min_eq_right hc, max_eq_left hc, csInf_Icc hc, min_eq_left hb, max_eq_right hb]
    intro t ht
    rcases he with rfl|rfl <;> constructor <;> linarith [ht.1, ht.2]
  · simp only [if_true] at *
    have hc : cx ≤ cy := by linarith
    have hb : byy ≤ bx := by linarith
    rw [min_eq_left hc, max_eq_right hc, csSup_Icc hc, min_eq_right hb, max_eq_left hb]
    intro t ht
    rcases he with rfl|rfl <;> constructor <;> linarith [ht.1, ht.2]
private theorem comparison (c : LowerBridgeCase) (n k : ℕ)
    (hf : lowerBridgeFamily c = .C) (h : lowerBridgeFacts c n k) :
    lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0 := by
  let L := [3,2,1,1]++lowerRepeat lowerPeriod n++[3,1,3,1,2]++List.replicate (k+1) (3:ℕ+)
  let R := [4,3,2,2]++lowerRepeat lowerPeriod n++[3,1]++List.replicate (k+1) (3:ℕ+)
  have hp : L.length%2=(R.length+3)%2 := by simp [L,R]; omega
  have hcN : lowerNormalize (lowerFamilyPair .C n k 0) = (R++[2,1,3],L++[1,3]) := by
    simpa [lowerFamilyPair,L,R,List.append_assoc] using Freiman.lower_initial_family_normalization LowerInitialFamily.C n k 0 (by decide)
  have hbN : lowerNormalize (lowerFamilyPair .B n (k+2) 0) = (L++[3],R++[3,3]) := by
    simpa [lowerFamilyPair,L,R,List.append_assoc,List.replicate_succ'] using Freiman.lower_initial_family_normalization LowerInitialFamily.B n (k+2) 0 (by decide)
  have hpair : lowerBridgePair c n k = (R++[2,1,3],L++[1,3]) := by
    simpa [lowerBridgePair,lowerBridgeK,hf] using hcN
  have hcommon : lowerBridgeCommonPair c n k = (L,R) := by simp [lowerBridgeCommonPair,hf,L,R]
  have hw : lowerWidth (L++[1,3,1,2]) < lowerWidth (R++[2,1,3,1,2]) := by
    have hh : lowerBridgeRecordFact c n k ((lowerBridgeRecords c)[3]'(by cases c <;> decide)) :=
      h _ (List.getElem_mem _)
    cases c <;> simp [lowerBridgeFamily,lowerBridgeSeamCase,lowerInitialSeamFamily] at hf
    all_goals simpa [lowerBridgeRecordFact,lowerBridgeRecords,lowerBridgeRecords_cZero,
      lowerBridgeRecords_cPos,hpair,lowerBridgeAppend,List.append_assoc] using hh
  have h1 : 0 < (-1:ℝ)^L.length *
      (prefixEval (L++[1,3,1,2,1,2,1,3]) lowerTau+prefixEval (R++[2,1,3,1,2,1,3]) lowerTau-
       prefixEval (L++[3,1,2,1,3]) lowerTau-prefixEval (R++[3,3,1,2,1,3]) lowerTau) := by
    have hh : lowerBridgeRecordFact c n k ((lowerBridgeRecords c)[4]'(by cases c <;> decide)) := h _ (List.getElem_mem _)
    cases c <;> simp [lowerBridgeFamily,lowerBridgeSeamCase,lowerInitialSeamFamily] at hf
    all_goals simpa [lowerBridgeRecordFact,lowerBridgeRecords,lowerBridgeRecords_cZero,
      lowerBridgeRecords_cPos,hcommon] using hh
  have h2 : 0 < (-1:ℝ)^L.length *
      (prefixEval (L++[3,3,1,2,1,3]) lowerTau+prefixEval (R++[3,3,2,1,3]) lowerTau-
       prefixEval (L++[1,3,1,2,1,3]) lowerTau-prefixEval (R++[2,1,3,1,2,1,3]) lowerTau) := by
    have hh : lowerBridgeRecordFact c n k ((lowerBridgeRecords c)[5]'(by cases c <;> decide)) := h _ (List.getElem_mem _)
    cases c <;> simp [lowerBridgeFamily,lowerBridgeSeamCase,lowerInitialSeamFamily] at hf
    all_goals simpa [lowerBridgeRecordFact,lowerBridgeRecords,lowerBridgeRecords_cZero,
      lowerBridgeRecords_cPos,hcommon] using hh
  have hC := pair_order (R++[2,1,3],L++[1,3]) (by simp; omega)
  have hB := pair_order (L++[3],R++[3,3]) (by simp; omega)
  have hes := endpoint_sign L R
  have he := endpoint_options L R hp hw
  have hcp : (-1:ℝ)^(R++[2,1,3]).length = (-1:ℝ)^L.length := by
    apply OtherBridge.pow_par
    simpa using hp.symm
  have hbp : (-1:ℝ)^(L++[3]).length = -(-1:ℝ)^L.length := by simp [pow_succ]
  have hpow : (-1:ℝ)^L.length = if decide (L.length%2=0) then 1 else -1 := by
    by_cases he : L.length%2=0
    · have hh : Even L.length := Nat.even_iff.mpr he
      simp [he,hh.neg_one_pow]
    · have hh : Odd L.length := Nat.odd_iff.mpr (by omega)
      simp [he,hh.neg_one_pow]
  simp only [hcp, hbp] at hC hB
  rw [hpow] at h1 h2 hC hB hes
  have hC' : 0 < (if decide (L.length%2=0) then 1 else -1)*
      ((4+prefixEval (L++[1,3,1,2,1,3]) lowerTau+prefixEval (R++[2,1,3,1,2,1,3]) lowerTau)-
       (4+prefixEval (L++[1,3,2,1,3]) lowerTau+prefixEval (R++[2,1,3,3,1,2,1,3]) lowerTau)) := by
    convert hC using 1 <;> simp only [List.append_assoc,List.cons_append,List.nil_append] <;> ring
  have hB' : 0 < (if decide (L.length%2=0) then -1 else 1)*
      ((4+prefixEval (L++[3,1,2,1,3]) lowerTau+prefixEval (R++[3,3,1,2,1,3]) lowerTau)-
       (4+prefixEval (L++[3,3,1,2,1,3]) lowerTau+prefixEval (R++[3,3,2,1,3]) lowerTau)) := by
    convert hB using 1 <;> simp only [List.append_assoc,List.cons_append,List.nil_append] <;>
      split <;> ring
  have hh := interval_bridge (decide (L.length%2=0)) _ _ _ _ _ _ _ hC' hB'
    (by convert h1 using 1 <;> ring) (by convert h2 using 1 <;> ring) hes he
  have hpC : (R++[2,1,3]).length%2=L.length%2 := by simpa using hp.symm
  simpa only [lowerBridgeInterval,lowerFamilyH,hcN,hbN,hpC,
    show LowerInitialFamily.C ≠ .auxB by decide, show LowerInitialFamily.C ≠ .B by decide,
    show LowerInitialFamily.B ≠ .auxB by decide, show k+2 ≠ 0 by omega,
    and_false,false_and,false_or,or_false,if_false,ite_self,
    List.append_assoc,List.cons_append,List.nil_append,Set.mem_Icc,decide_eq_true_eq,add_comm,add_left_comm,add_assoc] using hh
end OtherBridgeC

theorem solution (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c = .C) (h : lowerBridgeFacts c n k) : lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0 := OtherBridgeC.comparison c n k hf h
#print axioms solution
example : (∀ (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c = .C) (h : lowerBridgeFacts c n k) ,  lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0) := @solution
