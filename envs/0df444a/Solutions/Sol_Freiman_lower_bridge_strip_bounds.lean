-- Prove2me | solution 1 for Freiman.lower_bridge_strip_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:16:22.895631+00:00
-- url     : https://prove2.me/submissions/48b06dc1-67ca-47ea-8e0e-e62b18528188

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

namespace OtherBridgeStrip
private theorem strip_aZero (n : ℕ) (h : lowerBridgeFacts .aZero n 0)
    (he : lowerBridgeEndpointFacts .aZero n 0) :
    ∀ t ∈ lowerBridgeInterval .A n 0 0,
    ∃ a ∈ lowerBridgeLabels .A 0, ∃ b ∈ lowerBridgeLabels .A 0,
      lowerEndpoint (lowerBridgeAppend (lowerBridgePair .aZero n 0) a) false ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .aZero n 0) b) true := by
  have hp := OtherBridgeOrder.bridge_odd LowerBridgeCase.aZero n (by decide)
  have hpair : lowerNormalize (lowerFamilyPair .A n 0 0) = lowerBridgePair .aZero n 0 := rfl
  have hi := OtherBridgeOrder.familyH_inf_odd LowerInitialFamily.A n 0 0 (by simpa only [hpair] using hp.1) (by simpa only [hpair] using hp.2)
  simp only [hpair] at hi
  have hpow : (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length = -1 := by
    have ho : Odd (lowerBridgePair .aZero n 0).1.length := Nat.odd_iff.mpr hp.1
    exact ho.neg_one_pow
  have f53 : 0 < (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length *
      (prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,1,2,1,3]) lowerTau - prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aZero)[53]'(by decide)) (List.getElem_mem _)
  have f73 : 0 < (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length *
      (prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3]) lowerTau - prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aZero)[73]'(by decide)) (List.getElem_mem _)
  have e0 : lowerBridgeEndpointFact .aZero n 0 ⟨([1,2],[1,2]),true,([1,2,1,3],[1,2,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .aZero)[0]'(by decide)) (List.getElem_mem _)
  have e31 : lowerBridgeEndpointFact .aZero n 0 ⟨([1,2,1,3,3],[1,2,1,3,3]),false,([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .aZero)[31]'(by decide)) (List.getElem_mem _)
  have e40 : lowerBridgeEndpointFact .aZero n 0 ⟨([1,2,1,3],[1,2,1,3]),true,([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .aZero)[40]'(by decide)) (List.getElem_mem _)
  simp only [lowerBridgeEndpointFact, hp.1, reduceCtorEq, if_false, Bool.not_true, Bool.not_false] at e0 e31 e40
  rw [hpow] at f53 f73
  intro t ht
  have ht' : sInf (lowerFamilyH .A n 0 0) ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .aZero n 0) ([1,2],[1,2])) false := by
    simpa only [lowerBridgeInterval, hpair, hp.1, reduceCtorEq, if_false, decide_false, Set.mem_Icc, lowerBridgeAppend] using ht
  refine ⟨([1,2,1,3],[1,2,1,3]), by simp [lowerBridgeLabels], ([1,2,1,3,3],[1,2,1,3,3]), by simp [lowerBridgeLabels], ?_⟩
  simp only [show LowerInitialFamily.A ≠ .auxB by decide, show (LowerInitialFamily.A = .B) = False by decide, or_false, false_or, true_and, and_true, if_true, if_false] at hi
  constructor <;> linarith only [hi, ht'.1, ht'.2, f53, f73, e0, e31, e40]
private theorem strip_aPos (n : ℕ) (h : lowerBridgeFacts .aPos n 0)
    (he : lowerBridgeEndpointFacts .aPos n 0) :
    ∀ t ∈ lowerBridgeInterval .A n 0 0,
    ∃ a ∈ lowerBridgeLabels .A 1, ∃ b ∈ lowerBridgeLabels .A 1,
      lowerEndpoint (lowerBridgeAppend (lowerBridgePair .aPos n 0) a) false ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .aPos n 0) b) true := by
  have hp := OtherBridgeOrder.bridge_odd LowerBridgeCase.aPos n (by decide)
  have hpair : lowerNormalize (lowerFamilyPair .A n 0 0) = lowerBridgePair .aPos n 0 := rfl
  have hi := OtherBridgeOrder.familyH_inf_odd LowerInitialFamily.A n 0 0 (by simpa only [hpair] using hp.1) (by simpa only [hpair] using hp.2)
  simp only [hpair] at hi
  have hpow : (-1:ℝ)^(lowerBridgePair .aPos n 0).1.length = -1 := by
    have ho : Odd (lowerBridgePair .aPos n 0).1.length := Nat.odd_iff.mpr hp.1
    exact ho.neg_one_pow
  have f44 : 0 < (-1:ℝ)^(lowerBridgePair .aPos n 0).1.length *
      (prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,1,2,1,3]) lowerTau - prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aPos)[44]'(by decide)) (List.getElem_mem _)
  have f60 : 0 < (-1:ℝ)^(lowerBridgePair .aPos n 0).1.length *
      (prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3]) lowerTau - prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aPos)[60]'(by decide)) (List.getElem_mem _)
  have e0 : lowerBridgeEndpointFact .aPos n 0 ⟨([1,2],[1,2]),true,([1,2,1,3],[1,2,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .aPos)[0]'(by decide)) (List.getElem_mem _)
  have e25 : lowerBridgeEndpointFact .aPos n 0 ⟨([1,2,1,3,3],[1,2,1,3,3]),false,([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .aPos)[25]'(by decide)) (List.getElem_mem _)
  have e32 : lowerBridgeEndpointFact .aPos n 0 ⟨([1,2,1,3],[1,2,1,3]),true,([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .aPos)[32]'(by decide)) (List.getElem_mem _)
  simp only [lowerBridgeEndpointFact, hp.1, reduceCtorEq, if_false, Bool.not_true, Bool.not_false] at e0 e25 e32
  rw [hpow] at f44 f60
  intro t ht
  have ht' : sInf (lowerFamilyH .A n 0 0) ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .aPos n 0) ([1,2],[1,2])) false := by
    simpa only [lowerBridgeInterval, hpair, hp.1, reduceCtorEq, if_false, decide_false, Set.mem_Icc, lowerBridgeAppend] using ht
  refine ⟨([1,2,1,3],[1,2,1,3]), by simp [lowerBridgeLabels], ([1,2,1,3,3],[1,2,1,3,3]), by simp [lowerBridgeLabels], ?_⟩
  simp only [show LowerInitialFamily.A ≠ .auxB by decide, show (LowerInitialFamily.A = .B) = False by decide, or_false, false_or, true_and, and_true, if_true, if_false] at hi
  constructor <;> linarith only [hi, ht'.1, ht'.2, f44, f60, e0, e25, e32]
private theorem strip_bZero (n : ℕ) (h : lowerBridgeFacts .bZero n 0)
    (he : lowerBridgeEndpointFacts .bZero n 0) :
    ∀ t ∈ lowerBridgeInterval .B n 0 0,
    ∃ a ∈ lowerBridgeLabels .B 0, ∃ b ∈ lowerBridgeLabels .B 0,
      lowerEndpoint (lowerBridgeAppend (lowerBridgePair .bZero n 0) a) false ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .bZero n 0) b) true := by
  have hp := OtherBridgeOrder.bridge_odd LowerBridgeCase.bZero n (by decide)
  have hpair : lowerNormalize (lowerFamilyPair .B n 0 0) = lowerBridgePair .bZero n 0 := rfl
  have hi := OtherBridgeOrder.familyH_inf_odd LowerInitialFamily.B n 0 0 (by simpa only [hpair] using hp.1) (by simpa only [hpair] using hp.2)
  simp only [hpair] at hi
  have hpow : (-1:ℝ)^(lowerBridgePair .bZero n 0).1.length = -1 := by
    have ho : Odd (lowerBridgePair .bZero n 0).1.length := Nat.odd_iff.mpr hp.1
    exact ho.neg_one_pow
  have f16 : 0 < (-1:ℝ)^(lowerBridgePair .bZero n 0).1.length *
      (prefixEval ((lowerBridgePair .bZero n 0).1++[1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .bZero n 0).2++[1,2,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .bZero n 0).1++[1,3,3]) lowerTau - prefixEval ((lowerBridgePair .bZero n 0).2++[1,2,3]) lowerTau) :=
    h ((lowerBridgeRecords .bZero)[16]'(by decide)) (List.getElem_mem _)
  have f18 : 0 < (-1:ℝ)^(lowerBridgePair .bZero n 0).1.length *
      (prefixEval ((lowerBridgePair .bZero n 0).1++[1,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .bZero n 0).2++[1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .bZero n 0).1++[1,3]) lowerTau - prefixEval ((lowerBridgePair .bZero n 0).2++[1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .bZero)[18]'(by decide)) (List.getElem_mem _)
  have e0 : lowerBridgeEndpointFact .bZero n 0 ⟨([1,2],[1,2]),true,([1,2,1,3],[1,2,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .bZero)[0]'(by decide)) (List.getElem_mem _)
  have e7 : lowerBridgeEndpointFact .bZero n 0 ⟨([1,3],[1,2]),false,([1,3,3],[1,2,3])⟩ := he ((lowerBridgeEndpoints .bZero)[7]'(by decide)) (List.getElem_mem _)
  have e8 : lowerBridgeEndpointFact .bZero n 0 ⟨([1,3],[1,2]),true,([1,3,1,2,1,3],[1,2,1,3])⟩ := he ((lowerBridgeEndpoints .bZero)[8]'(by decide)) (List.getElem_mem _)
  simp only [lowerBridgeEndpointFact, hp.1, reduceCtorEq, if_false, Bool.not_true, Bool.not_false] at e0 e7 e8
  rw [hpow] at f16 f18
  intro t ht
  have ht' : sInf (lowerFamilyH .B n 0 0) ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .bZero n 0) ([1,2],[1,2])) false := by
    simpa only [lowerBridgeInterval, hpair, hp.1, reduceCtorEq, if_false, decide_false, Set.mem_Icc, lowerBridgeAppend] using ht
  refine ⟨([1,3],[1,2]), by simp [lowerBridgeLabels], ([1,3],[1,2]), by simp [lowerBridgeLabels], ?_⟩
  simp only [show LowerInitialFamily.B ≠ .auxB by decide, show (LowerInitialFamily.B = .B) = True by decide, or_false, false_or, true_and, and_true, if_true, if_false] at hi
  constructor <;> linarith only [hi, ht'.1, ht'.2, f16, f18, e0, e7, e8]
private theorem strip_bPos (n : ℕ) (h : lowerBridgeFacts .bPos n 0)
    (he : lowerBridgeEndpointFacts .bPos n 0) :
    ∀ t ∈ lowerBridgeInterval .B n 0 0,
    ∃ a ∈ lowerBridgeLabels .B 1, ∃ b ∈ lowerBridgeLabels .B 1,
      lowerEndpoint (lowerBridgeAppend (lowerBridgePair .bPos n 0) a) false ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .bPos n 0) b) true := by
  have hp := OtherBridgeOrder.bridge_odd LowerBridgeCase.bPos n (by decide)
  have hpair : lowerNormalize (lowerFamilyPair .B n 0 0) = lowerBridgePair .bPos n 0 := rfl
  have hi := OtherBridgeOrder.familyH_inf_odd LowerInitialFamily.B n 0 0 (by simpa only [hpair] using hp.1) (by simpa only [hpair] using hp.2)
  simp only [hpair] at hi
  have hpow : (-1:ℝ)^(lowerBridgePair .bPos n 0).1.length = -1 := by
    have ho : Odd (lowerBridgePair .bPos n 0).1.length := Nat.odd_iff.mpr hp.1
    exact ho.neg_one_pow
  have f16 : 0 < (-1:ℝ)^(lowerBridgePair .bPos n 0).1.length *
      (prefixEval ((lowerBridgePair .bPos n 0).1++[1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .bPos n 0).2++[1,2,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .bPos n 0).1++[1,3,3]) lowerTau - prefixEval ((lowerBridgePair .bPos n 0).2++[1,2,3]) lowerTau) :=
    h ((lowerBridgeRecords .bPos)[16]'(by decide)) (List.getElem_mem _)
  have f18 : 0 < (-1:ℝ)^(lowerBridgePair .bPos n 0).1.length *
      (prefixEval ((lowerBridgePair .bPos n 0).1++[1,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .bPos n 0).2++[1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .bPos n 0).1++[1,3]) lowerTau - prefixEval ((lowerBridgePair .bPos n 0).2++[1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .bPos)[18]'(by decide)) (List.getElem_mem _)
  have e0 : lowerBridgeEndpointFact .bPos n 0 ⟨([1,2],[1,2]),true,([1,2,1,3],[1,2,1,2,1,3])⟩ := he ((lowerBridgeEndpoints .bPos)[0]'(by decide)) (List.getElem_mem _)
  have e7 : lowerBridgeEndpointFact .bPos n 0 ⟨([1,3],[1,2]),false,([1,3,3],[1,2,3])⟩ := he ((lowerBridgeEndpoints .bPos)[7]'(by decide)) (List.getElem_mem _)
  have e8 : lowerBridgeEndpointFact .bPos n 0 ⟨([1,3],[1,2]),true,([1,3,1,2,1,3],[1,2,1,3])⟩ := he ((lowerBridgeEndpoints .bPos)[8]'(by decide)) (List.getElem_mem _)
  simp only [lowerBridgeEndpointFact, hp.1, reduceCtorEq, if_false, Bool.not_true, Bool.not_false] at e0 e7 e8
  rw [hpow] at f16 f18
  intro t ht
  have ht' : sInf (lowerFamilyH .B n 0 0) ≤ t ∧
      t ≤ lowerEndpoint (lowerBridgeAppend (lowerBridgePair .bPos n 0) ([1,2],[1,2])) false := by
    simpa only [lowerBridgeInterval, hpair, hp.1, reduceCtorEq, if_false, decide_false, Set.mem_Icc, lowerBridgeAppend] using ht
  refine ⟨([1,3],[1,2]), by simp [lowerBridgeLabels], ([1,3],[1,2]), by simp [lowerBridgeLabels], ?_⟩
  simp only [show LowerInitialFamily.B ≠ .auxB by decide, show (LowerInitialFamily.B = .B) = True by decide, or_false, false_or, true_and, and_true, if_true, if_false] at hi
  constructor <;> linarith only [hi, ht'.1, ht'.2, f16, f18, e0, e7, e8]
end OtherBridgeStrip

theorem solution (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) (h : lowerBridgeFacts c n 0) (he : lowerBridgeEndpointFacts c n 0) : ∀ t ∈ lowerBridgeInterval (lowerBridgeFamily c) n 0 0, ∃ a ∈ lowerBridgeLabels (lowerBridgeFamily c) n, ∃ b ∈ lowerBridgeLabels (lowerBridgeFamily c) n, lowerEndpoint (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) a) false ≤ t ∧ t ≤ lowerEndpoint (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) b) true := by
  cases c with
  | aZero =>
    have hn : n = 0 := by simpa [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero] using hc.symm
    subst n
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeAppend,
      lowerBridgePair, lowerBridgeK, lowerPhysicalAdd] using OtherBridgeStrip.strip_aZero 0 h he
  | aPos =>
    have hn : n ≠ 0 := by simpa [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero] using hc.symm
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeAppend,
      lowerBridgePair, lowerBridgeK, lowerPhysicalAdd, lowerBridgeLabels, hn] using OtherBridgeStrip.strip_aPos n h he
  | bZero =>
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeAppend,
      lowerBridgePair, lowerBridgeK, lowerPhysicalAdd, lowerBridgeLabels] using OtherBridgeStrip.strip_bZero n h he
  | bPos =>
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeAppend,
      lowerBridgePair, lowerBridgeK, lowerPhysicalAdd, lowerBridgeLabels] using OtherBridgeStrip.strip_bPos n h he
  | cZero => exact False.elim (hf rfl)
  | cPos => exact False.elim (hf rfl)
#print axioms solution

example : (∀ (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) (h : lowerBridgeFacts c n 0) (he : lowerBridgeEndpointFacts c n 0) ,  ∀ t ∈ lowerBridgeInterval (lowerBridgeFamily c) n 0 0, ∃ a ∈ lowerBridgeLabels (lowerBridgeFamily c) n, ∃ b ∈ lowerBridgeLabels (lowerBridgeFamily c) n, lowerEndpoint (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) a) false ≤ t ∧ t ≤ lowerEndpoint (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) b) true) := @solution
