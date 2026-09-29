-- Prove2me | solution 1 for Freiman.lower_bridge_chain_contacts
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:32:59.447265+00:00
-- url     : https://prove2.me/submissions/838ec7dc-57d8-417e-b2c5-ecd134c6d391

import Theorems.Thm_Freiman_lower_bridge_tau_values
import Theorems.Thm_Freiman_lower_initial_family_matrix
import Theorems.Thm_Freiman_lower_initial_period_ratio
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
private theorem den_scale (s : ℝ) (a : LowerInitialMatrix) (t : ℝ) :
    lowerInitialMatDen (lowerInitialMatScale s a) t = s * lowerInitialMatDen a t := by
  unfold lowerInitialMatDen lowerInitialMatScale
  ring
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
private theorem contact_generic (hf : FractionProperty) (p u v : LowerPair)
    (m : LowerInitialMatrix × LowerInitialMatrix) (s : ℝ) (hs : 0 < s)
    (hm1 : lowerInitialWordMatrix p.1 = lowerInitialMatScale s m.1)
    (hm2 : lowerInitialWordMatrix p.2 = lowerInitialMatScale s m.2) (opposite : Bool)
    (hpar : (-1:ℝ)^p.2.length = (if opposite then -1 else 1)*(-1:ℝ)^p.1.length)
    (hn : 0 < lowerBridgeDifference m u v opposite) :
    0 < (-1:ℝ)^p.1.length *
      (prefixEval (p.1++u.1) lowerTau + prefixEval (p.2++u.2) lowerTau -
       prefixEval (p.1++v.1) lowerTau - prefixEval (p.2++v.2) lowerTau) := by
  let a := prefixEval u.1 lowerTau
  let b := prefixEval v.1 lowerTau
  let cc := prefixEval u.2 lowerTau
  let d := prefixEval v.2 lowerTau
  have ha : 0 < a := pe_pos _ _ tau_pos
  have hb : 0 < b := pe_pos _ _ tau_pos
  have hcc : 0 < cc := pe_pos _ _ tau_pos
  have hd : 0 < d := pe_pos _ _ tau_pos
  let d1a := lowerInitialMatDen (lowerInitialWordMatrix p.1) a
  let d1b := lowerInitialMatDen (lowerInitialWordMatrix p.1) b
  let d2c := lowerInitialMatDen (lowerInitialWordMatrix p.2) cc
  let d2d := lowerInitialMatDen (lowerInitialWordMatrix p.2) d
  have hp : 0 < (d1b*d1a)*(d2d*d2c) :=
    mul_pos (mul_pos (hf p.1 _ hb).2.1 (hf p.1 _ ha).2.1)
      (mul_pos (hf p.2 _ hd).2.1 (hf p.2 _ hcc).2.1)
  have hn' : 0 < (a-b)*d2c*d2d + (if opposite then -(cc-d) else cc-d)*d1a*d1b := by
    have hh := mul_pos (sq_pos_of_pos hs) hn
    dsimp only [d1a, d1b, d2c, d2d]
    rw [hm1, hm2, den_scale, den_scale, den_scale, den_scale]
    unfold lowerBridgeDifference at hh
    cases opposite <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> nlinarith
  have e1 := difference_sign hf p.1 b a hb ha
  have e2 := difference_sign hf p.2 d cc hd hcc
  have heq : ((-1:ℝ)^p.1.length *
      (prefixEval p.1 a-prefixEval p.1 b+prefixEval p.2 cc-prefixEval p.2 d)) *
      ((d1b*d1a)*(d2d*d2c)) =
      (a-b)*d2c*d2d + (if opposite then -(cc-d) else cc-d)*d1a*d1b := by
    have hstep : ((-1:ℝ)^p.1.length *
        (prefixEval p.1 a-prefixEval p.1 b+prefixEval p.2 cc-prefixEval p.2 d)) *
        ((d1b*d1a)*(d2d*d2c)) =
        (-1:ℝ)^p.1.length * ((prefixEval p.1 a-prefixEval p.1 b)*(d1b*d1a))*(d2d*d2c) +
        (-1:ℝ)^p.1.length * ((prefixEval p.2 cc-prefixEval p.2 d)*(d2d*d2c))*(d1b*d1a) := by ring
    rw [hstep, e1, e2, hpar]
    have hh := sq_pow_one p.1.length
    cases opposite
    · simp only [Bool.false_eq_true, ite_false]
      linear_combination ((a-b)*(d2c*d2d) + (cc-d)*(d1a*d1b))*hh
    · simp only [ite_true]
      linear_combination ((a-b)*(d2c*d2d) - (cc-d)*(d1a*d1b))*hh
  rw [pe_append, pe_append, pe_append, pe_append]
  have hresult : 0 < (-1:ℝ)^p.1.length *
      (prefixEval p.1 a-prefixEval p.1 b+prefixEval p.2 cc-prefixEval p.2 d) := by
    nlinarith [heq]
  convert hresult using 1 <;> dsimp only [a, b, cc, d] <;> ring
private theorem family_matrix (c : LowerBridgeCase) (n k : ℕ)
    (hc : lowerBridgeZero c = decide (n=0)) :
    lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0 :=
  Freiman.lower_initial_family_matrix _ _ _ _ hc
end OtherBridge

open Freiman
open Freiman
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

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace OtherBridgeReverse
@[simp] private theorem rp_1_1_3 : prefixEval [1,1,3] lowerTau = (9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.1
@[simp] private theorem rp_1_2_1_3 : prefixEval [1,2,1,3] lowerTau = (52 / 73 : ℝ) + (1 / 73 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.1
@[simp] private theorem rp_2_1_1_3 : prefixEval [2,1,1,3] lowerTau = (35 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_1_3]
  have harg : (2 : ℝ) + ((9 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3) = (35 / 13 : ℝ) + (-1 / 13 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (35 / 13 : ℝ) (-1 / 13 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_1_3 : prefixEval [1,2,1,1,3] lowerTau = (43 / 59 : ℝ) + (-1 / 177 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_2_1_1_3]
  have harg : (1 : ℝ) + ((35 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3) = (129 / 94 : ℝ) + (1 / 94 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (129 / 94 : ℝ) (1 / 94 : ℝ) (by norm_num)]
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
@[simp] private theorem rp_1_3_1_2_1_3 : prefixEval [1,3,1,2,1,3] lowerTau = (1277 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_3_1_2_1_3]
  have harg : (1 : ℝ) + ((271 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3) = (1277 / 1006 : ℝ) + (-1 / 1006 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (1277 / 1006 : ℝ) (-1 / 1006 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_3_1_2_1_1_3 : prefixEval [3,1,2,1,1,3] lowerTau = (660 / 2461 : ℝ) + (1 / 2461 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_2_1_1_3]
  have harg : (3 : ℝ) + ((43 / 59 : ℝ) + (-1 / 177 : ℝ) * Real.sqrt 3) = (220 / 59 : ℝ) + (-1 / 177 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (220 / 59 : ℝ) (-1 / 177 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_3_3_3_3 : prefixEval [1,2,1,3,3,3,3] lowerTau = (44368 / 60397 : ℝ) + (-1 / 60397 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_3_1_2_1_1_3 : prefixEval [1,3,1,2,1,1,3] lowerTau = (3121 / 3958 : ℝ) + (-1 / 3958 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_3_1_2_1_1_3]
  have harg : (1 : ℝ) + ((660 / 2461 : ℝ) + (1 / 2461 : ℝ) * Real.sqrt 3) = (3121 / 2461 : ℝ) + (1 / 2461 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (3121 / 2461 : ℝ) (1 / 2461 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_3_1_3_1_2_1_3 : prefixEval [3,1,3,1,2,1,3] lowerTau = (6140 / 23257 : ℝ) + (-1 / 23257 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_3_1_2_1_3]
  have harg : (3 : ℝ) + ((1277 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3) = (6140 / 1621 : ℝ) + (1 / 1621 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (6140 / 1621 : ℝ) (1 / 1621 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_3_1_2_1_3 : prefixEval [1,2,1,3,1,2,1,3] lowerTau = (17117 / 23257 : ℝ) + (1 / 23257 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_3_3_3_3 : prefixEval [1,2,1,3,3,3,3,3] lowerTau = (484195 / 659149 : ℝ) + (1 / 659149 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_3_1_3_1_2_1_3 : prefixEval [1,3,1,3,1,2,1,3] lowerTau = (9799 / 12386 : ℝ) + (1 / 37158 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_3_1_3_1_2_1_3]
  have harg : (1 : ℝ) + ((6140 / 23257 : ℝ) + (-1 / 23257 : ℝ) * Real.sqrt 3) = (29397 / 23257 : ℝ) + (-1 / 23257 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (29397 / 23257 : ℝ) (-1 / 23257 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_3_1_3_1_2_1_1_3 : prefixEval [3,1,3,1,2,1,1,3] lowerTau = (14995 / 56809 : ℝ) + (1 / 56809 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_3_1_2_1_1_3]
  have harg : (3 : ℝ) + ((3121 / 3958 : ℝ) + (-1 / 3958 : ℝ) * Real.sqrt 3) = (14995 / 3958 : ℝ) + (-1 / 3958 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (14995 / 3958 : ℝ) (-1 / 3958 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,1,2,1,3] lowerTau = (190985 / 260038 : ℝ) + (-1 / 260038 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_3_3_2_1_3 : prefixEval [1,2,1,3,3,3,2,1,3] lowerTau = (299605 / 407858 : ℝ) + (-1 / 1223574 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_3_1_3_1_2_1_1_3 : prefixEval [1,3,1,3,1,2,1,1,3] lowerTau = (71804 / 90757 : ℝ) + (-1 / 90757 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_3_1_3_1_2_1_1_3]
  have harg : (1 : ℝ) + ((14995 / 56809 : ℝ) + (1 / 56809 : ℝ) * Real.sqrt 3) = (71804 / 56809 : ℝ) + (1 / 56809 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (71804 / 56809 : ℝ) (1 / 56809 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_2_1_3_1_3_1_2_1_3 : prefixEval [2,1,3,1,3,1,2,1,3] lowerTau = (103713 / 289477 : ℝ) + (-1 / 289477 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_3_1_3_1_2_1_3]
  have harg : (2 : ℝ) + ((9799 / 12386 : ℝ) + (1 / 37158 : ℝ) * Real.sqrt 3) = (34571 / 12386 : ℝ) + (1 / 37158 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (34571 / 12386 : ℝ) (1 / 37158 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_2_1_3_1_3_2_3 : prefixEval [1,2,1,2,1,3,1,3,2,3] lowerTau = (804501 / 1098526 : ℝ) + (1 / 1098526 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_1_3_1_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,1,3] lowerTau = (393190 / 534061 : ℝ) + (1 / 534061 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_2_1_3_1_3_1_2_1_3]
  have harg : (1 : ℝ) + ((103713 / 289477 : ℝ) + (-1 / 289477 : ℝ) * Real.sqrt 3) = (393190 / 289477 : ℝ) + (-1 / 289477 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (393190 / 289477 : ℝ) (-1 / 289477 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_3_1_3_1_2_2_3 : prefixEval [1,2,1,3,1,3,1,2,2,3] lowerTau = (253237 / 343967 : ℝ) + (1 / 1031901 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,3,1,2,1,3] lowerTau = (2079038 / 2830201 : ℝ) + (1 / 2830201 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_3_3_3_2_1_3 : prefixEval [1,2,1,3,3,3,3,2,1,3] lowerTau = (9805068 / 13347889 : ℝ) + (1 / 13347889 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_2_1_3_1_3_1_2_1_1_3 : prefixEval [2,1,3,1,3,1,2,1,1,3] lowerTau = (253318 / 707053 : ℝ) + (1 / 707053 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_1_3_1_3_1_2_1_1_3]
  have harg : (2 : ℝ) + ((71804 / 90757 : ℝ) + (-1 / 90757 : ℝ) * Real.sqrt 3) = (253318 / 90757 : ℝ) + (-1 / 90757 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (253318 / 90757 : ℝ) (-1 / 90757 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_2_1_3_1_3_2_1_3 : prefixEval [1,2,1,2,1,3,1,3,2,1,3] lowerTau = (2402518 / 3280573 : ℝ) + (-1 / 3280573 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_1_3_1_2_1_1_3 : prefixEval [1,2,1,3,1,3,1,2,1,1,3] lowerTau = (960371 / 1304446 : ℝ) + (-1 / 1304446 : ℝ) * Real.sqrt 3 := by
  rw [prefixEval]
  simp only [PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat]
  rw [rp_2_1_3_1_3_1_2_1_1_3]
  have harg : (1 : ℝ) + ((253318 / 707053 : ℝ) + (1 / 707053 : ℝ) * Real.sqrt 3) = (960371 / 707053 : ℝ) + (1 / 707053 : ℝ) * Real.sqrt 3 := by ring
  rw [harg, bridge_inv (960371 / 707053 : ℝ) (1 / 707053 : ℝ) (by norm_num)]
  norm_num
  ring
@[simp] private theorem rp_1_2_1_3_1_3_1_2_2_1_3 : prefixEval [1,2,1,3,1,3,1,2,2,1,3] lowerTau = (2304533 / 3130198 : ℝ) + (-1 / 3130198 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] private theorem rp_1_2_1_3_3_3_3_1_2_1_3 : prefixEval [1,2,1,3,3,3,3,1,2,1,3] lowerTau = (22683113 / 30879133 : ℝ) + (-1 / 30879133 : ℝ) * Real.sqrt 3 := (Freiman.lower_bridge_tau_values).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem reverse_ac : LowerInitialFamily.A ≠ .C := by decide
private theorem bernstein_positive (a b c z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 < a*(1-z)^2 + 2*b*z*(1-z) + c*z^2 := by
  have hmid : 0 ≤ 2*b*z*(1-z) := by positivity
  have ha0 : 0 ≤ a*(1-z)^2 := by positivity
  have hc0 : 0 ≤ c*z^2 := by positivity
  by_cases hz : z = 1
  · subst z; nlinarith
  · have hneq : 1-z ≠ 0 := by intro he; apply hz; linarith
    have ha1 : 0 < a*(1-z)^2 := mul_pos ha (sq_pos_of_ne_zero hneq)
    linarith
private theorem sqrt_three_lower : 1 < Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

private theorem numeric_aZero_0 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,3,3,3,3],[1,2,1,3,3,3,3,2,1,3]) ([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,3,3,3,3],[1,2,1,3,3,3,3,2,1,3]) ([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3]) false =
    ((24308776519851985048502 / 890621870784008575763 : ℝ) + (1825023470480173322917 / 1781243741568017151526 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((24308776519851985048502 / 890621870784008575763 : ℝ) + (1825023470480173322917 / 1781243741568017151526 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((24308776519851985048502 / 890621870784008575763 : ℝ) + (1825023470480173322917 / 1781243741568017151526 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_3_3_3_3, rp_1_2_1_3_3_3_3_2_1_3, rp_1_2_1_3_3_1_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

private theorem numeric_aZero_1 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,1,3,1,2,2,3],[1,2,1,2,1,3,1,3,2,3]) ([1,2,1,3,3,3,3,1,2,1,3],[1,2,1,3,3,3,3,1,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,1,3,1,2,2,3],[1,2,1,2,1,3,1,3,2,3]) ([1,2,1,3,3,3,3,1,2,1,3],[1,2,1,3,3,3,3,1,2,1,3]) false =
    ((-10326240371036888100625 / 109545222429879784467842 : ℝ) + (23069715876142269294035 / 109545222429879784467842 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((-10326240371036888100625 / 109545222429879784467842 : ℝ) + (23069715876142269294035 / 109545222429879784467842 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((-10326240371036888100625 / 109545222429879784467842 : ℝ) + (23069715876142269294035 / 109545222429879784467842 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_1_3_1_2_2_3, rp_1_2_1_2_1_3_1_3_2_3, rp_1_2_1_3_3_3_3_1_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

private theorem numeric_aZero_2 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,3,3,1,2,1,3],[1,2,1,3,3,3,1,2,1,3]) ([1,2,1,3,1,3,1,2,2,1,3],[1,2,1,2,1,3,1,3,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,3,3,1,2,1,3],[1,2,1,3,3,3,1,2,1,3]) ([1,2,1,3,1,3,1,2,2,1,3],[1,2,1,2,1,3,1,3,2,1,3]) false =
    ((213818852560670126114968663 / 82253819917567084276225054 : ℝ) + (11824888978004370389998819 / 82253819917567084276225054 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((213818852560670126114968663 / 82253819917567084276225054 : ℝ) + (11824888978004370389998819 / 82253819917567084276225054 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((213818852560670126114968663 / 82253819917567084276225054 : ℝ) + (11824888978004370389998819 / 82253819917567084276225054 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_3_3_1_2_1_3, rp_1_2_1_3_1_3_1_2_2_1_3, rp_1_2_1_2_1_3_1_3_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

private theorem numeric_aZero_3 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3]) ([1,2,1,3,3,3,3],[1,2,1,3,3,3,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aZero x 0) ([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3]) ([1,2,1,3,3,3,3],[1,2,1,3,3,3,2,1,3]) false =
    ((2009217241063673628098 / 6661955731972234837 : ℝ) + (228045802568049855868 / 19985867195916704511 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((2009217241063673628098 / 6661955731972234837 : ℝ) + (228045802568049855868 / 19985867195916704511 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((2009217241063673628098 / 6661955731972234837 : ℝ) + (228045802568049855868 / 19985867195916704511 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_1_2_1_3, rp_1_2_1_3_3_3_3, rp_1_2_1_3_3_3_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

private theorem numeric_aPos_0 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aPos x 0) ([1,2,1,3,1,3,1,2,1,3],[1,2,1,2,1,3,1,3,2,3]) ([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aPos x 0) ([1,2,1,3,1,3,1,2,1,3],[1,2,1,2,1,3,1,3,2,3]) ([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3]) false =
    ((32973110752273521709063757 / 163930390421845067852 : ℝ) + (15276786831344549097280779 / 1803234294640295746372 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((2802328432982044881890328439 / 13934083185856830767420 : ℝ) + (259669856387324429270914631 / 30654983008885027688324 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((2619816242337998410688983165429 / 13028367778776136767537700 : ℝ) + (110344595137417708997587299969 / 13028367778776136767537700 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_1_3_1_2_1_3, rp_1_2_1_2_1_3_1_3_2_3, rp_1_2_1_3_3_1_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

private theorem numeric_aPos_1 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aPos x 0) ([1,2,1,3,3,3,1,2,1,3],[1,2,1,3,3,3,1,2,1,3]) ([1,2,1,3,1,3,1,2,1,1,3],[1,2,1,2,1,3,1,3,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aPos x 0) ([1,2,1,3,3,3,1,2,1,3],[1,2,1,3,3,3,1,2,1,3]) ([1,2,1,3,1,3,1,2,1,1,3],[1,2,1,2,1,3,1,3,2,1,3]) false =
    ((59897110198781477836159294235 / 3116145205109903672540978 : ℝ) + (4592513726852613109133376249 / 3116145205109903672540978 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((149723788639640002079733917514 / 7790363012774759181352445 : ℝ) + (195155136725677085467720491397 / 132436171217170906082991565 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((216323442032797286999227681523658 / 11257074553459527017054283025 : ℝ) + (16585917715489987008519763709148 / 11257074553459527017054283025 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_3_3_1_2_1_3, rp_1_2_1_3_1_3_1_2_1_1_3, rp_1_2_1_2_1_3_1_3_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

private theorem numeric_aPos_2 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/85) :
    0 < lowerBridgeDifference (lowerBridgeMatrices .aPos x 0) ([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3]) ([1,2,1,3,3,3,3],[1,2,1,3,3,3,2,1,3]) false := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : lowerBridgeDifference (lowerBridgeMatrices .aPos x 0) ([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3]) ([1,2,1,3,3,3,3],[1,2,1,3,3,3,2,1,3]) false =
    ((29735986402046285871014577 / 13323911463944469674 : ℝ) + (3374528596619589671384081 / 39971734391833409022 : ℝ) * Real.sqrt 3)*(1-85*x)^2 + 2*((1263606583948862386415109513 / 566266237217639961145 : ℝ) + (28679569942582521716792695 / 339759742330583976687 : ℝ) * Real.sqrt 3)*(85*x)*(1-85*x) + ((19525794618751207099127651981 / 8751387302454435763150 : ℝ) + (2215845477082305152627028001 / 26254161907363307289450 : ℝ) * Real.sqrt 3)*(85*x)^2 := by
    norm_num [reverse_ac, lowerBridgeDifference, lowerBridgeMatrices, lowerBridgeSeamCase, lowerInitialSeamMatrices, lowerInitialSeamFamily, lowerInitialSeamZero, lowerBridgeFamily, lowerInitialP, lowerInitialK, lowerInitialWordMatrix, lowerInitialMatMul, lowerInitialMatDen, rp_1_2_1_3_1_2_1_3, rp_1_2_1_3_3_3_3, rp_1_2_1_3_3_3_2_1_3, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, PNat.val_ofNat, PNat.one_coe, Nat.cast_one, Nat.cast_ofNat, ite_self, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, mul_zero, zero_mul]
    ring_nf
    norm_num [Real.sq_sqrt, show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs]]
    ring
  rw [he]
  apply bernstein_positive
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · nlinarith [sqrt_three_lower]
  · positivity
  · linarith

end OtherBridgeReverse

namespace OtherBridgeEndpoint
private theorem normalize_parity (p : LowerPair) (hp : p.1.length%2=p.2.length%2) :
    (lowerNormalize p).1.length%2=(lowerNormalize p).2.length%2 := by
  unfold lowerNormalize
  split
  · exact hp
  · exact hp.symm
private theorem bridge_parity (c : LowerBridgeCase) (n k : ℕ) :
    (lowerBridgePair c n k).1.length%2=(lowerBridgePair c n k).2.length%2 := by
  unfold lowerBridgePair
  apply normalize_parity
  cases c <;> simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily,
    lowerFamilyPair, List.length_append] <;> omega
private theorem ends_append (p t s : List ℕ+) (h : s.length ≤ t.length) :
    s.IsSuffix (p++t) ↔ s.IsSuffix t :=
  ⟨fun hh => List.suffix_of_suffix_length_le hh (List.suffix_append p t) h,
    fun hh => List.suffix_append_of_suffix hh⟩
private theorem pow_mod (n : ℕ) : (-1:ℝ)^n = (-1:ℝ)^(n%2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul]
  norm_num
private theorem covers_overlap (p q : LowerPair)
    (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true)
    (h : lowerEndpoint p false ≤ lowerEndpoint q true ∧ lowerEndpoint q false ≤ lowerEndpoint p true) :
    (lowerCover p ∩ lowerCover q).Nonempty := by
  unfold lowerCover
  rw [Set.Icc_inter_Icc]
  exact Set.nonempty_Icc.mpr (max_le (le_min (ho _) h.1) (le_min h.2 (ho _)))
private theorem chain_aZero (n : ℕ) (hc : lowerBridgeZero .aZero = decide (n=0))
    (h : lowerBridgeFacts .aZero n 0) (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true) :
    (lowerBridgeLabels .A 0).IsChain (fun a b =>
      (lowerCover (lowerBridgeAppend (lowerBridgePair .aZero n 0) a) ∩
        lowerCover (lowerBridgeAppend (lowerBridgePair .aZero n 0) b)).Nonempty) := by
  have hp := bridge_parity LowerBridgeCase.aZero n 0
  have h0 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1]) := h ((lowerBridgeRecords .aZero)[0]'(by decide)) (List.getElem_mem _)
  have h0le := (h0).le
  have h0nle := not_le.mpr h0
  have h3 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2]) := h ((lowerBridgeRecords .aZero)[3]'(by decide)) (List.getElem_mem _)
  have h3le := (h3).le
  have h3nle := not_le.mpr h3
  have h4 : lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2])++[1,3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2])++[1,3]) := h ((lowerBridgeRecords .aZero)[4]'(by decide)) (List.getElem_mem _)
  have h5 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[5]'(by decide)) (List.getElem_mem _)
  have h5le := (h5).le
  have h5nle := not_le.mpr h5
  have h6 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[6]'(by decide)) (List.getElem_mem _)
  have h6le := (h6).le
  have h6nle := not_le.mpr h6
  have h7 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[7]'(by decide)) (List.getElem_mem _)
  have h7le := (h7).le
  have h7nle := not_le.mpr h7
  have h8 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aZero)[8]'(by decide)) (List.getElem_mem _)
  have h8le := (h8).le
  have h8nle := not_le.mpr h8
  have h10 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[10]'(by decide)) (List.getElem_mem _)
  have h10le := (h10).le
  have h10nle := not_le.mpr h10
  have h11 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[11]'(by decide)) (List.getElem_mem _)
  have h11le := (h11).le
  have h11nle := not_le.mpr h11
  have h12 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aZero)[12]'(by decide)) (List.getElem_mem _)
  have h12le := (h12).le
  have h12nle := not_le.mpr h12
  have h14 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[14]'(by decide)) (List.getElem_mem _)
  have h14le := (h14).le
  have h14nle := not_le.mpr h14
  have h15 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[15]'(by decide)) (List.getElem_mem _)
  have h15le := (h15).le
  have h15nle := not_le.mpr h15
  have h16 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[16]'(by decide)) (List.getElem_mem _)
  have h16le := (h16).le
  have h16nle := not_le.mpr h16
  have h17 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[17]'(by decide)) (List.getElem_mem _)
  have h17le := (h17).le
  have h17nle := not_le.mpr h17
  have h19 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[19]'(by decide)) (List.getElem_mem _)
  have h19le := (h19).le
  have h19nle := not_le.mpr h19
  have h20 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[20]'(by decide)) (List.getElem_mem _)
  have h20le := (h20).le
  have h20nle := not_le.mpr h20
  have h21 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[21]'(by decide)) (List.getElem_mem _)
  have h21le := (h21).le
  have h21nle := not_le.mpr h21
  have h23 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2]) := h ((lowerBridgeRecords .aZero)[23]'(by decide)) (List.getElem_mem _)
  have h23le := (h23).le
  have h23nle := not_le.mpr h23
  have h24 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[24]'(by decide)) (List.getElem_mem _)
  have h24le := (h24).le
  have h24nle := not_le.mpr h24
  have h25 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[25]'(by decide)) (List.getElem_mem _)
  have h25le := (h25).le
  have h25nle := not_le.mpr h25
  have h26 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2,1]) := h ((lowerBridgeRecords .aZero)[26]'(by decide)) (List.getElem_mem _)
  have h26le := (h26).le
  have h26nle := not_le.mpr h26
  have h27 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,2])++[3]) < lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2,1])++[3]) := h ((lowerBridgeRecords .aZero)[27]'(by decide)) (List.getElem_mem _)
  have h27le := (h27).le
  have h27nle := not_le.mpr h27
  have h29 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[29]'(by decide)) (List.getElem_mem _)
  have h29le := (h29).le
  have h29nle := not_le.mpr h29
  have h30 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aZero)[30]'(by decide)) (List.getElem_mem _)
  have h30le := (h30).le
  have h30nle := not_le.mpr h30
  have h31 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2,1]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,1]) := h ((lowerBridgeRecords .aZero)[31]'(by decide)) (List.getElem_mem _)
  have h31le := (h31).le
  have h31nle := not_le.mpr h31
  have h32 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2,1])++[3]) < lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,1])++[3]) := h ((lowerBridgeRecords .aZero)[32]'(by decide)) (List.getElem_mem _)
  have h32le := (h32).le
  have h32nle := not_le.mpr h32
  have h34 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[34]'(by decide)) (List.getElem_mem _)
  have h34le := (h34).le
  have h34nle := not_le.mpr h34
  have h35 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[35]'(by decide)) (List.getElem_mem _)
  have h35le := (h35).le
  have h35nle := not_le.mpr h35
  have h36 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[36]'(by decide)) (List.getElem_mem _)
  have h36le := (h36).le
  have h36nle := not_le.mpr h36
  have h37 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[37]'(by decide)) (List.getElem_mem _)
  have h37le := (h37).le
  have h37nle := not_le.mpr h37
  have h39 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[39]'(by decide)) (List.getElem_mem _)
  have h39le := (h39).le
  have h39nle := not_le.mpr h39
  have h40 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aZero)[40]'(by decide)) (List.getElem_mem _)
  have h40le := (h40).le
  have h40nle := not_le.mpr h40
  have h41 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[41]'(by decide)) (List.getElem_mem _)
  have h41le := (h41).le
  have h41nle := not_le.mpr h41
  have h43 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[43]'(by decide)) (List.getElem_mem _)
  have h43le := (h43).le
  have h43nle := not_le.mpr h43
  have h44 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[44]'(by decide)) (List.getElem_mem _)
  have h44le := (h44).le
  have h44nle := not_le.mpr h44
  have h45 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1]) := h ((lowerBridgeRecords .aZero)[45]'(by decide)) (List.getElem_mem _)
  have h45le := (h45).le
  have h45nle := not_le.mpr h45
  have h46 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[46]'(by decide)) (List.getElem_mem _)
  have h46le := (h46).le
  have h46nle := not_le.mpr h46
  have h48 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[48]'(by decide)) (List.getElem_mem _)
  have h48le := (h48).le
  have h48nle := not_le.mpr h48
  have h49 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,1]) := h ((lowerBridgeRecords .aZero)[49]'(by decide)) (List.getElem_mem _)
  have h49le := (h49).le
  have h49nle := not_le.mpr h49
  have h50 : lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[50]'(by decide)) (List.getElem_mem _)
  have h50le := (h50).le
  have h50nle := not_le.mpr h50
  have h52 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[52]'(by decide)) (List.getElem_mem _)
  have h52le := (h52).le
  have h52nle := not_le.mpr h52
  have h54 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aZero)[54]'(by decide)) (List.getElem_mem _)
  have h54le := (h54).le
  have h54nle := not_le.mpr h54
  have h55 : lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,3,3])++[3]) := h ((lowerBridgeRecords .aZero)[55]'(by decide)) (List.getElem_mem _)
  have h56 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[56]'(by decide)) (List.getElem_mem _)
  have h56le := (h56).le
  have h56nle := not_le.mpr h56
  have h58 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3]) := h ((lowerBridgeRecords .aZero)[58]'(by decide)) (List.getElem_mem _)
  have h58le := (h58).le
  have h58nle := not_le.mpr h58
  have h59 : lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3])++[3]) := h ((lowerBridgeRecords .aZero)[59]'(by decide)) (List.getElem_mem _)
  have h60 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2]) := h ((lowerBridgeRecords .aZero)[60]'(by decide)) (List.getElem_mem _)
  have h60le := (h60).le
  have h60nle := not_le.mpr h60
  have h61 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2])++[1,3]) < lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2])++[1,3]) := h ((lowerBridgeRecords .aZero)[61]'(by decide)) (List.getElem_mem _)
  have h61le := (h61).le
  have h61nle := not_le.mpr h61
  have h63 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2]) := h ((lowerBridgeRecords .aZero)[63]'(by decide)) (List.getElem_mem _)
  have h63le := (h63).le
  have h63nle := not_le.mpr h63
  have h64 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2])++[3]) < lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2])++[3]) := h ((lowerBridgeRecords .aZero)[64]'(by decide)) (List.getElem_mem _)
  have h64le := (h64).le
  have h64nle := not_le.mpr h64
  have h65 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[65]'(by decide)) (List.getElem_mem _)
  have h65le := (h65).le
  have h65nle := not_le.mpr h65
  have h66 : lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3])++[3]) := h ((lowerBridgeRecords .aZero)[66]'(by decide)) (List.getElem_mem _)
  have h68 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aZero)[68]'(by decide)) (List.getElem_mem _)
  have h68le := (h68).le
  have h68nle := not_le.mpr h68
  have h69 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[69]'(by decide)) (List.getElem_mem _)
  have h69le := (h69).le
  have h69nle := not_le.mpr h69
  have h70 : lowerWidth (((lowerBridgePair .aZero n 0).1++[1,2,1,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aZero n 0).2++[1,2,1,3])++[3]) := h ((lowerBridgeRecords .aZero)[70]'(by decide)) (List.getElem_mem _)
  have h72 : lowerWidth ((lowerBridgePair .aZero n 0).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aZero n 0).1++[1,2,1,3]) := h ((lowerBridgeRecords .aZero)[72]'(by decide)) (List.getElem_mem _)
  have h72le := (h72).le
  have h72nle := not_le.mpr h72
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h0le h0nle h3 h3le h3nle h4 h5 h5le h5nle h6 h6le h6nle h7 h7le h7nle h8 h8le h8nle h10 h10le h10nle h11 h11le h11nle h12 h12le h12nle h14 h14le h14nle h15 h15le h15nle h16 h16le h16nle h17 h17le h17nle h19 h19le h19nle h20 h20le h20nle h21 h21le h21nle h23 h23le h23nle h24 h24le h24nle h25 h25le h25nle h26 h26le h26nle h27 h27le h27nle h29 h29le h29nle h30 h30le h30nle h31 h31le h31nle h32 h32le h32nle h34 h34le h34nle h35 h35le h35nle h36 h36le h36nle h37 h37le h37nle h39 h39le h39nle h40 h40le h40nle h41 h41le h41nle h43 h43le h43nle h44 h44le h44nle h45 h45le h45nle h46 h46le h46nle h48 h48le h48nle h49 h49le h49nle h50 h50le h50nle h52 h52le h52nle h54 h54le h54nle h55 h56 h56le h56nle h58 h58le h58nle h59 h60 h60le h60nle h61 h61le h61nle h63 h63le h63nle h64 h64le h64nle h65 h65le h65nle h66 h68 h68le h68nle h69 h69le h69nle h70 h72 h72le h72nle
  have f57 : 0 < (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length *
      (prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3]) lowerTau + prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,1,2,1,3]) lowerTau - prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3,1,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aZero)[57]'(by decide)) (List.getElem_mem _)
  have f62 : 0 < (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length *
      (prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3,3]) lowerTau + prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,3,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,1,3]) lowerTau - prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aZero)[62]'(by decide)) (List.getElem_mem _)
  have f67 : 0 < (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length *
      (prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,1,3,1,2,2,3]) lowerTau + prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,2,1,3,1,3,2,3]) lowerTau -
       prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,3]) lowerTau - prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aZero)[67]'(by decide)) (List.getElem_mem _)
  have f71 : 0 < (-1:ℝ)^(lowerBridgePair .aZero n 0).1.length *
      (prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,3,3,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aZero n 0).1++[1,2,1,3,3]) lowerTau - prefixEval ((lowerBridgePair .aZero n 0).2++[1,2,1,3,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aZero)[71]'(by decide)) (List.getElem_mem _)
  obtain ⟨scale, hs, hm1, hm2⟩ := OtherBridge.bridge_link .aZero n 0 (OtherBridge.family_matrix .aZero n 0 hc)
  have hx := Freiman.lower_initial_period_ratio n
  have hpar : (-1:ℝ)^(lowerBridgePair .aZero n 0).2.length =
      (if false then -1 else 1)*(-1:ℝ)^(lowerBridgePair .aZero n 0).1.length := by
    simpa using OtherBridge.pow_par _ _ hp.symm
  have r0 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aZero n 0) ([1,2,1,3,3,3,3,3],[1,2,1,3,3,3,3,2,1,3]) ([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3])
    (lowerBridgeMatrices .aZero (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aZero_0 (lowerInitialX n) hx.1 hx.2.2)
  have r1 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aZero n 0) ([1,2,1,3,1,3,1,2,2,3],[1,2,1,2,1,3,1,3,2,3]) ([1,2,1,3,3,3,3,1,2,1,3],[1,2,1,3,3,3,3,1,2,1,3])
    (lowerBridgeMatrices .aZero (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aZero_1 (lowerInitialX n) hx.1 hx.2.2)
  have r2 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aZero n 0) ([1,2,1,3,3,3,1,2,1,3],[1,2,1,3,3,3,1,2,1,3]) ([1,2,1,3,1,3,1,2,2,1,3],[1,2,1,2,1,3,1,3,2,1,3])
    (lowerBridgeMatrices .aZero (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aZero_2 (lowerInitialX n) hx.1 hx.2.2)
  have r3 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aZero n 0) ([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3]) ([1,2,1,3,3,3,3],[1,2,1,3,3,3,2,1,3])
    (lowerBridgeMatrices .aZero (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aZero_3 (lowerInitialX n) hx.1 hx.2.2)
  simp only [lowerBridgeLabels, if_pos rfl, ite_true, List.isChain_cons_cons, List.isChain_singleton, and_true, if_false, one_ne_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply covers_overlap _ _ ho
    rcases Nat.mod_two_eq_zero_or_one (lowerBridgePair .aZero n 0).1.length with hp0 | hp0
    all_goals
      have hp2 : (lowerBridgePair .aZero n 0).2.length % 2 = (lowerBridgePair .aZero n 0).1.length % 2 := hp.symm
      rw [pow_mod, hp0] at f57 f62 f67 f71 r0 r1 r2 r3
      norm_num at f57 f62 f67 f71 r0 r1 r2 r3
      simp [lowerBridgeAppend,lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerNormalize, lowerEnds, ends_append, List.suffix_cons_iff, List.length_append,
        hp2, hp0, Nat.add_mod, List.append_assoc, h0, h0le, h0nle, h3, h3le, h3nle, h4, h5, h5le, h5nle, h6, h6le, h6nle, h7, h7le, h7nle, h8, h8le, h8nle, h10, h10le, h10nle, h11, h11le, h11nle, h12, h12le, h12nle, h14, h14le, h14nle, h15, h15le, h15nle, h16, h16le, h16nle, h17, h17le, h17nle, h19, h19le, h19nle, h20, h20le, h20nle, h21, h21le, h21nle, h23, h23le, h23nle, h24, h24le, h24nle, h25, h25le, h25nle, h26, h26le, h26nle, h27, h27le, h27nle, h29, h29le, h29nle, h30, h30le, h30nle, h31, h31le, h31nle, h32, h32le, h32nle, h34, h34le, h34nle, h35, h35le, h35nle, h36, h36le, h36nle, h37, h37le, h37nle, h39, h39le, h39nle, h40, h40le, h40nle, h41, h41le, h41nle, h43, h43le, h43nle, h44, h44le, h44nle, h45, h45le, h45nle, h46, h46le, h46nle, h48, h48le, h48nle, h49, h49le, h49nle, h50, h50le, h50nle, h52, h52le, h52nle, h54, h54le, h54nle, h55, h56, h56le, h56nle, h58, h58le, h58nle, h59, h60, h60le, h60nle, h61, h61le, h61nle, h63, h63le, h63nle, h64, h64le, h64nle, h65, h65le, h65nle, h66, h68, h68le, h68nle, h69, h69le, h69nle, h70, h72, h72le, h72nle]
      constructor <;> linarith only [f57, f62, f67, f71, r0, r1, r2, r3]
private theorem chain_aPos (n : ℕ) (hc : lowerBridgeZero .aPos = decide (n=0))
    (h : lowerBridgeFacts .aPos n 0) (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true) :
    (lowerBridgeLabels .A 1).IsChain (fun a b =>
      (lowerCover (lowerBridgeAppend (lowerBridgePair .aPos n 0) a) ∩
        lowerCover (lowerBridgeAppend (lowerBridgePair .aPos n 0) b)).Nonempty) := by
  have hp := bridge_parity LowerBridgeCase.aPos n 0
  have h0 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1]) := h ((lowerBridgeRecords .aPos)[0]'(by decide)) (List.getElem_mem _)
  have h0le := (h0).le
  have h0nle := not_le.mpr h0
  have h3 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2]) := h ((lowerBridgeRecords .aPos)[3]'(by decide)) (List.getElem_mem _)
  have h3le := (h3).le
  have h3nle := not_le.mpr h3
  have h4 : lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2])++[1,3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2])++[1,3]) := h ((lowerBridgeRecords .aPos)[4]'(by decide)) (List.getElem_mem _)
  have h5 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[5]'(by decide)) (List.getElem_mem _)
  have h5le := (h5).le
  have h5nle := not_le.mpr h5
  have h6 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[6]'(by decide)) (List.getElem_mem _)
  have h6le := (h6).le
  have h6nle := not_le.mpr h6
  have h7 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[7]'(by decide)) (List.getElem_mem _)
  have h7le := (h7).le
  have h7nle := not_le.mpr h7
  have h8 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aPos)[8]'(by decide)) (List.getElem_mem _)
  have h8le := (h8).le
  have h8nle := not_le.mpr h8
  have h10 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[10]'(by decide)) (List.getElem_mem _)
  have h10le := (h10).le
  have h10nle := not_le.mpr h10
  have h11 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[11]'(by decide)) (List.getElem_mem _)
  have h11le := (h11).le
  have h11nle := not_le.mpr h11
  have h12 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,1]) := h ((lowerBridgeRecords .aPos)[12]'(by decide)) (List.getElem_mem _)
  have h12le := (h12).le
  have h12nle := not_le.mpr h12
  have h14 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1]) := h ((lowerBridgeRecords .aPos)[14]'(by decide)) (List.getElem_mem _)
  have h14le := (h14).le
  have h14nle := not_le.mpr h14
  have h15 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,1]) := h ((lowerBridgeRecords .aPos)[15]'(by decide)) (List.getElem_mem _)
  have h15le := (h15).le
  have h15nle := not_le.mpr h15
  have h16 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,1,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aPos)[16]'(by decide)) (List.getElem_mem _)
  have h16le := (h16).le
  have h16nle := not_le.mpr h16
  have h17 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,1,1])++[3]) < lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2])++[3]) := h ((lowerBridgeRecords .aPos)[17]'(by decide)) (List.getElem_mem _)
  have h17le := (h17).le
  have h17nle := not_le.mpr h17
  have h18 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aPos)[18]'(by decide)) (List.getElem_mem _)
  have h18le := (h18).le
  have h18nle := not_le.mpr h18
  have h19 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2,1]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,2]) := h ((lowerBridgeRecords .aPos)[19]'(by decide)) (List.getElem_mem _)
  have h19le := (h19).le
  have h19nle := not_le.mpr h19
  have h20 : lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,2])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2,1])++[3]) := h ((lowerBridgeRecords .aPos)[20]'(by decide)) (List.getElem_mem _)
  have h22 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) := h ((lowerBridgeRecords .aPos)[22]'(by decide)) (List.getElem_mem _)
  have h22le := (h22).le
  have h22nle := not_le.mpr h22
  have h23 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,1]) := h ((lowerBridgeRecords .aPos)[23]'(by decide)) (List.getElem_mem _)
  have h23le := (h23).le
  have h23nle := not_le.mpr h23
  have h25 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[25]'(by decide)) (List.getElem_mem _)
  have h25le := (h25).le
  have h25nle := not_le.mpr h25
  have h26 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[26]'(by decide)) (List.getElem_mem _)
  have h26le := (h26).le
  have h26nle := not_le.mpr h26
  have h27 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aPos)[27]'(by decide)) (List.getElem_mem _)
  have h27le := (h27).le
  have h27nle := not_le.mpr h27
  have h28 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[28]'(by decide)) (List.getElem_mem _)
  have h28le := (h28).le
  have h28nle := not_le.mpr h28
  have h30 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[30]'(by decide)) (List.getElem_mem _)
  have h30le := (h30).le
  have h30nle := not_le.mpr h30
  have h31 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3,1]) := h ((lowerBridgeRecords .aPos)[31]'(by decide)) (List.getElem_mem _)
  have h31le := (h31).le
  have h31nle := not_le.mpr h31
  have h32 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[32]'(by decide)) (List.getElem_mem _)
  have h32le := (h32).le
  have h32nle := not_le.mpr h32
  have h34 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[34]'(by decide)) (List.getElem_mem _)
  have h34le := (h34).le
  have h34nle := not_le.mpr h34
  have h35 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[35]'(by decide)) (List.getElem_mem _)
  have h35le := (h35).le
  have h35nle := not_le.mpr h35
  have h36 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1]) := h ((lowerBridgeRecords .aPos)[36]'(by decide)) (List.getElem_mem _)
  have h36le := (h36).le
  have h36nle := not_le.mpr h36
  have h37 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[37]'(by decide)) (List.getElem_mem _)
  have h37le := (h37).le
  have h37nle := not_le.mpr h37
  have h39 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[39]'(by decide)) (List.getElem_mem _)
  have h39le := (h39).le
  have h39nle := not_le.mpr h39
  have h40 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,1]) := h ((lowerBridgeRecords .aPos)[40]'(by decide)) (List.getElem_mem _)
  have h40le := (h40).le
  have h40nle := not_le.mpr h40
  have h41 : lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1]) < lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[41]'(by decide)) (List.getElem_mem _)
  have h41le := (h41).le
  have h41nle := not_le.mpr h41
  have h43 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[43]'(by decide)) (List.getElem_mem _)
  have h43le := (h43).le
  have h43nle := not_le.mpr h43
  have h45 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3]) := h ((lowerBridgeRecords .aPos)[45]'(by decide)) (List.getElem_mem _)
  have h45le := (h45).le
  have h45nle := not_le.mpr h45
  have h46 : lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,3,3])++[3]) := h ((lowerBridgeRecords .aPos)[46]'(by decide)) (List.getElem_mem _)
  have h47 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1]) := h ((lowerBridgeRecords .aPos)[47]'(by decide)) (List.getElem_mem _)
  have h47le := (h47).le
  have h47nle := not_le.mpr h47
  have h48 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2])++[1,3]) < lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1])++[1,3]) := h ((lowerBridgeRecords .aPos)[48]'(by decide)) (List.getElem_mem _)
  have h48le := (h48).le
  have h48nle := not_le.mpr h48
  have h50 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1]) := h ((lowerBridgeRecords .aPos)[50]'(by decide)) (List.getElem_mem _)
  have h50le := (h50).le
  have h50nle := not_le.mpr h50
  have h51 : (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2])++[3]) < lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1])++[3]) := h ((lowerBridgeRecords .aPos)[51]'(by decide)) (List.getElem_mem _)
  have h51le := (h51).le
  have h51nle := not_le.mpr h51
  have h52 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[52]'(by decide)) (List.getElem_mem _)
  have h52le := (h52).le
  have h52nle := not_le.mpr h52
  have h53 : lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3])++[3]) := h ((lowerBridgeRecords .aPos)[53]'(by decide)) (List.getElem_mem _)
  have h55 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3]) := h ((lowerBridgeRecords .aPos)[55]'(by decide)) (List.getElem_mem _)
  have h55le := (h55).le
  have h55nle := not_le.mpr h55
  have h56 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[56]'(by decide)) (List.getElem_mem _)
  have h56le := (h56).le
  have h56nle := not_le.mpr h56
  have h57 : lowerWidth (((lowerBridgePair .aPos n 0).1++[1,2,1,3])++[3]) ≤ (7/5:ℝ)*lowerWidth (((lowerBridgePair .aPos n 0).2++[1,2,1,3])++[3]) := h ((lowerBridgeRecords .aPos)[57]'(by decide)) (List.getElem_mem _)
  have h59 : lowerWidth ((lowerBridgePair .aPos n 0).2++[1,2,1,3]) < lowerWidth ((lowerBridgePair .aPos n 0).1++[1,2,1,3]) := h ((lowerBridgeRecords .aPos)[59]'(by decide)) (List.getElem_mem _)
  have h59le := (h59).le
  have h59nle := not_le.mpr h59
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h0le h0nle h3 h3le h3nle h4 h5 h5le h5nle h6 h6le h6nle h7 h7le h7nle h8 h8le h8nle h10 h10le h10nle h11 h11le h11nle h12 h12le h12nle h14 h14le h14nle h15 h15le h15nle h16 h16le h16nle h17 h17le h17nle h18 h18le h18nle h19 h19le h19nle h20 h22 h22le h22nle h23 h23le h23nle h25 h25le h25nle h26 h26le h26nle h27 h27le h27nle h28 h28le h28nle h30 h30le h30nle h31 h31le h31nle h32 h32le h32nle h34 h34le h34nle h35 h35le h35nle h36 h36le h36nle h37 h37le h37nle h39 h39le h39nle h40 h40le h40nle h41 h41le h41nle h43 h43le h43nle h45 h45le h45nle h46 h47 h47le h47nle h48 h48le h48nle h50 h50le h50nle h51 h51le h51nle h52 h52le h52nle h53 h55 h55le h55nle h56 h56le h56nle h57 h59 h59le h59nle
  have f49 : 0 < (-1:ℝ)^(lowerBridgePair .aPos n 0).1.length *
      (prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3]) lowerTau + prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,1,3]) lowerTau - prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aPos)[49]'(by decide)) (List.getElem_mem _)
  have f54 : 0 < (-1:ℝ)^(lowerBridgePair .aPos n 0).1.length *
      (prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,1,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,2,1,3,1,3,2,3]) lowerTau -
       prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,3]) lowerTau - prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aPos)[54]'(by decide)) (List.getElem_mem _)
  have f58 : 0 < (-1:ℝ)^(lowerBridgePair .aPos n 0).1.length *
      (prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3,3,1,2,1,3]) lowerTau + prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3,3,3,1,2,1,3]) lowerTau -
       prefixEval ((lowerBridgePair .aPos n 0).1++[1,2,1,3,3]) lowerTau - prefixEval ((lowerBridgePair .aPos n 0).2++[1,2,1,3,2,1,3]) lowerTau) :=
    h ((lowerBridgeRecords .aPos)[58]'(by decide)) (List.getElem_mem _)
  obtain ⟨scale, hs, hm1, hm2⟩ := OtherBridge.bridge_link .aPos n 0 (OtherBridge.family_matrix .aPos n 0 hc)
  have hx := Freiman.lower_initial_period_ratio n
  have hpar : (-1:ℝ)^(lowerBridgePair .aPos n 0).2.length =
      (if false then -1 else 1)*(-1:ℝ)^(lowerBridgePair .aPos n 0).1.length := by
    simpa using OtherBridge.pow_par _ _ hp.symm
  have r0 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aPos n 0) ([1,2,1,3,1,3,1,2,1,3],[1,2,1,2,1,3,1,3,2,3]) ([1,2,1,3,3,1,2,1,3],[1,2,1,3,3,1,2,1,3])
    (lowerBridgeMatrices .aPos (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aPos_0 (lowerInitialX n) hx.1 hx.2.2)
  have r1 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aPos n 0) ([1,2,1,3,3,3,1,2,1,3],[1,2,1,3,3,3,1,2,1,3]) ([1,2,1,3,1,3,1,2,1,1,3],[1,2,1,2,1,3,1,3,2,1,3])
    (lowerBridgeMatrices .aPos (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aPos_1 (lowerInitialX n) hx.1 hx.2.2)
  have r2 := OtherBridge.contact_generic OtherBridge.wf (lowerBridgePair .aPos n 0) ([1,2,1,3,1,2,1,3],[1,2,1,3,1,2,1,3]) ([1,2,1,3,3,3,3],[1,2,1,3,3,3,2,1,3])
    (lowerBridgeMatrices .aPos (lowerInitialX n) (lowerInitialY 0)) scale hs hm1 hm2 false hpar
    (by simpa [lowerInitialY, lowerInitialV] using OtherBridgeReverse.numeric_aPos_2 (lowerInitialX n) hx.1 hx.2.2)
  simp only [lowerBridgeLabels, if_pos rfl, ite_true, List.isChain_cons_cons, List.isChain_singleton, and_true, if_false, one_ne_zero]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply covers_overlap _ _ ho
    rcases Nat.mod_two_eq_zero_or_one (lowerBridgePair .aPos n 0).1.length with hp0 | hp0
    all_goals
      have hp2 : (lowerBridgePair .aPos n 0).2.length % 2 = (lowerBridgePair .aPos n 0).1.length % 2 := hp.symm
      rw [pow_mod, hp0] at f49 f54 f58 r0 r1 r2
      norm_num at f49 f54 f58 r0 r1 r2
      simp [lowerBridgeAppend,lowerEndpoint, lowerEndpointWords, lowerEqualWords, lowerNaturalWords, lowerNaturalShort,
        lowerEndpointSuffix, lowerNormalize, lowerEnds, ends_append, List.suffix_cons_iff, List.length_append,
        hp2, hp0, Nat.add_mod, List.append_assoc, h0, h0le, h0nle, h3, h3le, h3nle, h4, h5, h5le, h5nle, h6, h6le, h6nle, h7, h7le, h7nle, h8, h8le, h8nle, h10, h10le, h10nle, h11, h11le, h11nle, h12, h12le, h12nle, h14, h14le, h14nle, h15, h15le, h15nle, h16, h16le, h16nle, h17, h17le, h17nle, h18, h18le, h18nle, h19, h19le, h19nle, h20, h22, h22le, h22nle, h23, h23le, h23nle, h25, h25le, h25nle, h26, h26le, h26nle, h27, h27le, h27nle, h28, h28le, h28nle, h30, h30le, h30nle, h31, h31le, h31nle, h32, h32le, h32nle, h34, h34le, h34nle, h35, h35le, h35nle, h36, h36le, h36nle, h37, h37le, h37nle, h39, h39le, h39nle, h40, h40le, h40nle, h41, h41le, h41nle, h43, h43le, h43nle, h45, h45le, h45nle, h46, h47, h47le, h47nle, h48, h48le, h48nle, h50, h50le, h50nle, h51, h51le, h51nle, h52, h52le, h52nle, h53, h55, h55le, h55nle, h56, h56le, h56nle, h57, h59, h59le, h59nle]
      constructor <;> linarith only [f49, f54, f58, r0, r1, r2]
end OtherBridgeEndpoint

theorem solution (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) (h : lowerBridgeFacts c n 0) (he : lowerBridgeEndpointFacts c n 0) (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true) : (lowerBridgeLabels (lowerBridgeFamily c) n).IsChain (fun a b => (lowerCover (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) a) ∩ lowerCover (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) b)).Nonempty) := by
  cases c with
  | aZero =>
    have hn : n = 0 := by simpa [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero] using hc.symm
    subst n
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeAppend,
      lowerBridgePair, lowerBridgeK, lowerPhysicalAdd] using OtherBridgeEndpoint.chain_aZero 0 hc h ho
  | aPos =>
    have hn : n ≠ 0 := by simpa [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero] using hc.symm
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeAppend,
      lowerBridgePair, lowerBridgeK, lowerPhysicalAdd, lowerBridgeLabels, hn] using
        OtherBridgeEndpoint.chain_aPos n hc h ho
  | bZero => simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeLabels]
  | bPos => simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily, lowerBridgeLabels]
  | cZero => exact False.elim (hf rfl)
  | cPos => exact False.elim (hf rfl)
#print axioms solution

example : (∀ (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) (h : lowerBridgeFacts c n 0) (he : lowerBridgeEndpointFacts c n 0) (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true) ,  (lowerBridgeLabels (lowerBridgeFamily c) n).IsChain (fun a b => (lowerCover (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) a) ∩ lowerCover (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) b)).Nonempty)) := @solution
