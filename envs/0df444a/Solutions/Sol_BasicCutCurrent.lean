-- Prove2me | solution 1 for BasicCutCurrent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:23.646997+00:00
-- url     : https://prove2.me/submissions/6ce5c97e-8c64-48d1-93a3-355e72e9efb7

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentReverse
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_BasicCutCurrent
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurrentReverse
import Theorems.Thm_RestrictCurrentFormula


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t')
    (ht'len : t' ≤ γ.len) (hne : t ≠ t') (ω : Form1 E) :
    curveCurrent γ ω = curveCurrent (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ω
      + curveCurrent (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 ω := by
-- BODY
  -- (0) Endpoint of a circular arc: `γ|_{[a,b]}` ends at `γ(b)`.
  have harcEnd : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b) (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha0 hal hb0 hbl).toFun (curveArc γ hclosed a b ha0 hal hb0 hbl).len
        = γ.toFun b := by
    intro a b ha0 hal hb0 hbl
    have hRestrict_len : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
        (curveRestrict γ p q hp hpq hq).len = q - p := fun _ _ _ _ _ => rfl
    have hRestrict_toFun_len : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
        (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
      intro p q hp hpq hq
      show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
      rw [max_eq_right (by linarith), min_self]
      congr 1
      ring
    unfold curveArc
    split_ifs with h
    · exact hRestrict_toFun_len a b ha0 h hbl
    · have hbt : b < a := not_le.mp h
      have hlen : (curveWrapRestrict γ a b hclosed ha0 hal hb0 hbt).len = (γ.len - a) + b := by
        show (curveRestrict γ a γ.len ha0 hal (le_refl _)).len
            + (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)).len = (γ.len - a) + b
        rw [hRestrict_len, hRestrict_len]
        ring_nf
      rw [hlen]
      show (if ((γ.len - a) + b) ≤ (curveRestrict γ a γ.len ha0 hal (le_refl _)).len
          then (curveRestrict γ a γ.len ha0 hal (le_refl _)).toFun ((γ.len - a) + b)
          else (curveRestrict γ 0 b (le_refl 0) hb0 (by linarith)).toFun
            (((γ.len - a) + b) - (curveRestrict γ a γ.len ha0 hal (le_refl _)).len))
          = γ.toFun b
      rw [hRestrict_len]
      rcases eq_or_lt_of_le hb0 with hbeq | hbpos
      · rw [if_pos (by linarith)]
        have harg : a + min (γ.len - a) (max 0 (γ.len - a + b)) = γ.len := by
          rw [max_eq_right (by linarith), min_eq_right (by linarith)]
          linarith
        show γ.toFun (a + min (γ.len - a) (max 0 (γ.len - a + b))) = γ.toFun b
        rw [harg, ← hbeq]
        exact hclosed
      · rw [if_neg (by linarith)]
        have harg : (γ.len - a) + b - (γ.len - a) = b := by ring
        rw [harg]
        have h1 := hRestrict_toFun_len 0 b (le_refl 0) hb0 (by linarith)
        simp only [hRestrict_len, sub_zero] at h1
        exact h1
  -- (a) Three-arc recombination: cutting `[0,len]` at `a ≤ b` splits `[[γ]]` into three pieces.
  -- The proof arguments are taken explicitly so that instantiations match the goal syntactically.
  have hthree : ∀ (a b : ℝ) (p1 : (0:ℝ) ≤ 0) (p2 : (0:ℝ) ≤ a) (p3 : a ≤ γ.len)
      (p4 : (0:ℝ) ≤ a) (p5 : a ≤ b) (p6 : b ≤ γ.len)
      (p7 : (0:ℝ) ≤ b) (p8 : b ≤ γ.len) (p9 : γ.len ≤ γ.len),
      curveCurrent γ ω = curveCurrent (curveRestrict γ 0 a p1 p2 p3) ω
        + curveCurrent (curveRestrict γ a b p4 p5 p6) ω
        + curveCurrent (curveRestrict γ b γ.len p7 p8 p9) ω := by
    intro a b p1 p2 p3 p4 p5 p6 p7 p8 p9
    have hmono : MonotoneOn (fun i : ℕ => if i = 0 then (0:ℝ) else if i = 1 then a else
        if i = 2 then b else γ.len) (Set.Icc 0 3) := by
      intro x hx y hy hxy
      obtain ⟨-, hx3⟩ := hx
      obtain ⟨-, hy3⟩ := hy
      interval_cases x <;> interval_cases y <;> norm_num <;> linarith
    have hres := CurrentResolutionAdditive γ ω 3 _ hmono (by norm_num) (by norm_num)
    rw [RestrictCurrentFormula, RestrictCurrentFormula, RestrictCurrentFormula, hres,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  -- (b) The two closing geodesic edges cancel.
  have hcancel : ∀ x y : E, curveCurrent (GP.G y x) ω = - curveCurrent (GP.G x y) ω := by
    intro x y
    refine CurrentReverse (GP.G x y) (GP.G y x) ?_ ?_ ω
    · rw [GP.len_eq, GP.len_eq, dist_comm]
    · intro s hs
      rw [GP.len_eq] at hs ⊢
      exact GP.reversal x y s hs
  -- The two components of `BasicCut` are concatenations, so `CurrentConcatAdditive` applies.
  have hP1 : curveCurrent (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ω
      = curveCurrent (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen) ω
        + curveCurrent (GP.G (γ.toFun t) (γ.toFun t')) ω :=
    CurrentConcatAdditive _ _ (by rw [harcEnd, GP.start_eq]) ω
  have hP2 : curveCurrent (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 ω
      = curveCurrent (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) ω
        + curveCurrent (GP.G (γ.toFun t') (γ.toFun t)) ω :=
    CurrentConcatAdditive _ _ (by rw [harcEnd, GP.start_eq]) ω
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · -- Case `t < t'`: the arc from `t'` to `t` wraps around.
    have harcA : curveArc γ hclosed t' t ht'0 ht'len ht0 htlen
        = curveWrapRestrict γ t' t hclosed ht'0 ht'len ht0 hlt := dif_neg (not_le.mpr hlt)
    have harcB : curveArc γ hclosed t t' ht0 htlen ht'0 ht'len
        = curveRestrict γ t t' ht0 hlt.le ht'len := dif_pos hlt.le
    have hwrap : curveCurrent (curveWrapRestrict γ t' t hclosed ht'0 ht'len ht0 hlt) ω
        = curveCurrent (curveRestrict γ t' γ.len ht'0 ht'len (le_refl γ.len)) ω
          + curveCurrent (curveRestrict γ 0 t (le_refl 0) ht0 htlen) ω :=
      CurrentConcatAdditive _ _ _ ω
    rw [hP1, hP2, harcA, harcB, hwrap, hcancel (γ.toFun t) (γ.toFun t'),
      hthree t t' (le_refl 0) ht0 htlen ht0 hlt.le ht'len ht'0 ht'len (le_refl γ.len)]
    ring
  · exact absurd heq hne
  · -- Case `t' < t`: the arc from `t` to `t'` wraps around.
    have harcA : curveArc γ hclosed t' t ht'0 ht'len ht0 htlen
        = curveRestrict γ t' t ht'0 hgt.le htlen := dif_pos hgt.le
    have harcB : curveArc γ hclosed t t' ht0 htlen ht'0 ht'len
        = curveWrapRestrict γ t t' hclosed ht0 htlen ht'0 hgt := dif_neg (not_le.mpr hgt)
    have hwrap : curveCurrent (curveWrapRestrict γ t t' hclosed ht0 htlen ht'0 hgt) ω
        = curveCurrent (curveRestrict γ t γ.len ht0 htlen (le_refl γ.len)) ω
          + curveCurrent (curveRestrict γ 0 t' (le_refl 0) ht'0 ht'len) ω :=
      CurrentConcatAdditive _ _ _ ω
    rw [hP1, hP2, harcA, harcB, hwrap, hcancel (γ.toFun t) (γ.toFun t'),
      hthree t' t (le_refl 0) ht'0 ht'len ht'0 hgt.le htlen ht0 htlen (le_refl γ.len)]
    ring
