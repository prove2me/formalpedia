-- Prove2me | solution 1 for BasicCutDiscardedResolutionGeneral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:50.800914+00:00
-- url     : https://prove2.me/submissions/99c78067-fc8e-4cc2-83cd-dc79490a7a15

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_GeodesicIsPiecewiseGeodesic


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len)
    (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) (hne : t ≠ t')
    (kA : ℕ) (sA : ℕ → ℝ)
    (hresA : IsGeodesicResolution (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) kA sA) :
    IsPiecewiseGeodesicWith (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 (kA + 1) := by
-- BODY
  classical
  -- (0) The circular arc `γ|_{[a,b]}` ends at `γ(b)` (the same fact `BasicCut` establishes
  -- internally to see that its two concatenations are well defined).
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
  -- (1) The endpoint match for the concatenation defining `g`.
  have hend : (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).toFun
      (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
        = (GP.G (γ.toFun t') (γ.toFun t)).toFun 0 := by
    rw [harcEnd, GP.start_eq]
  -- (2) The single closing geodesic edge is resolved by one edge.
  obtain ⟨r, hr⟩ := GeodesicIsPiecewiseGeodesic GP (γ.toFun t') (γ.toFun t)
  -- (3) Glue the arc's resolution to that one edge.
  have key := ConcatGeodesicResolution (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len)
      (GP.G (γ.toFun t') (γ.toFun t)) hend kA 1 sA r hresA hr
  exact ⟨_, key⟩
