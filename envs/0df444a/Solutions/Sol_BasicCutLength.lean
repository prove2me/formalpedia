-- Prove2me | solution 1 for BasicCutLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:11.674731+00:00
-- url     : https://prove2.me/submissions/55715be9-82b6-4827-ba3a-4d72181185c1

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutLength
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t')
    (ht'len : t' ≤ γ.len) (hne : t ≠ t') :
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1.len
        = γ.len - (if t ≤ t' then t' - t else (γ.len - t) + t')
          + dist (γ.toFun t) (γ.toFun t') ∧
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len
        = (if t ≤ t' then t' - t else (γ.len - t) + t') + dist (γ.toFun t) (γ.toFun t') ∧
    dist (γ.toFun t) (γ.toFun t') ≤ (if t ≤ t' then t' - t else (γ.len - t) + t') := by
-- BODY
  have harc_len : ∀ (a b : ℝ) (ha : 0 ≤ a) (hal : a ≤ γ.len) (hb : 0 ≤ b) (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha hal hb hbl).len = if a ≤ b then b - a else (γ.len - a) + b := by
    intro a b ha hal hb hbl
    unfold curveArc
    split_ifs with h
    · rfl
    · show (γ.len - a) + (b - 0) = (γ.len - a) + b
      ring
  have hlen1 : (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen).len
      = if t' ≤ t then t - t' else (γ.len - t') + t := harc_len t' t ht'0 ht'len ht0 htlen
  have hlen2 : (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
      = if t ≤ t' then t' - t else (γ.len - t) + t' := harc_len t t' ht0 htlen ht'0 ht'len
  have hlip : ∀ x y : ℝ, dist (γ.toFun x) (γ.toFun y) ≤ |x - y| := by
    intro x y
    have h := (CurveLipschitz γ).dist_le_mul x y
    simpa [Real.dist_eq] using h
  have htorder : t < t' ∨ t' < t := by
    rcases le_total t t' with h | h
    · exact Or.inl (h.lt_of_ne hne)
    · exact Or.inr (h.lt_of_ne hne.symm)
  have hd : dist (γ.toFun t) (γ.toFun t') ≤ if t ≤ t' then t' - t else (γ.len - t) + t' := by
    rcases htorder with h | h
    · rw [if_pos h.le]
      have h1 := hlip t t'
      rw [abs_of_nonpos (by linarith : t - t' ≤ 0)] at h1
      linarith
    · rw [if_neg (not_le.mpr h)]
      have htri := dist_triangle (γ.toFun t) (γ.toFun γ.len) (γ.toFun t')
      have h1 := hlip t γ.len
      rw [abs_of_nonpos (by linarith : t - γ.len ≤ 0)] at h1
      have h2 := hlip 0 t'
      rw [abs_of_nonpos (by linarith : (0:ℝ) - t' ≤ 0)] at h2
      rw [← hclosed] at h2
      linarith
  refine ⟨?_, ?_, hd⟩
  · show (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen).len
        + (GP.G (γ.toFun t) (γ.toFun t')).len
        = γ.len - (if t ≤ t' then t' - t else (γ.len - t) + t') + dist (γ.toFun t) (γ.toFun t')
    rw [GP.len_eq, hlen1]
    rcases htorder with h | h
    · rw [if_pos h.le, if_neg (not_le.mpr h)]; ring
    · rw [if_pos h.le, if_neg (not_le.mpr h)]; ring
  · show (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
        + (GP.G (γ.toFun t') (γ.toFun t)).len
        = (if t ≤ t' then t' - t else (γ.len - t) + t') + dist (γ.toFun t) (γ.toFun t')
    rw [GP.len_eq, hlen2, dist_comm (γ.toFun t') (γ.toFun t)]
