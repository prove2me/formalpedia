-- Prove2me | solution 1 for BasicCutDiscardedEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:58.0385+00:00
-- url     : https://prove2.me/submissions/4102bf82-1ebb-44b0-8c72-cf4df8459b19

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedEval
import Theorems.Thm_CurveConcatEndpoints


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len)
    (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) :
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len
        = (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
          + (GP.G (γ.toFun t') (γ.toFun t)).len ∧
      (∀ v : ℝ, v ≤ (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len →
        (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.toFun v
          = (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).toFun v) ∧
      IsGeodesicOn (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2
        (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
        (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len := by
-- BODY
  -- A restriction ends where it should.
  have hrestrictEnd : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
      (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
    intro p q hp hpq hq
    show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
    rw [max_eq_right (by linarith), min_self]
    congr 1
    ring
  -- Hence the circular arc `γ|_{[a,b]}` ends at `γ(b)`, in either order of `a,b`.
  have harcEnd : ∀ (a b : ℝ) (ha0 : 0 ≤ a) (hal : a ≤ γ.len) (hb0 : 0 ≤ b) (hbl : b ≤ γ.len),
      (curveArc γ hclosed a b ha0 hal hb0 hbl).toFun (curveArc γ hclosed a b ha0 hal hb0 hbl).len
        = γ.toFun b := by
    intro a b ha0 hal hb0 hbl
    unfold curveArc
    split_ifs with h
    · exact hrestrictEnd a b ha0 h hbl
    · unfold curveWrapRestrict
      rw [(CurveConcatEndpoints _ _ _).2]
      exact hrestrictEnd 0 b (le_refl 0) hb0 (by linarith)
  -- The generic statement about a concatenation whose second factor is a geodesic.
  have hgen : ∀ (A C : Curve E) (hm : A.toFun A.len = C.toFun 0), IsGeodesicOn C 0 C.len →
      (curveConcat A C hm).len = A.len + C.len ∧
        (∀ v : ℝ, v ≤ A.len → (curveConcat A C hm).toFun v = A.toFun v) ∧
        IsGeodesicOn (curveConcat A C hm) A.len (curveConcat A C hm).len := by
    intro A C hm hgeo
    have hlen : (curveConcat A C hm).len = A.len + C.len := rfl
    refine ⟨hlen, ?_, ?_⟩
    · intro v hv
      show (if v ≤ A.len then A.toFun v else C.toFun (v - A.len)) = A.toFun v
      rw [if_pos hv]
    · -- Beyond `A.len` the concatenation is `C` translated by `A.len`.
      have hbeyond : ∀ x : ℝ, A.len ≤ x → (curveConcat A C hm).toFun x = C.toFun (x - A.len) := by
        intro x hx
        show (if x ≤ A.len then A.toFun x else C.toFun (x - A.len)) = C.toFun (x - A.len)
        rcases eq_or_lt_of_le hx with h | h
        · rw [if_pos (by linarith)]
          rw [← h, sub_self, hm]
        · rw [if_neg (by linarith)]
      intro x hx y hy
      rw [hlen] at hx hy
      obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hy0, hy1⟩ := hy
      rw [hbeyond x hx0, hbeyond y hy0]
      rw [hgeo (x - A.len) ⟨by linarith, by linarith⟩ (y - A.len) ⟨by linarith, by linarith⟩]
      congr 1
      ring
  exact hgen (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) (GP.G (γ.toFun t') (γ.toFun t))
    (by rw [harcEnd, GP.start_eq]) (GP.isGeodesic _ _)
