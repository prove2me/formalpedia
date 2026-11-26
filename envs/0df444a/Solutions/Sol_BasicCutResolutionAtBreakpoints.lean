-- Prove2me | solution 1 for BasicCutResolutionAtBreakpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:11.645695+00:00
-- url     : https://prove2.me/submissions/50c0234f-ace9-4b03-9c36-149ed4a6ac31

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_SubResolutionShortEdgeCount
import Definitions.Def_Tablet_ConcatResolutionShortEdgeCount
import Definitions.Def_Tablet_BasicCutResolutionAtBreakpoints
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_ConcatResolutionShortEdgeCount
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_SubResolutionShortEdgeCount


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s) (p q : ℕ) (hp : p ≤ k) (hq : q ≤ k)
    (hne : s p ≠ s q) (δ : ℝ)
    (ht0 : 0 ≤ s p) (htlen : s p ≤ γ.len) (ht'0 : 0 ≤ s q) (ht'len : s q ≤ γ.len) :
    smallPieceCount (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1 δ
      + ((Finset.Icc 1 k).filter (fun j =>
          (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)).card
      ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card + 1 := by
-- BODY
  obtain ⟨hmono, hs0, hsk, -⟩ := id hres
  -- The restriction `γ|_{[a,b]}` ends at `γ(b)` (used for every endpoint match below).
  have hrestrictEnd : ∀ (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len),
      (curveRestrict γ a b ha hab hb).toFun (curveRestrict γ a b ha hab hb).len = γ.toFun b := by
    intro a b ha hab hb
    show γ.toFun (a + min (b - a) (max 0 (b - a))) = γ.toFun b
    rw [max_eq_right (by linarith), min_self]
    congr 1
    ring
  -- The single closing geodesic edge, with its one-edge resolution `r`.
  obtain ⟨r, hr⟩ := GeodesicIsPiecewiseGeodesic GP (γ.toFun (s p)) (γ.toFun (s q))
  obtain ⟨-, hr0, -, -⟩ := id hr
  have hrcount : ((Finset.Icc 1 1).filter (fun j => r j - r (j - 1) < δ)).card ≤ 1 := by
    have h := Finset.card_filter_le (Finset.Icc 1 1) (fun j => r j - r (j - 1) < δ)
    rw [Nat.card_Icc] at h
    omega
  rcases lt_trichotomy p q with hpq | hpq_eq | hqp
  · -- Case `p < q`: the kept arc wraps, gluing the tail `γ|_{[s q, len γ]}` to the head
    -- `γ|_{[0, s p]}`, and the excised index block is `Ioc p q`.
    have hle_pq : s p ≤ s q :=
      hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hp⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq.le
    have hlt : s p < s q := lt_of_le_of_ne hle_pq hne
    have hnle : ¬ (s q ≤ s p) := not_le.mpr hlt
    have hEndTailHead : (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len)).toFun
        (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len)).len
        = (curveRestrict γ 0 (s p) (le_refl 0) ht0 htlen).toFun 0 := by
      rw [hrestrictEnd (s q) γ.len ht'0 ht'len (le_refl γ.len)]
      show γ.toFun γ.len = γ.toFun (0 + min (s p - 0) (max 0 0))
      have e3 : max (0:ℝ) (0:ℝ) = 0 := max_self 0
      have e4 : min (s p - 0) (0:ℝ) = 0 := by rw [sub_zero]; exact min_eq_right ht0
      rw [e3, e4, add_zero]
      exact hclosed
    have harc : curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen
        = curveConcat (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len))
            (curveRestrict γ 0 (s p) (le_refl 0) ht0 htlen) hEndTailHead := by
      have h1 : curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen
          = curveWrapRestrict γ (s q) (s p) hclosed ht'0 ht'len ht0 hlt := dif_neg hnle
      rw [h1]; rfl
    -- The two legs of the wrap arc, each resolved by a shifted sub-resolution of `s`.
    have hab_qk : s q ≤ s k := by rw [hsk]; exact ht'len
    have hb_qk : s k ≤ γ.len := le_of_eq hsk
    have hRtailEq : curveRestrict γ (s q) (s k) ht'0 hab_qk hb_qk
        = curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len) := by congr 1
    have hRtail : IsGeodesicResolution (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len))
        (k - q) (fun j => s (q + j) - s q) := by
      have h := RestrictPiecewiseGeodesic γ k s hres q k hq (le_refl k) ht'0 hab_qk hb_qk
      rw [hRtailEq] at h
      exact h
    have ha_0p : 0 ≤ s 0 := le_of_eq hs0.symm
    have hab_0p : s 0 ≤ s p := by rw [hs0]; exact ht0
    have hRheadEq : curveRestrict γ (s 0) (s p) ha_0p hab_0p htlen
        = curveRestrict γ 0 (s p) (le_refl 0) ht0 htlen := by congr 1
    have hRhead : IsGeodesicResolution (curveRestrict γ 0 (s p) (le_refl 0) ht0 htlen)
        (p - 0) (fun j => s (0 + j) - s 0) := by
      have h := RestrictPiecewiseGeodesic γ k s hres 0 p (Nat.zero_le p) hp ha_0p hab_0p htlen
      rw [hRheadEq] at h
      exact h
    obtain ⟨W, hWdef, hWres⟩ : ∃ W : ℕ → ℝ,
        (∀ i, W i = if i ≤ k - q then (fun j => s (q + j) - s q) i
          else (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len)).len
            + (fun j => s (0 + j) - s 0) (i - (k - q))) ∧
        IsGeodesicResolution (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen)
          ((k - q) + (p - 0)) W := by
      refine ⟨fun i => if i ≤ k - q then (fun j => s (q + j) - s q) i
          else (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len)).len
            + (fun j => s (0 + j) - s 0) (i - (k - q)),
        fun i => rfl, ?_⟩
      rw [harc]
      exact ConcatGeodesicResolution _ _ hEndTailHead (k - q) (p - 0)
        (fun j => s (q + j) - s q) (fun j => s (0 + j) - s 0) hRtail hRhead
    have hend : (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).toFun
        (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len
        = (GP.G (γ.toFun (s p)) (γ.toFun (s q))).toFun 0 := by
      rw [harc, (CurveConcatEndpoints _ _ hEndTailHead).2,
        hrestrictEnd 0 (s p) (le_refl 0) ht0 htlen, GP.start_eq]
    obtain ⟨R, hRdef, hglue⟩ : ∃ R : ℕ → ℝ,
        (∀ i, R i = if i ≤ (k - q) + (p - 0) then W i
          else (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len
            + r (i - ((k - q) + (p - 0)))) ∧
        IsGeodesicResolution (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1
          ((k - q) + (p - 0) + 1) R := by
      refine ⟨fun i => if i ≤ (k - q) + (p - 0) then W i
          else (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len
            + r (i - ((k - q) + (p - 0))),
        fun i => rfl, ?_⟩
      exact ConcatGeodesicResolution (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen)
        (GP.G (γ.toFun (s p)) (γ.toFun (s q))) hend ((k - q) + (p - 0)) 1 W r hWres hr
    have hcut : smallPieceCount (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1 δ
        ≤ ((Finset.Icc 1 ((k - q) + (p - 0) + 1)).filter
            (fun i => R i - R (i - 1) < δ)).card :=
      Nat.sInf_le ⟨(k - q) + (p - 0) + 1, R, hglue, rfl⟩
    have hLW : W ((k - q) + (p - 0))
        = (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len := by
      obtain ⟨-, -, h3, -⟩ := id hWres
      exact h3
    have hcountOuter : ((Finset.Icc 1 ((k - q) + (p - 0) + 1)).filter
          (fun i => R i - R (i - 1) < δ)).card
        = ((Finset.Icc 1 ((k - q) + (p - 0))).filter (fun j => W j - W (j - 1) < δ)).card
          + ((Finset.Icc 1 1).filter (fun j => r j - r (j - 1) < δ)).card :=
      ConcatResolutionShortEdgeCount ((k - q) + (p - 0)) 1 W r R
        (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len δ hLW hr0 hRdef
    have hL1 : (fun j => s (q + j) - s q) (k - q)
        = (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len)).len := by
      obtain ⟨-, -, h3, -⟩ := id hRtail
      exact h3
    have hz2 : (fun j => s (0 + j) - s 0) 0 = 0 := by
      obtain ⟨-, h2, -, -⟩ := id hRhead
      exact h2
    have hcountInner : ((Finset.Icc 1 ((k - q) + (p - 0))).filter
          (fun j => W j - W (j - 1) < δ)).card
        = ((Finset.Icc 1 (k - q)).filter
            (fun j => (s (q + j) - s q) - (s (q + (j - 1)) - s q) < δ)).card
          + ((Finset.Icc 1 (p - 0)).filter
            (fun j => (s (0 + j) - s 0) - (s (0 + (j - 1)) - s 0) < δ)).card :=
      ConcatResolutionShortEdgeCount (k - q) (p - 0) (fun j => s (q + j) - s q)
        (fun j => s (0 + j) - s 0) W
        (curveRestrict γ (s q) γ.len ht'0 ht'len (le_refl γ.len)).len δ hL1 hz2 hWdef
    have hTail := SubResolutionShortEdgeCount q k s δ
    have hHead := SubResolutionShortEdgeCount 0 p s δ
    -- Index accounting: `Icc 1 k` splits as `Ioc 0 p ⊔ Ioc p q ⊔ Ioc q k`, and `inArc = Ioc p q`.
    have hinArc : (Finset.Icc 1 k).filter (fun j =>
          (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)
        = (Finset.Ioc p q).filter (fun j => s j - s (j - 1) < δ) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, if_pos hpq]
      constructor
      · rintro ⟨-, ⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by omega, by omega⟩, ⟨h1, h2⟩, h3⟩
    have hsplit : ((Finset.Ioc 0 p).filter (fun j => s j - s (j - 1) < δ)).card
        + ((Finset.Ioc p q).filter (fun j => s j - s (j - 1) < δ)).card
        + ((Finset.Ioc q k).filter (fun j => s j - s (j - 1) < δ)).card
        = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card := by
      have hsets : Finset.Icc 1 k
          = (Finset.Ioc 0 p) ∪ (Finset.Ioc p q) ∪ (Finset.Ioc q k) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
        omega
      have hd1 : Disjoint ((Finset.Ioc 0 p).filter (fun j => s j - s (j - 1) < δ))
          ((Finset.Ioc p q).filter (fun j => s j - s (j - 1) < δ)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
        have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
        omega
      have hd2 : Disjoint (((Finset.Ioc 0 p).filter (fun j => s j - s (j - 1) < δ))
            ∪ ((Finset.Ioc p q).filter (fun j => s j - s (j - 1) < δ)))
          ((Finset.Ioc q k).filter (fun j => s j - s (j - 1) < δ)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
        rcases Finset.mem_union.mp ha with h | h
        · have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1; omega
        · have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1; omega
      rw [hsets, Finset.filter_union, Finset.filter_union,
        Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
    rw [hinArc]
    omega
  · exact absurd (congrArg s hpq_eq) hne
  · -- Case `q < p`: the kept arc is the ordinary restriction `γ|_{[s q, s p]}`, and the excised
    -- index block is `Ioc 0 q ∪ Ioc p k`.
    have hle_qp : s q ≤ s p :=
      hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hp⟩) hqp.le
    have hlt' : s q < s p := lt_of_le_of_ne hle_qp (Ne.symm hne)
    have harc : curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen
        = curveRestrict γ (s q) (s p) ht'0 hlt'.le htlen := dif_pos hlt'.le
    have hR1 : IsGeodesicResolution (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen)
        (p - q) (fun j => s (q + j) - s q) := by
      rw [harc]
      exact RestrictPiecewiseGeodesic γ k s hres q p hqp.le hp ht'0 hlt'.le htlen
    have hend : (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).toFun
        (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len
        = (GP.G (γ.toFun (s p)) (γ.toFun (s q))).toFun 0 := by
      rw [harc, hrestrictEnd (s q) (s p) ht'0 hlt'.le htlen, GP.start_eq]
    obtain ⟨R, hRdef, hglue⟩ : ∃ R : ℕ → ℝ,
        (∀ i, R i = if i ≤ p - q then (fun j => s (q + j) - s q) i
          else (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len + r (i - (p - q))) ∧
        IsGeodesicResolution (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1
          ((p - q) + 1) R := by
      refine ⟨fun i => if i ≤ p - q then (fun j => s (q + j) - s q) i
          else (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len + r (i - (p - q)),
        fun i => rfl, ?_⟩
      exact ConcatGeodesicResolution (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen)
        (GP.G (γ.toFun (s p)) (γ.toFun (s q))) hend (p - q) 1
        (fun j => s (q + j) - s q) r hR1 hr
    have hcut : smallPieceCount (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1 δ
        ≤ ((Finset.Icc 1 ((p - q) + 1)).filter (fun i => R i - R (i - 1) < δ)).card :=
      Nat.sInf_le ⟨(p - q) + 1, R, hglue, rfl⟩
    have hLeq : (fun j => s (q + j) - s q) (p - q)
        = (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len := by
      obtain ⟨-, -, h3, -⟩ := id hR1
      exact h3
    have hcount1 : ((Finset.Icc 1 ((p - q) + 1)).filter (fun i => R i - R (i - 1) < δ)).card
        = ((Finset.Icc 1 (p - q)).filter
            (fun j => (s (q + j) - s q) - (s (q + (j - 1)) - s q) < δ)).card
          + ((Finset.Icc 1 1).filter (fun j => r j - r (j - 1) < δ)).card :=
      ConcatResolutionShortEdgeCount (p - q) 1 (fun j => s (q + j) - s q) r R
        (curveArc γ hclosed (s q) (s p) ht'0 ht'len ht0 htlen).len δ hLeq hr0 hRdef
    have hcount2 := SubResolutionShortEdgeCount q p s δ
    have hinArc : (Finset.Icc 1 k).filter (fun j =>
          (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)
        = ((Finset.Ioc 0 q) ∪ (Finset.Ioc p k)).filter (fun j => s j - s (j - 1) < δ) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc,
        if_neg (show ¬ p < q by omega)]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨by omega, h4⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, by omega⟩, by omega, h2⟩
    have hsplit : ((Finset.Ioc 0 q).filter (fun j => s j - s (j - 1) < δ)).card
        + ((Finset.Ioc q p).filter (fun j => s j - s (j - 1) < δ)).card
        + ((Finset.Ioc p k).filter (fun j => s j - s (j - 1) < δ)).card
        = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card := by
      have hsets : Finset.Icc 1 k
          = (Finset.Ioc 0 q) ∪ (Finset.Ioc q p) ∪ (Finset.Ioc p k) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
        omega
      have hd1 : Disjoint ((Finset.Ioc 0 q).filter (fun j => s j - s (j - 1) < δ))
          ((Finset.Ioc q p).filter (fun j => s j - s (j - 1) < δ)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
        have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
        omega
      have hd2 : Disjoint (((Finset.Ioc 0 q).filter (fun j => s j - s (j - 1) < δ))
            ∪ ((Finset.Ioc q p).filter (fun j => s j - s (j - 1) < δ)))
          ((Finset.Ioc p k).filter (fun j => s j - s (j - 1) < δ)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
        rcases Finset.mem_union.mp ha with h | h
        · have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1; omega
        · have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1; omega
      rw [hsets, Finset.filter_union, Finset.filter_union,
        Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
    have hdisjArc : Disjoint ((Finset.Ioc 0 q).filter (fun j => s j - s (j - 1) < δ))
        ((Finset.Ioc p k).filter (fun j => s j - s (j - 1) < δ)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
      have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
      omega
    rw [hinArc, Finset.filter_union, Finset.card_union_of_disjoint hdisjArc]
    omega
