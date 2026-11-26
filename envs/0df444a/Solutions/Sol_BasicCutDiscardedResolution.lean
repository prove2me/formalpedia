-- Prove2me | solution 1 for BasicCutDiscardedResolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:50.078797+00:00
-- url     : https://prove2.me/submissions/2281bde3-4c1d-46a5-8ac8-17ca5c760648

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_RestrictPiecewiseGeodesic


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s) (p q : ℕ) (hp : p ≤ k) (hq : q ≤ k)
    (hne : s p ≠ s q)
    (ht0 : 0 ≤ s p) (htlen : s p ≤ γ.len) (ht'0 : 0 ≤ s q) (ht'len : s q ≤ γ.len) :
    IsPiecewiseGeodesicWith (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).2
      (((Finset.Icc 1 k).filter (fun j =>
          if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card + 1) := by
-- BODY
  obtain ⟨hmono, hs0, hsk, -⟩ := id hres
  have hrestrictEnd : ∀ (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len),
      (curveRestrict γ a b ha hab hb).toFun (curveRestrict γ a b ha hab hb).len = γ.toFun b := by
    intro a b ha hab hb
    show γ.toFun (a + min (b - a) (max 0 (b - a))) = γ.toFun b
    rw [max_eq_right (by linarith), min_self]
    congr 1
    ring
  rcases lt_trichotomy p q with hpq_lt | hpq_eq | hqp_lt
  · -- Case p < q: `g`'s arc leg is the ordinary restriction `γ|_{[s p, s q]}`.
    have hle_pq : s p ≤ s q :=
      hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hp⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq_lt.le
    have hlt : s p < s q := lt_of_le_of_ne hle_pq hne
    have harc : curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len
        = curveRestrict γ (s p) (s q) ht0 hlt.le ht'len := dif_pos hlt.le
    have hR1 := RestrictPiecewiseGeodesic γ k s hres p q hpq_lt.le hq ht0 hlt.le ht'len
    rw [← harc] at hR1
    obtain ⟨r, hr⟩ := GeodesicIsPiecewiseGeodesic GP (γ.toFun (s q)) (γ.toFun (s p))
    have hend : (curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).toFun
        (curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).len
        = (GP.G (γ.toFun (s q)) (γ.toFun (s p))).toFun 0 := by
      rw [harc, hrestrictEnd (s p) (s q) ht0 hlt.le ht'len, GP.start_eq]
    have hconcat := ConcatGeodesicResolution
      (curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len)
      (GP.G (γ.toFun (s q)) (γ.toFun (s p))) hend (q - p) 1
      (fun j => s (p + j) - s p) r hR1 hr
    have hcard : ((Finset.Icc 1 k).filter (fun j =>
        if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card = q - p := by
      have heq : (Finset.Icc 1 k).filter (fun j =>
          if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) = Finset.Ioc p q := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, if_pos hpq_lt]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, h1, h2⟩
      rw [heq, Nat.card_Ioc]
    rw [hcard]
    exact ⟨_, hconcat⟩
  · exact absurd (congrArg s hpq_eq) hne
  · -- Case q < p: `g`'s arc leg wraps, gluing the tail `γ|_{[s p, γ.len]}` to the head `γ|_{[0, s q]}`.
    have hle_qp : s q ≤ s p :=
      hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) (Set.mem_Icc.mpr ⟨Nat.zero_le _, hp⟩) hqp_lt.le
    have hlt' : s q < s p := lt_of_le_of_ne hle_qp (Ne.symm hne)
    have hnle : ¬ (s p ≤ s q) := not_le.mpr hlt'
    have hEndTailHead : (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len)).toFun
        (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len)).len
        = (curveRestrict γ 0 (s q) (le_refl 0) ht'0 ht'len).toFun 0 := by
      rw [hrestrictEnd (s p) γ.len ht0 htlen (le_refl γ.len)]
      show γ.toFun γ.len = γ.toFun (0 + min (s q - 0) (max 0 0))
      have e3 : max (0:ℝ) (0:ℝ) = 0 := max_self 0
      have e4 : min (s q - 0) (0:ℝ) = 0 := by rw [sub_zero]; exact min_eq_right ht'0
      rw [e3, e4, add_zero]
      exact hclosed
    have harc : curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len
        = curveConcat (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len))
            (curveRestrict γ 0 (s q) (le_refl 0) ht'0 ht'len) hEndTailHead := by
      have h1 : curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len
          = curveWrapRestrict γ (s p) (s q) hclosed ht0 htlen ht'0 hlt' := dif_neg hnle
      rw [h1]; rfl
    have hab_pk : s p ≤ s k := by rw [hsk]; exact htlen
    have hb_pk : s k ≤ γ.len := le_of_eq hsk
    have hRtailEq : curveRestrict γ (s p) (s k) ht0 hab_pk hb_pk
        = curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len) := by
      congr 1
    have hRtail0 : IsGeodesicResolution (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len))
        (k - p) (fun j => s (p + j) - s p) := by
      have h := RestrictPiecewiseGeodesic γ k s hres p k hp (le_refl k) ht0 hab_pk hb_pk
      rw [hRtailEq] at h
      exact h
    have ha_0q : 0 ≤ s 0 := le_of_eq hs0.symm
    have hab_0q : s 0 ≤ s q := by rw [hs0]; exact ht'0
    have hRheadEq : curveRestrict γ (s 0) (s q) ha_0q hab_0q ht'len
        = curveRestrict γ 0 (s q) (le_refl 0) ht'0 ht'len := by
      congr 1
    have hRhead0 : IsGeodesicResolution (curveRestrict γ 0 (s q) (le_refl 0) ht'0 ht'len)
        (q - 0) (fun j => s (0 + j) - s 0) := by
      have h := RestrictPiecewiseGeodesic γ k s hres 0 q (Nat.zero_le q) hq ha_0q hab_0q ht'len
      rw [hRheadEq] at h
      exact h
    have hconcatWrap := ConcatGeodesicResolution
      (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len))
      (curveRestrict γ 0 (s q) (le_refl 0) ht'0 ht'len) hEndTailHead
      (k - p) (q - 0) (fun j => s (p + j) - s p) (fun j => s (0 + j) - s 0) hRtail0 hRhead0
    rw [← harc] at hconcatWrap
    obtain ⟨r, hr⟩ := GeodesicIsPiecewiseGeodesic GP (γ.toFun (s q)) (γ.toFun (s p))
    have hend2 : (curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).toFun
        (curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).len
        = (GP.G (γ.toFun (s q)) (γ.toFun (s p))).toFun 0 := by
      rw [harc, (CurveConcatEndpoints
          (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len))
          (curveRestrict γ 0 (s q) (le_refl 0) ht'0 ht'len) hEndTailHead).2,
        hrestrictEnd 0 (s q) (le_refl 0) ht'0 ht'len, GP.start_eq]
    have hconcatFull := ConcatGeodesicResolution
      (curveArc γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len)
      (GP.G (γ.toFun (s q)) (γ.toFun (s p))) hend2
      ((k - p) + (q - 0)) 1
      (fun i => if i ≤ k - p then (fun j => s (p + j) - s p) i
        else (curveRestrict γ (s p) γ.len ht0 htlen (le_refl γ.len)).len
          + (fun j => s (0 + j) - s 0) (i - (k - p)))
      r hconcatWrap hr
    have hcard2 : ((Finset.Icc 1 k).filter (fun j =>
        if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card
        = q + (k - p) := by
      have heq : (Finset.Icc 1 k).filter (fun j =>
          if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)
          = Finset.Icc 1 q ∪ Finset.Ioc p k := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc,
          if_neg (by omega : ¬ p < q)]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases h3 with h3 | h3
          · exact Or.inl ⟨h1, h3⟩
          · exact Or.inr ⟨h3, h2⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨⟨h1, by omega⟩, Or.inl h2⟩
          · exact ⟨⟨by omega, h2⟩, Or.inr h1⟩
      have hdisj : Disjoint (Finset.Icc 1 q) (Finset.Ioc p k) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_Icc] at hj1
        simp only [Finset.mem_Ioc] at hj2
        omega
      rw [heq, Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Ioc]
      omega
    rw [hcard2]
    have hfinal : (k - p) + (q - 0) + 1 = q + (k - p) + 1 := by omega
    rw [hfinal] at hconcatFull
    exact ⟨_, hconcatFull⟩
