-- Prove2me | solution 1 for CutTypeI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:47.234751+00:00
-- url     : https://prove2.me/submissions/29a3061c-c17b-4f94-ba3f-88fe0cbc2404

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_TypeICutPointExists
import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_BasicCutClosed
import Definitions.Def_Tablet_BasicCutCurrent
import Definitions.Def_Tablet_BasicCutLength
import Definitions.Def_Tablet_BasicCutResolutionGeneral
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_ArcShortWindowEdgeCount
import Definitions.Def_Tablet_ArcDeltaEpsNCount
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_FullBallLem
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_RestrictLSI
import Definitions.Def_Tablet_RestrictFullIsSelf
import Definitions.Def_Tablet_RestrictMeasureFormula
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Definitions.Def_Tablet_MorreySubadditive
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedEval
import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_CutTypeI
import Theorems.Thm_ArcDeltaEpsNCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ArcShortWindowEdgeCount
import Theorems.Thm_BasicCutClosed
import Theorems.Thm_BasicCutCurrent
import Theorems.Thm_BasicCutDiscardedEval
import Theorems.Thm_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_BasicCutLength
import Theorems.Thm_BasicCutResolutionGeneral
import Theorems.Thm_C1SmallBall
import Theorems.Thm_FullBallLem
import Theorems.Thm_GeodesicMorreyLeTwo
import Theorems.Thm_MorreyResolutionAdditive
import Theorems.Thm_MorreySubadditive
import Theorems.Thm_RestrictFullIsSelf
import Theorems.Thm_RestrictLSI
import Theorems.Thm_RestrictMeasureFormula
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_TypeICutPointExists


set_option autoImplicit false
open Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (δ ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (hden : IsDeltaEpsN γ δ ε n) (hnlsi : ¬ IsLSI γ δ ε) :
    ∃ (γ' g : Curve E) (β : ℝ),
      δ ≤ β ∧ β ≤ γ.len / 2 ∧
      (∀ ω : Form1 E, curveCurrent γ ω = curveCurrent γ' ω + curveCurrent g ω) ∧
      IsClosedCurve γ' ∧ IsPiecewiseGeodesic γ' ∧
      IsClosedCurve g ∧ IsPiecewiseGeodesic g ∧
      morreyNorm (curveMeasure g) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10) ∧
      γ'.len ≤ γ.len - (1 - ε) * β ∧
      γ'.len + g.len ≤ γ.len + 2 * ε * β ∧
      smallPieceCount γ' δ ≤ smallPieceCount γ δ + 3 := by
-- BODY
  classical
  -- ## Setup: the cut point, from `TypeICutPointExists`.
  obtain ⟨t, t', ht0, htl, ht'0, ht'l, β, hβA, hβd, hδβ, hβhalf, hdist, -, hncA, hlsiA⟩ :=
    TypeICutPointExists γ hclosed hpg δ ε hε0 hε1 hδ hnlsi
  -- ## Step 0: `t ≠ t'`.
  have hne : t ≠ t' := by
    intro h
    have hd : dGamma γ t t' = 0 := by
      unfold dGamma
      rw [if_pos hclosed, h, sub_self, abs_zero, sub_zero, min_eq_left γ.len_nonneg]
    rw [hd] at hβd
    linarith
  -- The excised arc, and the arc-length identity `A.len = β`.
  have harc_len : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len
      = if t ≤ t' then t' - t else (γ.len - t) + t' := by
    unfold curveArc
    split_ifs with h
    · rfl
    · show (γ.len - t) + (t' - 0) = (γ.len - t) + t'
      ring
  have hifβ : (if t ≤ t' then t' - t else (γ.len - t) + t') = β := by rw [← harc_len, hβA]
  -- ## The Morrey bound, proved separately below.
  have hMorrey : morreyNorm (curveMeasure (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2)
      ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10) := by
    obtain ⟨k, s, hres, hlin, hwrapc⟩ := hden
    have hwrap := hwrapc hclosed
    obtain ⟨kA, sA, hkA, hresA, hord, hwr⟩ :=
      ArcGeodesicResolution γ hclosed k s hres t t' ht0 htl ht'0 ht'l
    rcases le_or_gt (sA (kA - 1) - sA 1) δ with hshort | hlong
    · -- ### Branch 1: the arc's interior window is short, so the arc has at most `n+3` edges.
      have hkn : kA ≤ n + 3 :=
        ArcShortWindowEdgeCount γ hclosed δ ε n k s hres hδ hε0 hε1 hlin hwrap
          t t' ht0 htl ht'0 ht'l kA sA hkA hresA hord hwr hshort
      have hpw := BasicCutDiscardedResolutionGeneral GP γ hclosed t t' ht0 htl ht'0 ht'l hne kA sA
        hresA
      refine le_trans (C1SmallBall _ (kA + 1) hpw) ?_
      have hcast : (2 : ℝ≥0∞) * ((kA + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * ((kA : ℝ) + 1)) := by
        rw [show (2 : ℝ) * ((kA : ℝ) + 1) = ((2 * (kA + 1) : ℕ) : ℝ) by push_cast; ring,
          ENNReal.ofReal_natCast]
        push_cast
        ring
      rw [hcast]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (kA : ℝ) ≤ (n : ℝ) + 3 := by exact_mod_cast hkn
      have h2 : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε0
      linarith
    · -- ### Branch 2: the arc's interior window is longer than `δ`.
      obtain ⟨hmonoA, hsA0, hsAk, hedgeA⟩ := id hresA
      have hk3 : 3 ≤ kA := by
        by_contra hc
        push_neg at hc
        have hle : sA (kA - 1) ≤ sA 1 :=
          hmonoA (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
            (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) (by omega)
        linarith
      have hu0 : (0 : ℝ) ≤ sA 1 := by
        have h := hmonoA (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
          (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩) (by omega : (0 : ℕ) ≤ 1)
        rwa [hsA0] at h
      have huu' : sA 1 ≤ sA (kA - 1) := by linarith
      have hu'l : sA (kA - 1) ≤ (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by
        have h := hmonoA (Set.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
          (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_refl _⟩) (by omega : kA - 1 ≤ kA)
        rwa [hsAk] at h
      -- `δ < β`, so the three conjuncts of `TypeICutPointExists` guarded by it fire.
      have hδβ' : δ < β := by rw [hβA]; linarith
      have hncA' := hncA hδβ'
      have hlsiA' := hlsiA hδβ'
      -- The interior window `B` is not closed.
      have hBnc : ¬ IsClosedCurve (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l) := by
        intro hcl
        have e0 : (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l).toFun 0 = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA 1) := by
          show (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA 1 + min (sA (kA - 1) - sA 1) (max 0 0)) = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA 1)
          rw [max_self, min_eq_right (by linarith), add_zero]
        have e1 : (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l).toFun (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l).len = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA (kA - 1)) := by
          show (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA 1 + min (sA (kA - 1) - sA 1) (max 0 (sA (kA - 1) - sA 1)))
            = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA (kA - 1))
          rw [max_eq_right (by linarith), min_self]
          congr 1
          ring
        have hdG : dGamma (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) = sA (kA - 1) - sA 1 := by
          unfold dGamma
          rw [if_neg hncA', abs_of_nonpos (by linarith : sA 1 - sA (kA - 1) ≤ 0)]
          ring
        have hlow := hlsiA'.2 (sA 1) (Set.mem_Icc.mpr ⟨hu0, by linarith⟩)
          (sA (kA - 1)) (Set.mem_Icc.mpr ⟨by linarith, hu'l⟩) (by rw [hdG]; linarith)
        rw [hdG] at hlow
        have heq : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA (kA - 1)) = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun (sA 1) := e1.symm.trans (hcl.trans e0)
        rw [heq, dist_self] at hlow
        nlinarith
      -- `B` is piecewise geodesic, `(δ,ε)`-l.s.i., and a `(δ,ε,n)`-curve.
      have hBpg : IsPiecewiseGeodesic (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l) :=
        ⟨kA - 1 - 1, fun j => sA (1 + j) - sA 1,
          RestrictPiecewiseGeodesic (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) kA sA hresA 1 (kA - 1) (by omega) (by omega)
            hu0 huu' hu'l⟩
      have hfull := RestrictFullIsSelf (curveArc γ hclosed t t' ht0 htl ht'0 ht'l)
      have hlsiFull : IsLSI (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) 0 (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len (le_refl 0) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len_nonneg
          (le_refl (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)) δ ε := by rw [hfull]; exact hlsiA'
      have hncFull : ¬ IsClosedCurve (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) 0 (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len (le_refl 0) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len_nonneg
          (le_refl (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len)) := by rw [hfull]; exact hncA'
      have hBlsi : IsLSI (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l) δ ε :=
        RestrictLSI (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) δ ε 0 (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len (sA 1) (sA (kA - 1)) (le_refl 0) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len_nonneg
          (le_refl (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len) hu0 huu' hu'l hu0 hu'l hlsiFull hncFull hBnc hBpg
      have hBden : IsDeltaEpsN (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l) δ ε n :=
        ArcDeltaEpsNCount γ hclosed δ ε n k s hres hlin hwrap t t' ht0 htl ht'0 ht'l kA sA hkA
          hresA hord hwr hu0 huu' hu'l hBnc
      have hBmorrey : morreyNorm (curveMeasure (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 4) :=
        FullBallLem (curveRestrict (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l) δ ε n hδ hε0 hε1 hBden hBlsi
      -- ### Splicing `B` back into `g`.
      obtain ⟨hglen, hgagree, hggeo⟩ := BasicCutDiscardedEval GP γ hclosed t t' ht0 htl ht'0 ht'l
      have hClen : (0 : ℝ) ≤ (GP.G (γ.toFun t') (γ.toFun t)).len := (GP.G _ _).len_nonneg
      have hAg : (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len ≤ (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.len := by rw [hglen]; linarith
      have htrans : ∀ a b : ℝ, b ≤ (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len → IsGeodesicOn (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) a b → IsGeodesicOn (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 a b := by
        intro a b hb hgeo x hx y hy
        rw [hgagree x (le_trans hx.2 hb), hgagree y (le_trans hy.2 hb)]
        exact hgeo x hx y hy
      have hgeo0 : IsGeodesicOn (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 0 (sA 1) := by
        have h := hedgeA 0 (by omega)
        simp only [zero_add] at h
        rw [hsA0] at h
        exact htrans 0 (sA 1) (by linarith) h
      have hgeo2 : IsGeodesicOn (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 (sA (kA - 1)) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by
        have h := hedgeA (kA - 1) (by omega)
        rw [show kA - 1 + 1 = kA by omega, hsAk] at h
        exact htrans _ _ (le_refl _) h
      have hM0 : morreyNorm (MeasureTheory.Measure.map (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.toFun
          (MeasureTheory.volume.restrict (Set.Icc 0 (sA 1)))) ≤ 2 :=
        GeodesicMorreyLeTwo (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 0 (sA 1) hu0 (by linarith) hgeo0
      have hM2 : morreyNorm (MeasureTheory.Measure.map (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.toFun
          (MeasureTheory.volume.restrict (Set.Icc (sA (kA - 1)) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len))) ≤ 2 :=
        GeodesicMorreyLeTwo (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 (sA (kA - 1)) (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len hu'l hAg hgeo2
      have hM3 : morreyNorm (MeasureTheory.Measure.map (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.toFun
          (MeasureTheory.volume.restrict (Set.Icc (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.len))) ≤ 2 :=
        GeodesicMorreyLeTwo (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.len hAg (le_refl _) hggeo
      have hM1 : morreyNorm (MeasureTheory.Measure.map (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.toFun
          (MeasureTheory.volume.restrict (Set.Icc (sA 1) (sA (kA - 1)))))
          ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 4) := by
        have hmapeq : MeasureTheory.Measure.map (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.toFun
            (MeasureTheory.volume.restrict (Set.Icc (sA 1) (sA (kA - 1))))
            = MeasureTheory.Measure.map (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).toFun
              (MeasureTheory.volume.restrict (Set.Icc (sA 1) (sA (kA - 1)))) := by
          apply MeasureTheory.Measure.map_congr
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
          exact hgagree x (le_trans hx.2 hu'l)
        rw [hmapeq, ← RestrictMeasureFormula (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) (sA 1) (sA (kA - 1)) hu0 huu' hu'l]
        exact hBmorrey
      -- ### Assembly of the four blocks.
      set s' : ℕ → ℝ := fun i => if i = 0 then 0 else if i = 1 then sA 1
        else if i = 2 then sA (kA - 1) else if i = 3 then (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len else (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.len with hs'def
      have hv0 : s' 0 = 0 := by simp [hs'def]
      have hv1 : s' 1 = sA 1 := by simp [hs'def]
      have hv2 : s' 2 = sA (kA - 1) := by simp [hs'def]
      have hv3 : s' 3 = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len := by simp [hs'def]
      have hv4 : s' 4 = (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.len := by simp [hs'def]
      have hmono : MonotoneOn s' (Set.Icc 0 4) := by
        intro a ha b hb hab
        obtain ⟨-, ha4⟩ := Set.mem_Icc.mp ha
        obtain ⟨-, hb4⟩ := Set.mem_Icc.mp hb
        interval_cases a <;> interval_cases b <;>
          simp only [hv0, hv1, hv2, hv3, hv4] <;> linarith
      have hdec := MorreyResolutionAdditive (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2 4 s' hmono hv0 hv4
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hinv : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε0
      calc morreyNorm (curveMeasure (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2)
          ≤ ∑ i ∈ Finset.range 4, morreyNorm (MeasureTheory.Measure.map (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2.toFun
              (MeasureTheory.volume.restrict (Set.Icc (s' i) (s' (i + 1))))) := by
            rw [hdec]; exact MorreySubadditive _ _
        _ ≤ (2 : ℝ≥0∞) + ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 4) + 2 + 2 := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd,
              hv0, hv1, hv2, hv3, hv4]
            exact add_le_add (add_le_add (add_le_add hM0 hM1) hM2) hM3
        _ = ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10) := by
            have hX : (0 : ℝ) ≤ 4 * ε⁻¹ + 2 * (n : ℝ) + 4 := by linarith
            have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
            have e : (4 : ℝ) * ε⁻¹ + 2 * (n : ℝ) + 10
                = 2 + (4 * ε⁻¹ + 2 * (n : ℝ) + 4) + 2 + 2 := by ring
            rw [h2, e,
              ENNReal.ofReal_add (p := 2 + (4 * ε⁻¹ + 2 * (n : ℝ) + 4) + 2) (q := 2)
                (by linarith) (by norm_num),
              ENNReal.ofReal_add (p := 2 + (4 * ε⁻¹ + 2 * (n : ℝ) + 4)) (q := 2)
                (by linarith) (by norm_num),
              ENNReal.ofReal_add (p := 2) (q := 4 * ε⁻¹ + 2 * (n : ℝ) + 4)
                (by norm_num) hX]
  -- ## Assembly.
  refine ⟨(BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).1,
    (BasicCut GP γ hclosed t t' ht0 htl ht'0 ht'l).2, β, hδβ, hβhalf,
    fun ω => BasicCutCurrent GP γ hclosed t t' ht0 htl ht'0 ht'l hne ω, ?_, ?_, ?_, ?_,
    hMorrey, ?_, ?_,
    BasicCutResolutionGeneral GP γ hclosed hpg δ hδ t t' ht0 htl ht'0 ht'l hne⟩
  · exact (BasicCutClosed GP γ hclosed hpg t t' ht0 htl ht'0 ht'l hne).1
  · exact (BasicCutClosed GP γ hclosed hpg t t' ht0 htl ht'0 ht'l hne).2.1
  · exact (BasicCutClosed GP γ hclosed hpg t t' ht0 htl ht'0 ht'l hne).2.2.1
  · exact (BasicCutClosed GP γ hclosed hpg t t' ht0 htl ht'0 ht'l hne).2.2.2
  -- ## Step 4: the two length bounds.
  · obtain ⟨hk, -, -⟩ := BasicCutLength GP γ hclosed t t' ht0 htl ht'0 ht'l hne
    rw [hk, hifβ]
    linarith
  · obtain ⟨hk, hg, -⟩ := BasicCutLength GP γ hclosed t t' ht0 htl ht'0 ht'l hne
    rw [hk, hg, hifβ]
    linarith
