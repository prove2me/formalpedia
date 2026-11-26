-- Prove2me | solution 1 for BasicCutResolutionGeneral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:08.671015+00:00
-- url     : https://prove2.me/submissions/15aaa1ee-5325-439e-bc0c-e6c2e3967c78

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Definitions.Def_Tablet_BasicCutResolutionGeneral
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_SplicedBreakpointShortEdgeCount


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) (δ : ℝ) (hδ : 0 < δ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len)
    (hne : t ≠ t') :
    smallPieceCount (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 δ
      ≤ smallPieceCount γ δ + 3 := by
-- BODY
  -- (0) The circular arc `γ|_{[a,b]}` ends at `γ(b)` (the endpoint match `BasicCut` uses).
  have hrestrictEnd : ∀ (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ γ.len),
      (curveRestrict γ p q hp hpq hq).toFun (curveRestrict γ p q hp hpq hq).len = γ.toFun q := by
    intro p q hp hpq hq
    show γ.toFun (p + min (q - p) (max 0 (q - p))) = γ.toFun q
    rw [max_eq_right (by linarith), min_self]
    congr 1
    ring
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
  -- (1) A resolution `(k,s)` of `γ` attaining `smallPieceCount γ δ` (`Nat.sInf_mem`).
  have hSne : { c : ℕ | ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
      c = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card }.Nonempty := by
    obtain ⟨k0, s0, hs0⟩ := hpg
    exact ⟨_, k0, s0, hs0, rfl⟩
  obtain ⟨k, s, hres, hM⟩ : ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
      smallPieceCount γ δ = ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card :=
    Nat.sInf_mem hSne
  -- (2) The kept arc `γ|_{[t',t]}`, with its named resolution and its correspondence with `s`.
  obtain ⟨kA, sA, hkA1, hresA, hord, hwr⟩ :=
    ArcGeodesicResolution γ hclosed k s hres t' t ht'0 ht'len ht0 htlen
  obtain ⟨hmonoA, hsA0, hsAk, -⟩ := id hresA
  obtain ⟨hmonoS, hs0, -, -⟩ := id hres
  have hmn : ∀ a b : ℕ, a ≤ b → b ≤ kA → sA a ≤ sA b := by
    intro a b hab hb
    exact hmonoA (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hb⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb⟩) hab
  -- (3) The closing geodesic edge, resolved by a single edge.
  obtain ⟨r, hr⟩ := GeodesicIsPiecewiseGeodesic GP (γ.toFun t) (γ.toFun t')
  have hend : (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen).toFun
      (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen).len
        = (GP.G (γ.toFun t) (γ.toFun t')).toFun 0 := by
    rw [harcEnd, GP.start_eq]
  -- (4) Gluing the two resolutions: an explicit resolution `R` of `γ'` with `kA+1` edges whose
  -- first `kA` edges are exactly the arc's own edges.
  obtain ⟨R, hRlow, hglue⟩ : ∃ R : ℕ → ℝ, (∀ i, i ≤ kA → R i = sA i) ∧
      IsGeodesicResolution (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 (kA + 1) R := by
    refine ⟨fun i => if i ≤ kA then sA i
        else (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen).len + r (i - kA),
      fun i hi => if_pos hi, ?_⟩
    exact ConcatGeodesicResolution (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen)
      (GP.G (γ.toFun t) (γ.toFun t')) hend kA 1 sA r hresA hr
  have hle : smallPieceCount (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 δ ≤
      ((Finset.Icc 1 (kA + 1)).filter (fun j => R j - R (j - 1) < δ)).card :=
    Nat.sInf_le ⟨kA + 1, R, hglue, rfl⟩
  -- (5) Step 1b: the arc's *interior* small-edge count is at most `γ`'s own.
  have hcnt : ∀ a' b' : ℝ, ((Finset.Icc 1 k).filter
      (fun j => a' ≤ s (j - 1) ∧ s j ≤ b' ∧ s j - s (j - 1) < δ)).card
      ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card := by
    intro a' b'
    refine Finset.card_le_card ?_
    intro j hj
    obtain ⟨hjI, -, -, hsh⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjI, hsh⟩
  have hcntW : ∀ a' b' : ℝ, ((Finset.Icc 1 k).filter
      (fun j => (a' ≤ s (j - 1) ∨ s j ≤ b') ∧ s j - s (j - 1) < δ)).card
      ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card := by
    intro a' b'
    refine Finset.card_le_card ?_
    intro j hj
    obtain ⟨hjI, -, hsh⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjI, hsh⟩
  have hshW : ((Finset.Icc 2 (kA - 1)).filter
      (fun i => sA 1 ≤ sA (i - 1) ∧ sA i ≤ sA (kA - 1) ∧ sA i - sA (i - 1) < δ)).card
      ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card := by
    rcases lt_or_ge t t' with hlt | hge
    · -- Wrap case `t < t'`: the arc `γ|_{[t',t]}` runs off the end of `γ` and restarts at `0`.
      obtain ⟨j0, m, htail, hhead, hsplice⟩ := hwr hlt
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · -- `m = 0`: the head stretch covers every interior index.
        subst hm0
        refine ShiftedBreakpointShortEdgeCount k _ 2 (kA - 1) 0 0 δ (γ.len - t') (sA 1)
          (sA (kA - 1)) s sA (by omega) (by omega) ?_ (hcnt _ _)
        intro i h1 h2
        obtain ⟨p, q⟩ := hhead i (by omega) h2
        have e : i + 0 - 0 = i - 0 := by omega
        rw [e]
        exact ⟨p, by rw [q]; ring⟩
      rcases le_or_gt (kA - 1) m with hmbig | hmsmall
      · -- `m ≥ kA-1`: the tail stretch covers every interior index.
        refine ShiftedBreakpointShortEdgeCount k _ 2 (kA - 1) j0 1 δ (-t') (sA 1) (sA (kA - 1))
          s sA (by omega) (by omega) ?_ (hcnt _ _)
        intro i h1 h2
        have hidx : i + j0 - 1 = j0 + (i - 1) := by omega
        obtain ⟨p, q⟩ := htail i (by omega) (by omega)
        rw [hidx]
        exact ⟨p, by rw [q]; ring⟩
      · -- `1 ≤ m ≤ kA-2`: both stretches are live and meet at the splice.
        refine SplicedBreakpointShortEdgeCount k _ kA j0 m δ (-t') (γ.len - t') (sA 1)
          (sA (kA - 1)) s sA hmonoS hs0 hm1 (by omega) ?_ ?_ ?_ ?_ (hcntW _ _)
        · intro i h1 h2
          obtain ⟨p, q⟩ := htail i h1 h2
          exact ⟨p, by rw [q]; ring⟩
        · intro i h1 h2
          obtain ⟨p, q⟩ := hhead i h1 h2
          exact ⟨p, by rw [q]; ring⟩
        · rw [hsplice hm1]; ring
        · -- the margin: the head stretch lands left of `t`, the tail stretch right of `t'`
          have hlenA : (curveArc γ hclosed t' t ht'0 ht'len ht0 htlen).len
              = (γ.len - t') + (t - 0) := by
            unfold curveArc
            rw [dif_neg (not_le.mpr hlt)]
            rfl
          obtain ⟨-, q1⟩ := htail 1 le_rfl hm1
          obtain ⟨-, q2⟩ := hhead (kA - 1) hmsmall le_rfl
          have e1 : j0 + (1 - 1) = j0 := by omega
          rw [e1] at q1
          have hA0 : sA 0 ≤ sA 1 := hmn 0 1 (by omega) (by omega)
          have hAk : sA (kA - 1) ≤ sA kA := hmn _ _ (by omega) le_rfl
          rw [hsA0, q1] at hA0
          rw [hsAk, hlenA, q2] at hAk
          rw [q1, q2]
          linarith
    · -- Ordinary case `t' ≤ t`: a single affine reindexing.
      obtain ⟨j0, hcorr0⟩ := hord hge
      refine ShiftedBreakpointShortEdgeCount k _ 2 (kA - 1) j0 1 δ (-t') (sA 1) (sA (kA - 1))
        s sA (by omega) (by omega) ?_ (hcnt _ _)
      intro i h1 h2
      have hidx : i + j0 - 1 = j0 + (i - 1) := by omega
      obtain ⟨p, q⟩ := hcorr0 i (by omega) h2
      rw [hidx]
      exact ⟨p, by rw [q]; ring⟩
  have hinterior : ((Finset.Icc 2 (kA - 1)).filter (fun i => sA i - sA (i - 1) < δ)).card
      ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card := by
    refine le_trans (Finset.card_le_card ?_) hshW
    intro i hi
    obtain ⟨hiI, hsh⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi2, hiK⟩ := Finset.mem_Icc.mp hiI
    exact Finset.mem_filter.mpr ⟨hiI, hmn 1 (i - 1) (by omega) (by omega),
      hmn i (kA - 1) hiK (by omega), hsh⟩
  -- (6) Step 1a + the closing edge: the three extra indices `1`, `kA`, `kA+1`.
  have hsub : ((Finset.Icc 1 (kA + 1)).filter (fun j => R j - R (j - 1) < δ)) ⊆
      ((Finset.Icc 2 (kA - 1)).filter (fun i => sA i - sA (i - 1) < δ)) ∪ {1, kA, kA + 1} := by
    intro j hj
    obtain ⟨hjI, hjsh⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hjI
    by_cases hc1 : j = 1
    · exact Finset.mem_union_right _ (by simp [hc1])
    by_cases hc2 : j = kA
    · exact Finset.mem_union_right _ (by simp [hc2])
    by_cases hc3 : j = kA + 1
    · exact Finset.mem_union_right _ (by simp [hc3])
    refine Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩)
    rw [← hRlow j (by omega), ← hRlow (j - 1) (by omega)]
    exact hjsh
  have h3 : ({1, kA, kA + 1} : Finset ℕ).card ≤ 3 := by
    have e1 : ({kA + 1} : Finset ℕ).card = 1 := Finset.card_singleton _
    have e2 := Finset.card_insert_le kA ({kA + 1} : Finset ℕ)
    have e3 := Finset.card_insert_le 1 (insert kA ({kA + 1} : Finset ℕ))
    omega
  refine le_trans hle ?_
  rw [hM]
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  omega
