-- Prove2me | solution 1 for BBAssertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:09.693436+00:00
-- url     : https://prove2.me/submissions/15393410-8f99-4066-b205-092a3677def0

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_PaoliniStepanovExists
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_BBSamplingDiagonal
import Definitions.Def_Tablet_DiagonalizationGeneral
import Definitions.Def_Tablet_ClosingUp
import Definitions.Def_Tablet_MassSupFormula
import Definitions.Def_Tablet_MassFamilyBound
import Definitions.Def_Tablet_MassPosOfNonzero
import Definitions.Def_Tablet_EasyEstimateForMass
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_BBAssertion
import Theorems.Thm_BBSamplingDiagonal
import Theorems.Thm_ClosingUp
import Theorems.Thm_DiagonalizationGeneral
import Theorems.Thm_EasyEstimateForMass
import Theorems.Thm_MassFamilyBound
import Theorems.Thm_MassPosOfNonzero


set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hT0 : T.toFun ≠ 0) (hbdry : BoundaryZero T.toFun) :
    ∃ (n : ℕ → ℕ) (ghat : ℕ → ℕ → Curve E),
      (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesic (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l,
        massOfFunctional (curveCurrent (ghat l i)) ≤ ENNReal.ofReal (ghat l i).len) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω)
          atTop (nhds (T.toFun ω))) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (massOfFunctional (curveCurrent (ghat l i))).toReal)
        atTop (nhds 1)) ∧
      (Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
          ∑ i ∈ Finset.range (n l), (ghat l i).len)
        atTop (nhds 1)) := by
-- BODY
  -- Step 0: setup.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  have hDne : D.Nonempty := hDd.nonempty
  obtain ⟨x0⟩ := ‹Nonempty E›
  obtain ⟨F, hF⟩ := hPS T hT0 hbdry
  have hMne : massOfFunctional T.toFun ≠ 0 := MassPosOfNonzero _ hT0
  have hMtop : massOfFunctional T.toFun ≠ (⊤ : ℝ≥0∞) := T.finiteMass
  have hMRpos : 0 < (massOfFunctional T.toFun).toReal := ENNReal.toReal_pos hMne hMtop
  have hFne : F.massMeasure Set.univ ≠ 0 := by rw [hF]; exact hMne
  have hFMR : (F.massMeasure Set.univ).toReal = (massOfFunctional T.toFun).toReal := by rw [hF]
  obtain ⟨om, hom⟩ := DiagonalizationGeneral T F D hDc hDne hDd
  obtain ⟨n, hnpos, hntop, γ, hlen, hmassγ, hcurom, hend, hpsi⟩ :=
    BBSamplingDiagonal T.toFun F hFne om x0 D hDc hDne hDd
  have hcur := hom n γ hnpos hlen hcurom hpsi
  obtain ⟨ghat, gbar, kedge, hclosed, hpg, hb2l, hbprime, hcid, hdlen, hgbarcur⟩ :=
    ClosingUp T.toFun F GP x0 n hnpos γ hlen hcur hend
  have hnlpos : ∀ l : ℕ, 1 ≤ l → (0 : ℝ) < (n l : ℝ) * l := by
    intro l hl
    have h1 : (0 : ℝ) < (n l : ℝ) := by exact_mod_cast hnpos l
    have h2 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
    exact mul_pos h1 h2
  -- Step 2: clause (b), mass half; finiteness of the curve masses.
  have hmassle : ∀ g : Curve E,
      (massOfFunctional (curveCurrent g)).toReal ≤ g.len := fun g =>
    ENNReal.toReal_le_of_le_ofReal g.len_nonneg (EasyEstimateForMass g).2
  have hmfin : ∀ g : Curve E, massOfFunctional (curveCurrent g) ≠ (⊤ : ℝ≥0∞) := fun g =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (EasyEstimateForMass g).2
  have hfam : ∀ (g : Curve E) (p : ℕ) (ω : Fin p → Form1 E), (∀ q, (ω q).piLip ≤ 1) →
      (∀ x : E, ∑ q, |(ω q).f x| ≤ 1) →
      ∑ q, |curveCurrent g (ω q)| ≤ (massOfFunctional (curveCurrent g)).toReal := by
    intro g p ω h1 h2
    exact (ENNReal.ofReal_le_iff_le_toReal (hmfin g)).1 (MassFamilyBound _ p ω h1 h2)
  -- Step 3: clause (c) of the theorem (eq. closed1).
  have hclause_c : ∀ ω : Form1 E, Tendsto (fun l : ℕ =>
      (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
        ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω)
      atTop (nhds (T.toFun ω)) := by
    intro ω
    have h2 := (hcid ω).sub (hgbarcur ω)
    rw [sub_zero] at h2
    refine Tendsto.congr ?_ h2
    intro l
    rw [hFMR]; ring
  -- Step 4: the two sequences of eq. closed2, plus the auxiliary sequence of ClosingUp (d).
  obtain ⟨bseq, hbseq⟩ : ∃ b : ℕ → ℝ, b = fun l : ℕ => (1 / ((n l : ℝ) * l)) *
      ∑ i ∈ Finset.range (n l), (massOfFunctional (curveCurrent (ghat l i))).toReal := ⟨_, rfl⟩
  obtain ⟨cseq, hcseq⟩ : ∃ c : ℕ → ℝ, c = fun l : ℕ => (1 / ((n l : ℝ) * l)) *
      ∑ i ∈ Finset.range (n l), (ghat l i).len := ⟨_, rfl⟩
  obtain ⟨dseq, hdseq⟩ : ∃ d : ℕ → ℝ, d = fun l : ℕ => (1 / ((n l : ℝ) * l)) *
      ∑ i ∈ Finset.range (n l), (gbar l i).len := ⟨_, rfl⟩
  have hd0 : Tendsto dseq atTop (nhds 0) := by rw [hdseq]; exact hdlen
  have hb0 : ∀ l : ℕ, 0 ≤ bseq l := by
    intro l
    simp only [hbseq]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg)
  have hbc : ∀ l : ℕ, bseq l ≤ cseq l := by
    intro l
    simp only [hbseq, hcseq]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => hmassle (ghat l i)) (by positivity)
  have hc0 : ∀ l : ℕ, 0 ≤ cseq l := fun l => le_trans (hb0 l) (hbc l)
  -- Step 5: the upper bound limsup c ≤ 1.
  have hcd : ∀ᶠ l : ℕ in atTop, cseq l ≤ 1 + dseq l := by
    filter_upwards [eventually_ge_atTop 1] with l hl
    have hpos := hnlpos l hl
    have hne : ((n l : ℝ) * l) ≠ 0 := ne_of_gt hpos
    have hsum : ∑ i ∈ Finset.range (n l), (ghat l i).len
        ≤ (n l : ℝ) * l + ∑ i ∈ Finset.range (n l), (gbar l i).len := by
      have h := Finset.sum_le_sum
        (fun i (hi : i ∈ Finset.range (n l)) => hbprime l hl i (Finset.mem_range.1 hi))
      simpa [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul] using h
    simp only [hcseq, hdseq]
    calc (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (ghat l i).len
        ≤ (1 / ((n l : ℝ) * l)) *
            ((n l : ℝ) * l + ∑ i ∈ Finset.range (n l), (gbar l i).len) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 + (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len := by
          rw [mul_add, one_div_mul_cancel hne]
  have hdlt : ∀ᶠ l : ℕ in atTop, dseq l < 1 := hd0.eventually_lt_const (by norm_num)
  have hbddge_b : IsBoundedUnder (· ≥ ·) atTop bseq := by
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    exact Eventually.of_forall hb0
  have hbddge_c : IsBoundedUnder (· ≥ ·) atTop cseq := by
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    exact Eventually.of_forall hc0
  have hbddle_c : IsBoundedUnder (· ≤ ·) atTop cseq := by
    refine ⟨2, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hcd, hdlt] with l h1 h2
    linarith
  have hbddle_b : IsBoundedUnder (· ≤ ·) atTop bseq := by
    refine ⟨2, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hcd, hdlt] with l h1 h2
    have := hbc l
    linarith
  have hbddle_1d : IsBoundedUnder (· ≤ ·) atTop (fun l : ℕ => 1 + dseq l) := by
    refine ⟨2, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hdlt] with l h2
    linarith
  have hlimsup1d : limsup (fun l : ℕ => 1 + dseq l) atTop = 1 := by
    have h : Tendsto (fun l : ℕ => 1 + dseq l) atTop (nhds (1 + 0)) := hd0.const_add 1
    rw [add_zero] at h
    exact h.limsup_eq
  have hlimsupc : limsup cseq atTop ≤ 1 := by
    have h := Filter.limsup_le_limsup hcd hbddge_c.isCoboundedUnder_le hbddle_1d
    rwa [hlimsup1d] at h
  have hlimsupb : limsup bseq atTop ≤ 1 :=
    le_trans (Filter.limsup_le_limsup (Eventually.of_forall hbc)
      hbddge_b.isCoboundedUnder_le hbddle_c) hlimsupc
  -- Steps 6 and 7: the lower bound 1 ≤ liminf b, via MassSupFormula.
  have hL0 : (0 : ℝ) ≤ liminf bseq atTop :=
    Filter.le_liminf_of_le hbddle_b.isCoboundedUnder_ge (Eventually.of_forall hb0)
  have hsup : ∀ (p : ℕ) (ω : Fin p → Form1 E), (∀ q, (ω q).piLip ≤ 1) →
      (∀ x : E, ∑ q, |(ω q).f x| ≤ 1) →
      ∑ q, |T.toFun (ω q)| ≤ (massOfFunctional T.toFun).toReal * liminf bseq atTop := by
    intro p ω h1 h2
    have hu : Tendsto (fun l : ℕ => ∑ q : Fin p,
        |(massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
          ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) (ω q)|)
        atTop (nhds (∑ q : Fin p, |T.toFun (ω q)|)) :=
      tendsto_finsetSum _ (fun q _ => (hclause_c (ω q)).abs)
    have hv := hu.div_const ((massOfFunctional T.toFun).toReal)
    have hvle : ∀ᶠ l : ℕ in atTop,
        (∑ q : Fin p, |(massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
          ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) (ω q)|)
          / (massOfFunctional T.toFun).toReal ≤ bseq l := by
      filter_upwards [eventually_ge_atTop 1] with l hl
      have hpos := hnlpos l hl
      have hMdiv : (0 : ℝ) ≤ (massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) :=
        div_nonneg ENNReal.toReal_nonneg (le_of_lt hpos)
      have hstep : (∑ q : Fin p, |(massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
          ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) (ω q)|)
          ≤ (massOfFunctional T.toFun).toReal * bseq l := by
        calc (∑ q : Fin p, |(massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) (ω q)|)
            ≤ ∑ q : Fin p, ((massOfFunctional T.toFun).toReal / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), |curveCurrent (ghat l i) (ω q)| := by
              refine Finset.sum_le_sum fun q _ => ?_
              rw [abs_mul, abs_of_nonneg hMdiv]
              exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hMdiv
          _ = ((massOfFunctional T.toFun).toReal / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), ∑ q : Fin p, |curveCurrent (ghat l i) (ω q)| := by
              rw [← Finset.mul_sum, Finset.sum_comm]
          _ ≤ ((massOfFunctional T.toFun).toReal / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l),
                  (massOfFunctional (curveCurrent (ghat l i))).toReal := by
              refine mul_le_mul_of_nonneg_left ?_ hMdiv
              exact Finset.sum_le_sum fun i _ => hfam (ghat l i) p ω h1 h2
          _ = (massOfFunctional T.toFun).toReal * bseq l := by
              simp only [hbseq]; ring
      rw [div_le_iff₀ hMRpos]
      linarith
    have hbddge_v : IsBoundedUnder (· ≥ ·) atTop (fun l : ℕ =>
        (∑ q : Fin p, |(massOfFunctional T.toFun).toReal / ((n l : ℝ) * l) *
          ∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) (ω q)|)
          / (massOfFunctional T.toFun).toReal) := by
      refine ⟨0, ?_⟩
      rw [Filter.eventually_map]
      refine Eventually.of_forall fun l => ?_
      exact div_nonneg (Finset.sum_nonneg fun q _ => abs_nonneg _) hMRpos.le
    have h3 := Filter.liminf_le_liminf hvle hbddge_v hbddle_b.isCoboundedUnder_ge
    rw [hv.liminf_eq, div_le_iff₀ hMRpos] at h3
    linarith
  have hLb : (1 : ℝ) ≤ liminf bseq atTop := by
    have hms := hAK T ((massOfFunctional T.toFun).toReal * liminf bseq atTop)
      (mul_nonneg hMRpos.le hL0) (fun p ω hp hf => hsup p ω hp hf)
    have h3 := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hMRpos.le hL0) hms
    nlinarith [hMRpos, hL0]
  -- Step 8: assembling clause (d).
  have hliminfc : (1 : ℝ) ≤ liminf cseq atTop :=
    le_trans hLb (Filter.liminf_le_liminf (Eventually.of_forall hbc) hbddge_b
      hbddle_c.isCoboundedUnder_ge)
  have htb : Tendsto bseq atTop (nhds 1) :=
    tendsto_of_le_liminf_of_limsup_le hLb hlimsupb hbddle_b hbddge_b
  have htc : Tendsto cseq atTop (nhds 1) :=
    tendsto_of_le_liminf_of_limsup_le hliminfc hlimsupc hbddle_c hbddge_c
  refine ⟨n, ghat, hnpos, hntop, hclosed, ?_, ?_, hb2l, hclause_c, ?_, ?_⟩
  · exact fun l hl i hi => ⟨kedge l i, hpg l hl i hi⟩
  · exact fun l hl i hi => (EasyEstimateForMass (ghat l i)).2
  · rw [← hbseq]; exact htb
  · rw [← hcseq]; exact htc
