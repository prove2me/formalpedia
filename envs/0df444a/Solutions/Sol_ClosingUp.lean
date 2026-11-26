-- Prove2me | solution 1 for ClosingUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:30.813258+00:00
-- url     : https://prove2.me/submissions/58f3041a-00f7-4ea4-8920-8a0c53a6c666

import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_SamplingEndpoints
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_SamplingPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicSampledCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentReverse
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_ClosingUp
import Theorems.Thm_ConcatPiecewiseGeodesic
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentReverse
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_GeodesicSampledCurrent
import Theorems.Thm_SamplingEndpoints
import Theorems.Thm_SamplingPiecewiseGeodesic


set_option autoImplicit false
open Set Filter Finset MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T) (GP : GeodesicPairing E) (x0 : E)
    (n : ℕ → ℕ) (hn_pos : ∀ l : ℕ, 0 < n l)
    (γ : ℕ → ℕ → Curve E)
    (hlen : ∀ l : ℕ, 1 ≤ l → ∀ i < n l, (γ l i).len = (l : ℝ))
    (hcur : ∀ ω : Form1 E, Tendsto (fun l : ℕ =>
        (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
          ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
        atTop (nhds (T ω)))
    (hend : ∀ r : ℚ, 0 < r →
      (Tendsto (fun l : ℕ => (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
          (if (r : ℝ) ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)) atTop
        (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
          (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal)))
      ∧ (Tendsto (fun l : ℕ => (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
          (if (r : ℝ) ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0)) atTop
        (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
          (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal)))) :
    ∃ (ghat gbar : ℕ → ℕ → Curve E) (k : ℕ → ℕ → ℕ),
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsClosedCurve (ghat l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, IsPiecewiseGeodesicWith (ghat l i) (k l i)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ 2 * (l : ℝ)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (ghat l i).len ≤ (l : ℝ) + (gbar l i).len) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            (∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω
              + ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω))
          atTop (nhds (T ω))) ∧
      (Tendsto (fun l : ℕ =>
          (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len)
          atTop (nhds 0)) ∧
      (∀ ω : Form1 E, Tendsto (fun l : ℕ =>
          (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω)
          atTop (nhds 0)) := by
-- BODY
  classical
  -- ## The sampling scale `δ_l = 1/(l+1)`.
  let δ : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1)
  have hδpos : ∀ l : ℕ, 0 < δ l := by
    intro l; show 0 < 1 / ((l : ℝ) + 1); positivity
  have hδlt : ∀ l : ℕ, 1 ≤ l → ∀ i : ℕ, i < n l → δ l < (γ l i).len := by
    intro l hl i hi
    rw [hlen l hl i hi]
    show 1 / ((l : ℝ) + 1) < (l : ℝ)
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hl1 (show (0 : ℝ) ≤ (l : ℝ) + 1 by linarith)]
  have hδtendsto : Tendsto δ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- ## A dummy `1`-form, used only to invoke length-only conjuncts of `GeodesicSampledCurrent`.
  have hω0 : Form1 E :=
    { f := fun _ => 0, fBound := 0, f_bounded := fun x => by simp
      fLip := 0, f_lipschitz := fun x y => by simp
      pi := fun _ => 0, piLip := 0, pi_lipschitz := fun x y => by simp }
  let ghat : ℕ → ℕ → Curve E := fun l i => if h : 1 ≤ l ∧ i < n l then
      curveConcat (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2))
        (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0))
        (by
          rw [(SamplingEndpoints GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).2, GP.start_eq])
    else GP.G x0 x0
  let gbar : ℕ → ℕ → Curve E := fun l i => if h : 1 ≤ l ∧ i < n l then
      GP.G ((γ l i).toFun 0) ((γ l i).toFun (γ l i).len)
    else GP.G x0 x0
  let k : ℕ → ℕ → ℕ := fun l i => if h : 1 ≤ l ∧ i < n l then
      (SamplingPiecewiseGeodesic GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).choose + 1
    else 1
  -- ## Named unfolding equations for `ghat`, `gbar`, `k` on the "good" indices.
  have hcompatfun : ∀ l i (h : 1 ≤ l ∧ i < n l),
      (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).toFun
        (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).len
        = (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)).toFun 0 := by
    intro l i h
    rw [(SamplingEndpoints GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).2, GP.start_eq]
  have hghat_pos : ∀ l i (h : 1 ≤ l ∧ i < n l), ghat l i =
      curveConcat (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2))
        (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)) (hcompatfun l i h) :=
    fun l i h => dif_pos h
  have hgbar_pos : ∀ l i (h : 1 ≤ l ∧ i < n l), gbar l i =
      GP.G ((γ l i).toFun 0) ((γ l i).toFun (γ l i).len) :=
    fun l i h => dif_pos h
  have hk_pos : ∀ l i (h : 1 ≤ l ∧ i < n l), k l i =
      (SamplingPiecewiseGeodesic GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).choose + 1 :=
    fun l i h => dif_pos h
  -- ## (d) averaged length of `gbar` → 0, proved once here so (e) can reuse it.
  have hd : Tendsto (fun l : ℕ =>
      (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len)
      atTop (nhds 0) := by
    have hLnonneg : ∀ l : ℕ, 0 ≤
        (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len := by
      intro l
      have hsum_nonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.range (n l), (gbar l i).len :=
        Finset.sum_nonneg (fun i _ => (gbar l i).len_nonneg)
      have hden_nonneg : (0 : ℝ) ≤ 1 / ((n l : ℝ) * (l : ℝ)) := by positivity
      exact mul_nonneg hden_nonneg hsum_nonneg
    -- ## Pointwise bound (§): `length(gbar_i) ≤ 2r + l·𝟙[r≤d(x0,b)] + l·𝟙[r≤d(x0,e)]`.
    have hpt : ∀ l : ℕ, 1 ≤ l → ∀ i : ℕ, i < n l → ∀ r : ℝ, 0 < r →
        (gbar l i).len ≤ 2 * r +
          (l : ℝ) * (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0) +
          (l : ℝ) * (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) := by
      intro l hl i hi r hr
      have h : 1 ≤ l ∧ i < n l := ⟨hl, hi⟩
      have hlen_eq : (gbar l i).len = dist ((γ l i).toFun 0) ((γ l i).toFun (γ l i).len) := by
        rw [hgbar_pos l i h, GP.len_eq]
      have hLip : dist ((γ l i).toFun 0) ((γ l i).toFun (γ l i).len) ≤ (l : ℝ) := by
        have hdlip : dist ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)
            ≤ |(γ l i).len - (0 : ℝ)| := by
          simpa [Real.dist_eq] using (CurveLipschitz (γ l i)).dist_le_mul (γ l i).len 0
        have habs : |(γ l i).len - (0 : ℝ)| = (l : ℝ) := by
          rw [sub_zero, abs_of_nonneg (γ l i).len_nonneg, hlen l hl i hi]
        rw [habs] at hdlip
        rwa [dist_comm] at hdlip
      have htri : dist ((γ l i).toFun 0) ((γ l i).toFun (γ l i).len)
          ≤ dist ((γ l i).toFun 0) x0 + dist ((γ l i).toFun (γ l i).len) x0 := by
        have h0 := dist_triangle ((γ l i).toFun 0) x0 ((γ l i).toFun (γ l i).len)
        rwa [dist_comm x0 ((γ l i).toFun (γ l i).len)] at h0
      rw [hlen_eq]
      by_cases hb : r ≤ dist ((γ l i).toFun 0) x0
      · by_cases he : r ≤ dist ((γ l i).toFun (γ l i).len) x0
        · rw [if_pos hb, if_pos he]
          nlinarith [hLip, hr.le, (Nat.cast_nonneg l : (0 : ℝ) ≤ (l : ℝ))]
        · rw [if_pos hb, if_neg he]
          nlinarith [hLip, hr.le, (Nat.cast_nonneg l : (0 : ℝ) ≤ (l : ℝ))]
      · by_cases he : r ≤ dist ((γ l i).toFun (γ l i).len) x0
        · rw [if_neg hb, if_pos he]
          nlinarith [hLip, hr.le, (Nat.cast_nonneg l : (0 : ℝ) ≤ (l : ℝ))]
        · rw [if_neg hb, if_neg he]
          push_neg at hb he
          nlinarith [htri, hb, he]
    -- ## Summed bound (§): still with an undivided sum on the right.
    have hsum_ineq : ∀ l : ℕ, 1 ≤ l → ∀ r : ℝ, 0 < r →
        ∑ i ∈ Finset.range (n l), (gbar l i).len ≤
          (n l : ℝ) * (2 * r)
            + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
            + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) := by
      intro l hl r hr
      have hterm : ∀ i ∈ Finset.range (n l), (gbar l i).len ≤
          2 * r + (l : ℝ) * (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
            + (l : ℝ) * (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) :=
        fun i hi => hpt l hl i (Finset.mem_range.mp hi) r hr
      calc ∑ i ∈ Finset.range (n l), (gbar l i).len
          ≤ ∑ i ∈ Finset.range (n l),
              (2 * r + (l : ℝ) * (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
                + (l : ℝ) * (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0)) :=
            Finset.sum_le_sum hterm
        _ = (n l : ℝ) * (2 * r)
              + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                  (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
              + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                  (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.mul_sum]
    have hLle : ∀ l : ℕ, 1 ≤ l → ∀ r : ℝ, 0 < r →
        (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len ≤
          (1 / ((n l : ℝ) * (l : ℝ))) *
            ((n l : ℝ) * (2 * r)
              + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                  (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
              + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                  (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0)) := by
      intro l hl r hr
      have hden_nonneg : (0 : ℝ) ≤ 1 / ((n l : ℝ) * (l : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_left (hsum_ineq l hl r hr) hden_nonneg
    -- ## Algebraic identity turning the undivided bound into the `hend`-matching shape.
    have hUeq : ∀ l : ℕ, 1 ≤ l → ∀ r : ℝ,
        (1 / ((n l : ℝ) * (l : ℝ))) *
            ((n l : ℝ) * (2 * r)
              + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                  (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
              + (l : ℝ) * ∑ i ∈ Finset.range (n l),
                  (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0))
          = 2 * r / (l : ℝ)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) := by
      intro l hl r
      have hnl : (n l : ℝ) ≠ 0 := by exact_mod_cast (hn_pos l).ne'
      have hlne : (l : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hl)
      field_simp
    have hLle' : ∀ l : ℕ, 1 ≤ l → ∀ r : ℝ, 0 < r →
        (1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len ≤
          2 * r / (l : ℝ)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) := by
      intro l hl r hr
      rw [← hUeq l hl r]
      exact hLle l hl r hr
    -- ## Continuity-from-above: `μ_T({x : m ≤ d(x,x0)}) → 0` as `m → ∞`, `m : ℕ`.
    have hScont : Continuous (fun x : E => dist x x0) := continuous_id.dist continuous_const
    have hSmeas : ∀ m : ℕ, MeasurableSet {x : E | (m : ℝ) ≤ dist x x0} := by
      intro m
      have heq : {x : E | (m : ℝ) ≤ dist x x0} = (fun x : E => dist x x0) ⁻¹' Set.Ici (m : ℝ) :=
        rfl
      rw [heq]
      exact (isClosed_Ici.preimage hScont).measurableSet
    have hSanti : Antitone (fun m : ℕ => {x : E | (m : ℝ) ≤ dist x x0}) := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_trans (by exact_mod_cast hab) hx
    have hSempty : (⋂ m : ℕ, {x : E | (m : ℝ) ≤ dist x x0}) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨m, hm⟩ := exists_nat_gt (dist x x0)
      exact absurd (hx m) (not_le.mpr hm)
    haveI := F.massMeasure_finite
    have hSfin : ∃ m : ℕ, F.massMeasure {x : E | (m : ℝ) ≤ dist x x0} ≠ ⊤ :=
      ⟨0, measure_ne_top _ _⟩
    have hSmeasureTendsto : Tendsto (fun m : ℕ => F.massMeasure {x : E | (m : ℝ) ≤ dist x x0})
        atTop (nhds (F.massMeasure (⋂ m : ℕ, {x : E | (m : ℝ) ≤ dist x x0}))) :=
      tendsto_measure_iInter_atTop (fun m => (hSmeas m).nullMeasurableSet) hSanti hSfin
    rw [hSempty, measure_empty] at hSmeasureTendsto
    have hSrealTendsto : Tendsto (fun m : ℕ => (F.massMeasure {x : E | (m : ℝ) ≤ dist x x0}).toReal)
        atTop (nhds 0) := by
      have h0 : (0 : ENNReal) ≠ ⊤ := by simp
      have hcomp := (ENNReal.tendsto_toReal h0).comp hSmeasureTendsto
      simpa [Function.comp_def] using hcomp
    have hVtendsto : Tendsto (fun m : ℕ =>
        2 * (F.massMeasure Set.univ).toReal⁻¹ *
          (F.massMeasure {x : E | (m : ℝ) ≤ dist x x0}).toReal)
        atTop (nhds 0) := by
      have hcm := hSrealTendsto.const_mul (2 * (F.massMeasure Set.univ).toReal⁻¹)
      simpa using hcm
    -- ## Assemble: `L l ≥ 0` always, and `L l < ε` eventually for every `ε > 0`.
    refine tendsto_order.mpr ⟨?_, ?_⟩
    · intro a ha
      filter_upwards with l
      exact lt_of_lt_of_le ha (hLnonneg l)
    · intro ε hε
      have hev : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
          2 * (F.massMeasure Set.univ).toReal⁻¹ *
              (F.massMeasure {x : E | (m : ℝ) ≤ dist x x0}).toReal < ε :=
        (Filter.eventually_ge_atTop 1).and ((tendsto_order.mp hVtendsto).2 ε hε)
      obtain ⟨m, hm1, hmε⟩ := hev.exists
      have hrQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm1
      have hendm := hend (m : ℚ) hrQ
      have hcast : (((m : ℚ) : ℝ)) = (m : ℝ) := by push_cast; ring
      rw [hcast] at hendm
      set r : ℝ := (m : ℝ) with hr_def
      have hrpos : 0 < r := by rw [hr_def]; exact_mod_cast hm1
      have ht1 : Tendsto (fun l : ℕ => 2 * r / (l : ℝ)) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (2 * r)
      have hUtendsto : Tendsto (fun l : ℕ =>
          2 * r / (l : ℝ)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0))
          atTop (nhds (0
              + (F.massMeasure Set.univ).toReal⁻¹ * (F.massMeasure {x : E | r ≤ dist x x0}).toReal
              + (F.massMeasure Set.univ).toReal⁻¹
                  * (F.massMeasure {x : E | r ≤ dist x x0}).toReal)) :=
        (ht1.add hendm.1).add hendm.2
      have hVeq : (0
          + (F.massMeasure Set.univ).toReal⁻¹ * (F.massMeasure {x : E | r ≤ dist x x0}).toReal
          + (F.massMeasure Set.univ).toReal⁻¹ * (F.massMeasure {x : E | r ≤ dist x x0}).toReal)
          = 2 * (F.massMeasure Set.univ).toReal⁻¹
              * (F.massMeasure {x : E | r ≤ dist x x0}).toReal := by
        ring
      rw [hVeq] at hUtendsto
      have hUlt : ∀ᶠ l : ℕ in atTop,
          2 * r / (l : ℝ)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0)
            + (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
                (if r ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0) < ε :=
        (tendsto_order.mp hUtendsto).2 ε hmε
      filter_upwards [hUlt, Filter.eventually_ge_atTop 1] with l hUl hl1
      exact lt_of_le_of_lt (hLle' l hl1 r hrpos) hUl
  refine ⟨ghat, gbar, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) closedness
    intro l hl i hi
    have h : 1 ≤ l ∧ i < n l := ⟨hl, hi⟩
    rw [hghat_pos l i h]
    unfold IsClosedCurve
    rw [(CurveConcatEndpoints _ _ (hcompatfun l i h)).2,
      (CurveConcatEndpoints _ _ (hcompatfun l i h)).1,
      GP.end_eq, (SamplingEndpoints GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi)).1]
  · -- (a) piecewise geodesic
    intro l hl i hi
    have h : 1 ≤ l ∧ i < n l := ⟨hl, hi⟩
    rw [hghat_pos l i h, hk_pos l i h]
    exact ConcatPiecewiseGeodesic _ _ _ _ 1
      (SamplingPiecewiseGeodesic GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)).choose_spec
      (GeodesicIsPiecewiseGeodesic GP _ _)
  · -- (b) length ≤ 2l
    intro l hl i hi
    have h : 1 ≤ l ∧ i < n l := ⟨hl, hi⟩
    rw [hghat_pos l i h]
    have hAlen : (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi)).len ≤ (γ l i).len :=
      (GeodesicSampledCurrent GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi) hω0).1
    have hBlen : (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)).len ≤ (l : ℝ) := by
      rw [GP.len_eq]
      have hlip : dist ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)
          ≤ |(γ l i).len - (0 : ℝ)| := by
        simpa [Real.dist_eq] using (CurveLipschitz (γ l i)).dist_le_mul (γ l i).len 0
      have habs : |(γ l i).len - (0 : ℝ)| = (l : ℝ) := by
        rw [sub_zero, abs_of_nonneg (γ l i).len_nonneg, hlen l hl i hi]
      rw [habs] at hlip
      exact hlip
    have heq : (curveConcat
        (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi))
        (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)) (hcompatfun l i h)).len
        = (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi)).len
          + (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)).len := rfl
    rw [heq]
    rw [hlen l hl i hi] at hAlen
    linarith
  · -- (b') length ≤ l + gbar.len
    intro l hl i hi
    have h : 1 ≤ l ∧ i < n l := ⟨hl, hi⟩
    rw [hghat_pos l i h, hgbar_pos l i h]
    have hAlen : (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi)).len ≤ (γ l i).len :=
      (GeodesicSampledCurrent GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi) hω0).1
    have heq : (curveConcat
        (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi))
        (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)) (hcompatfun l i h)).len
        = (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l hl i hi)).len
          + (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)).len := rfl
    rw [heq]
    rw [hlen l hl i hi] at hAlen
    have hsym : (GP.G ((γ l i).toFun (γ l i).len) ((γ l i).toFun 0)).len
        = (GP.G ((γ l i).toFun 0) ((γ l i).toFun (γ l i).len)).len := by
      rw [GP.len_eq, GP.len_eq, dist_comm]
    rw [hsym]
    linarith
  · -- (c) current-average splitting identity
    -- ## (*) the current-splitting identity: `[[ghat]] + [[gbar]] = [[γ^δ]]`.
    have hstar : ∀ l i (h : 1 ≤ l ∧ i < n l) (ω : Form1 E),
        curveCurrent (ghat l i) ω + curveCurrent (gbar l i) ω
          = curveCurrent (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)) ω := by
      intro l i h ω
      rw [hghat_pos l i h, hgbar_pos l i h]
      rw [CurrentConcatAdditive _ _ (hcompatfun l i h) ω]
      set A := curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)
      set e := (γ l i).toFun (γ l i).len with he
      set b := (γ l i).toFun 0 with hb
      have hlenGe : (GP.G b e).len = (GP.G e b).len := by
        rw [GP.len_eq, GP.len_eq, dist_comm]
      have hrevcond : ∀ t ∈ Set.Icc (0 : ℝ) (GP.G e b).len,
          (GP.G b e).toFun t = (GP.G e b).toFun ((GP.G e b).len - t) := by
        intro t ht
        rw [GP.len_eq] at ht ⊢
        exact GP.reversal e b t ht
      have hrev : curveCurrent (GP.G b e) ω = - curveCurrent (GP.G e b) ω :=
        CurrentReverse (GP.G e b) (GP.G b e) hlenGe hrevcond ω
      rw [hrev]
      ring
    -- ## Per-index chord bound: `|[[γ^δ]](ω) - [[γ]](ω)| ≤ fLip·piLip·δ_l·l`.
    have hdiff : ∀ l i (h : 1 ≤ l ∧ i < n l) (ω : Form1 E),
        |curveCurrent (curveSampling GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2)) ω
            - curveCurrent (γ l i) ω|
          ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l * (l : ℝ) := by
      intro l i h ω
      have hb := (GeodesicSampledCurrent GP (γ l i) (δ l) (hδpos l) (hδlt l h.1 i h.2) ω).2
      rwa [hlen l h.1 i h.2] at hb
    -- ## Sum-level bound, for a fixed `l ≥ 1` and `ω`.
    have hsumbound : ∀ (l : ℕ), 1 ≤ l → ∀ ω : Form1 E,
        |(∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω
            + ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω)
            - ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω|
          ≤ (n l : ℝ) * ((ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l * (l : ℝ)) := by
      intro l hl ω
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ i ∈ Finset.range (n l),
          |curveCurrent (ghat l i) ω + curveCurrent (gbar l i) ω - curveCurrent (γ l i) ω|
            ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l * (l : ℝ) := by
        intro i hi
        have hi' : i < n l := Finset.mem_range.mp hi
        rw [hstar l i ⟨hl, hi'⟩ ω]
        exact hdiff l i ⟨hl, hi'⟩ ω
      calc |(∑ i ∈ Finset.range (n l), (curveCurrent (ghat l i) ω + curveCurrent (gbar l i) ω))
              - ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω|
          = |∑ i ∈ Finset.range (n l),
              (curveCurrent (ghat l i) ω + curveCurrent (gbar l i) ω
                - curveCurrent (γ l i) ω)| := by
            rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i ∈ Finset.range (n l),
              |curveCurrent (ghat l i) ω + curveCurrent (gbar l i) ω
                - curveCurrent (γ l i) ω| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.range (n l), (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l * (l : ℝ) :=
            Finset.sum_le_sum hterm
        _ = (n l : ℝ) * ((ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l * (l : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- ## Assemble via the squeeze theorem.
    intro ω
    have hzero : Tendsto (fun l : ℕ =>
        (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            (∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω
              + ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω)
          - (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
        atTop (nhds 0) := by
      apply squeeze_zero_norm' (a := fun l : ℕ =>
          (F.massMeasure Set.univ).toReal * (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l)
      · filter_upwards [Filter.eventually_ge_atTop 1] with l hl
        have hM : (0 : ℝ) ≤ (F.massMeasure Set.univ).toReal := ENNReal.toReal_nonneg
        have hnl : (0 : ℝ) < (n l : ℝ) := by exact_mod_cast hn_pos l
        have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
        have hfrac_nonneg : (0 : ℝ) ≤ (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) := by
          positivity
        have hsb := hsumbound l hl ω
        have hne : (n l : ℝ) * (l : ℝ) ≠ 0 := mul_ne_zero hnl.ne' hlpos.ne'
        show |_| ≤ _
        calc |(F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
                (∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω
                  + ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω)
              - (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
                  ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω|
            = (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
                |(∑ i ∈ Finset.range (n l), curveCurrent (ghat l i) ω
                    + ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω)
                  - ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω| := by
              rw [← mul_sub, abs_mul, abs_of_nonneg hfrac_nonneg]
          _ ≤ (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
                ((n l : ℝ) * ((ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l * (l : ℝ))) :=
              mul_le_mul_of_nonneg_left hsb hfrac_nonneg
          _ = (F.massMeasure Set.univ).toReal * (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ l := by
              rw [div_mul_eq_mul_div, div_eq_iff hne]
              ring
      · have hcm := hδtendsto.const_mul
          ((F.massMeasure Set.univ).toReal * (ω.fLip : ℝ) * (ω.piLip : ℝ))
        simpa [mul_assoc] using hcm
    have := (hcur ω).add hzero
    simpa using this
  · -- (d) averaged length of gbar → 0
    exact hd
  · -- (e) averaged current of gbar → 0
    intro ω
    apply squeeze_zero_norm' (a := fun l : ℕ =>
        (F.massMeasure Set.univ).toReal * (ω.fBound : ℝ) * (ω.piLip : ℝ) *
          ((1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len))
    · filter_upwards with l
      have hMnn : (0 : ℝ) ≤ (F.massMeasure Set.univ).toReal := ENNReal.toReal_nonneg
      have hfrac_nonneg : (0 : ℝ) ≤ (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) := by
        positivity
      have hsum_abs : |∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω|
          ≤ ∑ i ∈ Finset.range (n l), (ω.fBound : ℝ) * (ω.piLip : ℝ) * (gbar l i).len :=
        (abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun i _ => CurveCurrentBound (gbar l i) ω))
      have hsum_eq : ∑ i ∈ Finset.range (n l), (ω.fBound : ℝ) * (ω.piLip : ℝ) * (gbar l i).len
          = (ω.fBound : ℝ) * (ω.piLip : ℝ) * ∑ i ∈ Finset.range (n l), (gbar l i).len := by
        rw [← Finset.mul_sum]
      show |_| ≤ _
      calc |(F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω|
          = (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              |∑ i ∈ Finset.range (n l), curveCurrent (gbar l i) ω| := by
            rw [abs_mul, abs_of_nonneg hfrac_nonneg]
        _ ≤ (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ((ω.fBound : ℝ) * (ω.piLip : ℝ) * ∑ i ∈ Finset.range (n l), (gbar l i).len) := by
            rw [← hsum_eq]
            exact mul_le_mul_of_nonneg_left hsum_abs hfrac_nonneg
        _ = (F.massMeasure Set.univ).toReal * (ω.fBound : ℝ) * (ω.piLip : ℝ) *
              ((1 / ((n l : ℝ) * l)) * ∑ i ∈ Finset.range (n l), (gbar l i).len) := by
            ring
    · have hcm := hd.const_mul
        ((F.massMeasure Set.univ).toReal * (ω.fBound : ℝ) * (ω.piLip : ℝ))
      simpa using hcm
