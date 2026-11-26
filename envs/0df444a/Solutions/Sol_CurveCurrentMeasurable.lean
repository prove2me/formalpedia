-- Prove2me | solution 1 for CurveCurrentMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:03.500456+00:00
-- url     : https://prove2.me/submissions/86c93c6d-1518-4aaa-84be-4fc7d30a395d

import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_CurveCurrentMeasurable
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_RestrictCurrentFormula


set_option autoImplicit false
open MeasureTheory Finset
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ω : Form1 E) : Measurable (fun g : Curve E => curveCurrent g ω) := by
-- BODY
  classical
  set R : ℕ → Curve E → ℝ := fun m g =>
    ∑ i ∈ Finset.range m,
      ω.f (g.toFun ((i : ℝ) / m * g.len)) *
        (ω.pi (g.toFun (((i : ℝ) + 1) / m * g.len)) - ω.pi (g.toFun ((i : ℝ) / m * g.len)))
    with hR
  have hmeas : ∀ m : ℕ, Measurable (R m) := by
    intro m
    simp only [hR]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have hf : Measurable (ω.f) := ω.f_lipschitz.continuous.measurable
    have hpi : Measurable (ω.pi) := ω.pi_lipschitz.continuous.measurable
    have h1 : Measurable (fun g : Curve E => g.toFun ((i : ℝ) / m * g.len)) :=
      CurveScaledEvalMeasurable ((i : ℝ) / m)
    have h2 : Measurable (fun g : Curve E => g.toFun (((i : ℝ) + 1) / m * g.len)) :=
      CurveScaledEvalMeasurable (((i : ℝ) + 1) / m)
    exact (hf.comp h1).mul ((hpi.comp h2).sub (hpi.comp h1))
  have htend : ∀ g : Curve E,
      Filter.Tendsto (fun m : ℕ => R m g) Filter.atTop (nhds (curveCurrent g ω)) := by
    intro g
    have hbound : ∀ m : ℕ, 1 ≤ m →
        |R m g - curveCurrent g ω|
          ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * g.len ^ 2 / (2 * m) := by
      intro m hm
      have hm0 : (0:ℝ) < m := by exact_mod_cast hm
      set s : ℕ → ℝ := fun i => (i : ℝ) / m * g.len with hs
      have hmono : MonotoneOn s (Set.Icc (0:ℕ) m) := by
        intro i _ j _ hij
        have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
        simp only [hs]
        gcongr
        exact g.len_nonneg
      have h0 : s 0 = 0 := by simp [hs]
      have hk : s m = g.len := by
        simp only [hs]
        field_simp
      have hresol := CurrentResolutionAdditive g ω m s hmono h0 hk
      have hbounds : ∀ i ∈ Finset.range m,
          (0:ℝ) ≤ s i ∧ s i ≤ s (i+1) ∧ s (i+1) ≤ g.len := by
        intro i hi
        have hi' : i < m := Finset.mem_range.mp hi
        have h2 : (i:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hi'
        have ha : (0:ℝ) ≤ s i := by
          simp only [hs]
          exact mul_nonneg (div_nonneg (Nat.cast_nonneg i) hm0.le) g.len_nonneg
        have hab : s i ≤ s (i + 1) := by
          simp only [hs]
          push_cast
          gcongr
          · exact g.len_nonneg
          · linarith
        have hb : s (i + 1) ≤ g.len := by
          simp only [hs]
          push_cast
          calc ((i:ℝ) + 1) / m * g.len ≤ 1 * g.len := by
                gcongr
                · exact g.len_nonneg
                · exact (div_le_one hm0).mpr h2
            _ = g.len := one_mul _
        exact ⟨ha, hab, hb⟩
      have hchord : ∀ i ∈ Finset.range m,
          |(∫ t in (s i)..(s (i+1)), ω.f (g.toFun t) * deriv (ω.pi ∘ g.toFun) t)
              - (ω.f (g.toFun (s i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i))))|
            ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2 := by
        intro i hi
        obtain ⟨ha, hab, hb⟩ := hbounds i hi
        have hrestr := RestrictCurrentFormula g (s i) (s (i+1)) ha hab hb ω
        set σ := curveRestrict g (s i) (s (i+1)) ha hab hb with hσ
        have hlen : σ.len = s (i + 1) - s i := rfl
        have ht0 : σ.toFun 0 = g.toFun (s i) := by
          show g.toFun (s i + min (s (i+1) - s i) (max 0 0)) = g.toFun (s i)
          have : max (0:ℝ) 0 = 0 := max_self 0
          rw [this, min_eq_right (by linarith), add_zero]
        have htL : σ.toFun σ.len = g.toFun (s (i + 1)) := by
          rw [hlen]
          show g.toFun (s i + min (s (i+1) - s i) (max 0 (s (i+1) - s i))) = g.toFun (s (i+1))
          have hnn : (0:ℝ) ≤ s (i+1) - s i := by linarith
          rw [max_eq_right hnn, min_self]
          ring_nf
        have hlenval : s (i + 1) - s i = g.len / m := by
          simp only [hs]
          push_cast
          field_simp
          ring
        have hchord0 := CurrentChordEstimate σ ω 0 le_rfl σ.len_nonneg
        rw [ht0, htL, hlen, hlenval] at hchord0
        rw [← hrestr]
        convert hchord0 using 2
      have hrsEq : R m g
          = ∑ i ∈ Finset.range m, ω.f (g.toFun (s i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i))) := by
        simp only [hR]
        apply Finset.sum_congr rfl
        intro i _
        have e1 : s i = (i:ℝ) / m * g.len := by simp [hs]
        have e2 : s (i + 1) = ((i:ℝ) + 1) / m * g.len := by
          simp only [hs]
          push_cast
          ring
        rw [e1, e2]
      have hsub : curveCurrent g ω - R m g
          = ∑ i ∈ Finset.range m,
              ((∫ t in (s i)..(s (i+1)), ω.f (g.toFun t) * deriv (ω.pi ∘ g.toFun) t)
                - (ω.f (g.toFun (s i)) * (ω.pi (g.toFun (s (i+1))) - ω.pi (g.toFun (s i))))) := by
        rw [hresol, hrsEq, ← Finset.sum_sub_distrib]
      have habs : |curveCurrent g ω - R m g|
          ≤ ∑ i ∈ Finset.range m, (ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2 := by
        rw [hsub]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum hchord
      have hcard : ∑ _i ∈ Finset.range m, (ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2
          = (m : ℝ) * ((ω.fLip : ℝ) * (ω.piLip : ℝ) * (g.len / m) ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hcard] at habs
      have hfinal : (m:ℝ) * ((ω.fLip:ℝ) * (ω.piLip:ℝ) * (g.len/m)^2/2)
          = (ω.fLip:ℝ) * (ω.piLip:ℝ) * g.len^2 / (2*m) := by
        field_simp
      rw [hfinal] at habs
      rw [abs_sub_comm]
      exact habs
    have hlim : Filter.Tendsto (fun m : ℕ => (ω.fLip:ℝ) * (ω.piLip:ℝ) * g.len^2 / (2*(m:ℝ)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun m : ℕ => (2:ℝ) * (m:ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      have h2 := (tendsto_const_nhds (x := (ω.fLip:ℝ) * (ω.piLip:ℝ) * g.len^2)).div_atTop h1
      simpa using h2
    have hbound' : ∀ᶠ m : ℕ in Filter.atTop,
        ‖R m g - curveCurrent g ω‖
          ≤ (ω.fLip:ℝ) * (ω.piLip:ℝ) * g.len^2 / (2*(m:ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      simpa [Real.norm_eq_abs] using hbound m hm
    have hz : Filter.Tendsto (fun m : ℕ => R m g - curveCurrent g ω)
        Filter.atTop (nhds 0) := squeeze_zero_norm' hbound' hlim
    have := hz.add_const (curveCurrent g ω)
    simpa using this
  exact measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 htend)
