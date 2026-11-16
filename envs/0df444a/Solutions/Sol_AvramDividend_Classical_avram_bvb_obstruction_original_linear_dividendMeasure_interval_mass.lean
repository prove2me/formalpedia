-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_linear_dividendMeasure_interval_mass
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-15T15:15:55.123822+00:00
-- url     : https://prove2.me/submissions/0fd7a3ee-7f0e-47b6-8049-622fc0b9c33a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical Filter Topology Function
open scoped NNReal ENNReal



theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (_hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T t : ℝ≥0)
    (_ht : t ≤ T)
    (_hLinear : ∀ s : ℝ≥0, s ≤ T → D s ω = (s : ℝ)),
    dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (t : ℝ)) := by
  intro H
  let mΩ : MeasurableSpace PUnit.{1} := ⊤
  let 𝓕 : Filtration ℝ≥0 mΩ := ⟨fun _ => mΩ, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  let D : ℝ≥0 → PUnit.{1} → ℝ := fun s _ => (s : ℝ) + (if (1 : ℝ) < s then 1 else 0)
  have hstep_mono : Monotone (fun x : ℝ => (if (1 : ℝ) < x then (1 : ℝ) else 0)) := by
    intro a b hab
    by_cases ha : (1 : ℝ) < a
    · have hb : (1 : ℝ) < b := lt_of_lt_of_le ha hab
      simp [ha, hb]
    · simp only [ha, if_false]
      split_ifs <;> norm_num
  have hDmono : ∀ ω, Monotone fun s => D s ω := by
    intro ω a b hab
    have hab' : (a : ℝ) ≤ b := hab
    exact add_le_add hab' (hstep_mono hab')
  have hD : IsDividendStrategy 𝓕 D := by
    refine ⟨?_, hDmono, ?_, ?_⟩
    · intro ω; simp [D]
    · intro ω t
      have hc : ContinuousWithinAt (fun s : ℝ≥0 => (s : ℝ)) (Iic t) t :=
        NNReal.continuous_coe.continuousWithinAt
      by_cases ht : (1 : ℝ) < t
      · have hev : (fun s : ℝ≥0 => D s ω) =ᶠ[𝓝[Iic t] t] fun s => (s : ℝ) + 1 := by
          have : ∀ᶠ s : ℝ≥0 in 𝓝 t, (1 : ℝ) < s := by
            have h1 : (1 : ℝ≥0) < t := by exact_mod_cast ht
            filter_upwards [lt_mem_nhds h1] with s hs
            exact_mod_cast hs
          filter_upwards [nhdsWithin_le_nhds this] with s hs
          have hs' : (1 : ℝ≥0) < s := by exact_mod_cast hs
          simp [D, hs']
        refine ContinuousWithinAt.congr_of_eventuallyEq (hc.add continuousWithinAt_const) hev ?_
        have ht' : (1 : ℝ≥0) < t := by exact_mod_cast ht
        simp [D, ht']
      · have hev : (fun s : ℝ≥0 => D s ω) =ᶠ[𝓝[Iic t] t] fun s => (s : ℝ) + 0 := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          have : ¬ (1 : ℝ) < s := fun h => ht (lt_of_lt_of_le h (by exact_mod_cast hs))
          have : ¬ (1 : ℝ≥0) < s := fun h => this (by exact_mod_cast h)
          simp [D, this]
        refine ContinuousWithinAt.congr_of_eventuallyEq (hc.add continuousWithinAt_const) hev ?_
        have ht' : ¬ (1 : ℝ≥0) < t := fun h => ht (by exact_mod_cast h)
        simp [D, ht']
    · intro i
      exact measurable_const
  have hLin : ∀ s : ℝ≥0, s ≤ 1 → D s PUnit.unit = (s : ℝ) := by
    intro s hs
    have : ¬ (1 : ℝ≥0) < s := not_lt.2 hs
    simp [D, this]
  have key := @H PUnit.{1} mΩ 𝓕 D hD PUnit.unit 1 1 le_rfl hLin
  -- compute the left side via the Stieltjes function
  have hf : Monotone (fun x : ℝ => D x.toNNReal PUnit.unit) :=
    fun a b hab => hDmono PUnit.unit (Real.toNNReal_le_toNNReal hab)
  have hfx : ∀ x : ℝ, 0 ≤ x → D x.toNNReal PUnit.unit = x + (if (1 : ℝ) < x then 1 else 0) := by
    intro x hx
    simp [D, Real.coe_toNNReal _ hx]
  unfold dividendMeasure at key
  rw [dif_pos hf, StieltjesFunction.measure_Ioc, hf.stieltjesFunction_eq,
    hf.stieltjesFunction_eq] at key
  have hlow : (2 : ℝ) ≤ rightLim (fun x : ℝ => D x.toNNReal PUnit.unit) ((1 : ℝ≥0) : ℝ) := by
    refine ge_of_tendsto (hf.tendsto_rightLim _) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (1 : ℝ) < y := by simpa using hy
    rw [hfx y (by linarith)]
    simp [hy']
    linarith
  have hup : rightLim (fun x : ℝ => D x.toNNReal PUnit.unit) 0 ≤ 1 / 2 := by
    refine (hf.rightLim_le (show (0 : ℝ) < 1 / 2 by norm_num)).trans ?_
    rw [hfx _ (by norm_num)]
    norm_num
  have hval : (1 : ℝ) < rightLim (fun x : ℝ => D x.toNNReal PUnit.unit) ((1 : ℝ≥0) : ℝ)
      - rightLim (fun x : ℝ => D x.toNNReal PUnit.unit) 0 := by linarith
  have := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hval
  rw [key] at this
  simp at this
