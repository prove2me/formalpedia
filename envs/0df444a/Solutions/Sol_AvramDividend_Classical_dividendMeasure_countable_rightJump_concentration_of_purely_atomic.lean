-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration_of_purely_atomic
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-23T10:19:11.230446+00:00
-- url     : https://prove2.me/submissions/e1142a98-e169-47d3-9ec5-94d82fc0b6b5

import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

local instance : MeasurableSpace Unit := ⊤

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      {𝓕 : Filtration ℝ≥0 mΩ}
      (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
      (ω : Ω) (S : Set ℝ)
      (hS : S = {t : ℝ | 0 ≤ t ∧
        rightLimit D t.toNNReal ω ≠ D t.toNNReal ω})
      (hatomic : ∀ a b : ℝ, a ≤ b →
        dividendMeasure D ω (Ioc a b) =
          ENNReal.ofReal (rightLimit D b.toNNReal ω -
            rightLimit D a.toNNReal ω)),
      (dividendMeasure D ω).restrict S = dividendMeasure D ω) := by
  intro h
  let D : ℝ≥0 → Unit → ℝ := fun t _ => (t : ℝ)
  have hmono : Monotone (fun t : ℝ≥0 => (t : ℝ)) := by
    intro a b hab
    exact_mod_cast hab
  have hcont : Continuous (fun t : ℝ≥0 => (t : ℝ)) := by
    fun_prop
  have hD : IsDividendStrategy
      (⊤ : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit)) D := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω
      simp [D]
    · intro ω
      exact hmono
    · intro ω t
      exact hcont.continuousWithinAt
    · intro t
      exact measurable_const
  have hRight (t : ℝ≥0) : rightLimit D t () = (t : ℝ) := by
    have hrc : Function.rightLim (fun s : ℝ≥0 => (s : ℝ)) t =
        (t : ℝ) := hcont.continuousWithinAt.rightLim_eq
    have hrl : Function.rightLim (fun s : ℝ≥0 => (s : ℝ)) t =
        sInf ((fun s : ℝ≥0 => (s : ℝ)) '' Ioi t) :=
      hmono.rightLim_eq_sInf
    change (⨅ s : Ioi t, (s.1 : ℝ)) = (t : ℝ)
    calc
      (⨅ s : Ioi t, (s.1 : ℝ)) =
          sInf ((fun s : ℝ≥0 => (s : ℝ)) '' Ioi t) := by
            simp only [iInf, Set.image_eq_range]
      _ = Function.rightLim (fun s : ℝ≥0 => (s : ℝ)) t := hrl.symm
      _ = (t : ℝ) := hrc
  have hmono_real : Monotone (fun s : ℝ => (s.toNNReal : ℝ)) := by
    intro a b hab
    exact_mod_cast Real.toNNReal_mono hab
  have hcont_real : Continuous (fun s : ℝ => (s.toNNReal : ℝ)) := by
    fun_prop
  have hLim (t : ℝ) :
      Function.leftLim (hmono_real.stieltjesFunction : ℝ → ℝ) t =
        (t.toNNReal : ℝ) := by
    change Function.leftLim (Function.rightLim
      (fun s : ℝ => (s.toNNReal : ℝ))) t = _
    rw [leftLim_rightLim (hmono_real.tendsto_leftLim t)]
    exact hcont_real.continuousWithinAt.leftLim_eq
  have hMass : dividendMeasure D () (Ico (0 : ℝ) 1) = 1 := by
    unfold dividendMeasure
    rw [dif_pos hmono_real]
    rw [hmono_real.stieltjesFunction.measure_Ico, hLim 1, hLim 0]
    norm_num
  have hg (t : ℝ) :
      (hmono_real.stieltjesFunction : ℝ → ℝ) t =
        (t.toNNReal : ℝ) := by
    change Function.rightLim (fun x : ℝ => (x.toNNReal : ℝ)) t = _
    exact hcont_real.continuousWithinAt.rightLim_eq
  have hAtomic (a b : ℝ) (hab : a ≤ b) :
      dividendMeasure D () (Ioc a b) =
        ENNReal.ofReal (rightLimit D b.toNNReal () -
          rightLimit D a.toNNReal ()) := by
    unfold dividendMeasure
    rw [dif_pos hmono_real, hmono_real.stieltjesFunction.measure_Ioc,
      hg b, hg a, hRight b.toNNReal, hRight a.toNNReal]
  have hS : (∅ : Set ℝ) =
      {t : ℝ | 0 ≤ t ∧
        rightLimit D t.toNNReal () ≠ D t.toNNReal ()} := by
    ext t
    constructor
    · intro ht
      simpa using ht
    · intro ht
      exact (ht.2 (hRight t.toNNReal)).elim
  have hc : (dividendMeasure D ()).restrict (∅ : Set ℝ) =
      dividendMeasure D () :=
    h (Ω := Unit) (mΩ := (⊤ : MeasurableSpace Unit))
      (P := (0 : Measure Unit))
      (𝓕 := (⊤ : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit)))
      D hD () ∅ hS hAtomic
  have hzero : dividendMeasure D () = 0 := by
    simpa using hc.symm
  have hcontra : (0 : ENNReal) = 1 := by
    simpa [hzero] using hMass
  exact zero_ne_one hcontra
