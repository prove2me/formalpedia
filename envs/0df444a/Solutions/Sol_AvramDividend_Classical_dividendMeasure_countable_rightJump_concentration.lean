-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-23T10:11:54.642341+00:00
-- url     : https://prove2.me/submissions/cd889e96-e7b2-455b-b5f6-d61b7a1423cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Deterministic linear dividends are adapted to every filtration. -/
private theorem linearDividendStrategy {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    IsDividendStrategy 𝓕 (fun t (_ : Ω) => (t : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    simp
  · intro ω a b hab
    exact_mod_cast hab
  · intro ω t
    exact NNReal.continuous_coe.continuousWithinAt
  · intro t
    exact measurable_const

/-- A continuous linear dividend strategy has no right jumps. -/
private theorem linearDividend_rightLimit {Ω : Type*} (ω : Ω) (t : ℝ≥0) :
    rightLimit (fun s (_ : Ω) => (s : ℝ)) t ω = (t : ℝ) := by
  have hm : Monotone (fun s : ℝ≥0 => (s : ℝ)) := by
    intro a b hab
    exact_mod_cast hab
  have hRange : (fun s : ℝ≥0 => (s : ℝ)) '' Ioi t =
      Set.range (fun u : Ioi t => (u.1 : ℝ)) := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    · rintro ⟨⟨s, hs⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hLim : Function.rightLim (fun s : ℝ≥0 => (s : ℝ)) t =
      rightLimit (fun s (_ : Ω) => (s : ℝ)) t ω := by
    rw [hm.rightLim_eq_sInf, hRange, sInf_range]
    rfl
  have hCont : ContinuousWithinAt (fun s : ℝ≥0 => (s : ℝ)) (Ici t) t :=
    NNReal.continuous_coe.continuousWithinAt
  exact hLim.symm.trans hCont.rightLim_eq

/-- On [0,1), the linear dividend Stieltjes measure has mass one. -/
private theorem linearDividend_mass {Ω : Type*} [mΩ : MeasurableSpace Ω] (ω : Ω) :
    dividendMeasure (fun t (_ : Ω) => (t : ℝ)) ω (Ico (0 : ℝ) 1) = 1 := by
  let f : ℝ → ℝ := fun x => max x 0
  have hf : (fun x : ℝ => ((x.toNNReal : ℝ))) = f := by
    funext x
    simp [f, Real.coe_toNNReal]
  have hmon : Monotone (fun x : ℝ => (x.toNNReal : ℝ)) := by
    intro a b hab
    exact_mod_cast Real.toNNReal_mono hab
  have hcont : Continuous f := continuous_id.max continuous_const
  have hco : (fun x : ℝ => (hmon.stieltjesFunction x : ℝ)) = f := by
    funext x
    rw [Monotone.stieltjesFunction_eq hmon x]
    exact (congrArg (fun g : ℝ → ℝ => Function.rightLim g x) hf).trans
      hcont.continuousWithinAt.rightLim_eq
  have hleft (x : ℝ) : Function.leftLim f x = f x :=
    hcont.continuousWithinAt.leftLim_eq
  unfold dividendMeasure
  simp only [dif_pos hmon]
  rw [StieltjesFunction.measure_Ico]
  change ENNReal.ofReal
    (Function.leftLim (fun x : ℝ => (hmon.stieltjesFunction x : ℝ)) 1 -
     Function.leftLim (fun x : ℝ => (hmon.stieltjesFunction x : ℝ)) 0) = 1
  rw [hco, hleft 1, hleft 0]
  norm_num [f]

/-- A concrete continuous dividend strategy disproves jump concentration. -/
theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ}
        (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
        (ω : Ω) (S : Set ℝ)
        (hS : S =
          {t : ℝ | 0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω}),
        (dividendMeasure D ω).restrict S = dividendMeasure D ω) := by
  classical
  intro hall
  letI : MeasurableSpace Unit := ⊤
  let 𝓕 : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit) := ⊤
  let ω : Unit := ()
  let D : ℝ≥0 → Unit → ℝ := fun t _ => (t : ℝ)
  have hS : (∅ : Set ℝ) =
      {t : ℝ | 0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} := by
    ext t
    constructor
    · intro ht
      simpa using ht
    · intro ht
      exact (ht.2 (by simpa [D] using linearDividend_rightLimit ω t.toNNReal)).elim
  have hEq := hall (Ω := Unit)
    (P := (0 : Measure Unit)) (𝓕 := 𝓕)
    D (linearDividendStrategy 𝓕) ω ∅ hS
  have hImpossible : (0 : ENNReal) = 1 := by
    have hInterval :=
      congrArg (fun μ : Measure ℝ => μ (Ico (0 : ℝ) 1)) hEq
    simpa [D, linearDividend_mass ω] using hInterval
  exact zero_ne_one hImpossible
