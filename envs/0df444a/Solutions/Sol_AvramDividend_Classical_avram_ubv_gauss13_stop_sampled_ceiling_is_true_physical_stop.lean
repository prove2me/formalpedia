-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_sampled_ceiling_is_true_physical_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:29:58.164375+00:00
-- url     : https://prove2.me/submissions/6b52e9cc-2d86-4f1a-bc8a-f962425360c0

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

/-- A genuine sampled stopping index yields a genuine physical-time stopping
clock for the original right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hK : IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ))) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (e (K ω) : WithTop ℝ≥0)) := by
  classical
  have hFiber (i : ℕ) :
      MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω = i} := by
    have hEq : MeasurableSet[𝓖 i]
        {ω : Ω | (K ω : WithTop ℕ) = (i : WithTop ℕ)} :=
      hK.measurableSet_eq_le (le_refl i)
    have hFil : 𝓖 i = 𝓕.rightCont (e i) := by
      rw [h𝓖]
    rw [hFil] at hEq
    simpa using hEq
  intro t
  simp only [WithTop.coe_le_coe]
  have hEvent : {ω : Ω | e (K ω) ≤ t} =
      ⋃ i : ℕ, if e i ≤ t then {ω : Ω | K ω = i} else ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hw
      refine ⟨K ω, ?_⟩
      simp [hw]
    · rintro ⟨i, hi⟩
      by_cases hle : e i ≤ t
      · have hki : K ω = i := by simpa [hle] using hi
        simpa [hki] using hle
      · simp [hle] at hi
  rw [hEvent]
  apply MeasurableSet.iUnion
  intro i
  by_cases hle : e i ≤ t
  · have hMeas : MeasurableSet[𝓕.rightCont t]
        {ω : Ω | K ω = i} :=
      (𝓕.rightCont.mono hle {ω : Ω | K ω = i}) (hFiber i)
    simpa [hle] using hMeas
  · simp [hle]
