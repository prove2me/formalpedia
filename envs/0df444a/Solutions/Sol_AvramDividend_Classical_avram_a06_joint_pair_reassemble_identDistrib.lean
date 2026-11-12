-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_joint_pair_reassemble_identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:17:17.378435+00:00
-- url     : https://prove2.me/submissions/af9390ba-b0c3-4331-bac9-c7e7a34b500f

import Mathlib.Probability.IdentDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Assemble the full waiting-time sequence from its first wait and infinite suffix. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R U : Ω → ℝ) (F G : Ω → (ℕ → ℝ))
    (hPair : IdentDistrib (fun ω => (R ω, F ω))
      (fun ω => (U ω, G ω)) P P) :
    IdentDistrib
      (fun ω (j : ℕ) => if j = 0 then R ω else F ω (j - 1))
      (fun ω (j : ℕ) => if j = 0 then U ω else G ω (j - 1)) P P := by
  let join : (ℝ × (ℕ → ℝ)) → (ℕ → ℝ) :=
    fun p j => if j = 0 then p.1 else p.2 (j - 1)
  have hjoin : Measurable join := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = 0
    · subst j
      simpa [join] using
        (measurable_fst : Measurable (fun p : ℝ × (ℕ → ℝ) => p.1))
    · simp only [join, if_neg hj]
      change Measurable (fun p : ℝ × (ℕ → ℝ) => p.2 (j - 1))
      exact ((measurable_pi_apply (j - 1)).comp
        (measurable_snd : Measurable (fun p : ℝ × (ℕ → ℝ) => p.2)))
  have hComp := ProbabilityTheory.IdentDistrib.comp hPair hjoin
  have hLeft :
      (fun ω (j : ℕ) => if j = 0 then R ω else F ω (j - 1)) =
        (fun ω => join (R ω, F ω)) := by
    funext ω j
    rfl
  have hRight :
      (fun ω (j : ℕ) => if j = 0 then U ω else G ω (j - 1)) =
        (fun ω => join (U ω, G ω)) := by
    funext ω j
    rfl
  rw [hLeft, hRight]
  exact hComp
