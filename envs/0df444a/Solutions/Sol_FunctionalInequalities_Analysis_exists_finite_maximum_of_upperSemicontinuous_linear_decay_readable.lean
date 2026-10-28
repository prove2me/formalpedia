-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:54.082316+00:00
-- url     : https://prove2.me/submissions/947bc51b-457c-4ab0-b5ee-fe25bb98260b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Extremum

noncomputable section
/-- Actual extended-real USC objectives with a finite witness and positive
linear decay attain a finite global maximum. Bottom values elsewhere and
dimension zero are allowed; no maximizing point is supplied. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : E → EReal) (husc : UpperSemicontinuous G)
    (hnotTop : ∀ x : E, G x ≠ ⊤) (hfinite : ∃ x : E, G x ≠ ⊥)
    (a b : ℝ) (ha : 0 < a)
    (hdecay : ∀ x : E, G x ≤ ((b - a * ‖x‖ : ℝ) : EReal)) :
    ∃ x : E, G x ≠ ⊥ ∧ G x ≠ ⊤ ∧ ∀ z : E, G z ≤ G x := by
    let : ProperSpace E := FiniteDimensional.proper ℝ E
    obtain ⟨x₀, hx₀⟩ := hfinite
    let r : ℝ := (G x₀).toReal
    have hcoe : (r : EReal) = G x₀ := by
      dsimp [r]
      exact EReal.coe_toReal (hnotTop x₀) hx₀
    let R : ℝ := max ‖x₀‖ ((b - r) / a)
    have hR₁ : ‖x₀‖ ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    have hR₂ : (b - r) / a ≤ R := by
      dsimp [R]
      exact le_max_right _ _
    have hx₀K : x₀ ∈ Metric.closedBall (0 : E) R := by
      apply (Metric.mem_closedBall).2
      simpa [dist_zero_right] using hR₁
    have hK : (Metric.closedBall (0 : E) R).Nonempty :=
      ⟨x₀, hx₀K⟩
    have hKcompact : IsCompact (Metric.closedBall (0 : E) R) :=
      ProperSpace.isCompact_closedBall 0 R
    have hUSCK : UpperSemicontinuousOn G (Metric.closedBall (0 : E) R) :=
      husc.upperSemicontinuousOn _
    obtain ⟨x, hxK, hxmax⟩ :=
      UpperSemicontinuousOn.exists_isMaxOn hK hKcompact hUSCK
    have hx₀_le : G x₀ ≤ G x :=
      (isMaxOn_iff.mp hxmax) x₀ hx₀K
    refine ⟨x, ne_bot_of_le_ne_bot hx₀ hx₀_le, hnotTop x, ?_⟩
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : E) R
    · exact (isMaxOn_iff.mp hxmax) z hz
    · have hnotnorm : ¬ ‖z‖ ≤ R := by
        intro hz'
        apply hz
        apply (Metric.mem_closedBall).2
        simpa [dist_zero_right] using hz'
      have hnorm : R < ‖z‖ := lt_of_not_ge hnotnorm
      have hdiv : (b - r) / a < ‖z‖ :=
        lt_of_le_of_lt hR₂ hnorm
      have hmul : b - r < ‖z‖ * a :=
        (div_lt_iff₀ ha).mp hdiv
      have hreal : b - a * ‖z‖ < r := by
        nlinarith [hmul]
      have hstrict : G z < G x₀ := by
        calc
          G z ≤ ((b - a * ‖z‖ : ℝ) : EReal) := hdecay z
          _ < (r : EReal) := (EReal.coe_lt_coe_iff).2 hreal
          _ = G x₀ := hcoe
      exact le_of_lt (hstrict.trans_le hx₀_le)
