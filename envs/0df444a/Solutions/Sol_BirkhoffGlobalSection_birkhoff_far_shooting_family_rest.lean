-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_shooting_family_rest
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T19:03:49.728457+00:00
-- url     : https://prove2.me/submissions/364d6933-af90-4da7-90d9-145c9d004952

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_crossing_curve_rest
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Definitions.Def_BirkhoffShootingArcs
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.ExtendFrom

open BirkhoffGlobalSection Set Filter Topology Function

-- ===== Solutions.Abstract =====
section Abstract

variable {X : Type*} [TopologicalSpace X]

-- ===== Solutions.CM29 =====
/-! Birkhoff's identity (59): the angular momentum about the primary along far arcs. -/

-- ===== Solutions.CM37 =====
/-- A continuous map on an open interval with a limit at the left end extends to a curve on
`[-1,1)`, and to `[-1,1]` when it also has a limit at the right end. -/
lemma curve_of_left_limit (F : ℝ → ℝ × ℝ) (b : ℝ) (hb : 0 < b) (hF : ContinuousOn F (Ioo 0 b))
    (L : ℝ × ℝ) (hL : Tendsto F (𝓝[>] 0) (𝓝 L)) :
    ∃ Γ : ℝ → ℝ × ℝ, ContinuousOn Γ (Ico (-1) 1) ∧ Γ (-1) = L ∧
      (∀ l ∈ Ioo (-1 : ℝ) 1, b * (1 + l) / 2 ∈ Ioo 0 b ∧ Γ l = F (b * (1 + l) / 2)) ∧
      (∀ R, Tendsto F (𝓝[<] b) (𝓝 R) → ContinuousOn Γ (Icc (-1) 1) ∧ Γ 1 = R) := by
  set E := extendFrom (Ioo 0 b) F
  refine ⟨fun l => E (b * (1 + l) / 2), ?_, ?_, ?_, ?_⟩
  · apply (continuousOn_Ico_extendFrom_Ioo hF hL).comp (by fun_prop)
    intro l hl
    constructor <;> nlinarith [hl.1, hl.2]
  · simp only; rw [show b * (1 + -1) / 2 = 0 by ring]
    exact eq_lim_at_left_extendFrom_Ioo hb hL
  · intro l hl
    have hm : b * (1 + l) / 2 ∈ Ioo 0 b := by
      constructor <;> nlinarith [hl.1, hl.2]
    exact ⟨hm, extendFrom_extends hF _ hm⟩
  · intro R hR
    refine ⟨?_, ?_⟩
    · apply (continuousOn_Icc_extendFrom_Ioo hF hL hR).comp (by fun_prop)
      intro l hl
      constructor <;> nlinarith [hl.1, hl.2]
    · simp only; rw [show b * (1 + 1) / 2 = b by ring]
      exact eq_lim_at_right_extendFrom_Ioo hb hR

lemma abs_sine_le_one (v0 v1 : ℝ) : |v1 / Real.sqrt (v0 ^ 2 + v1 ^ 2)| ≤ 1 := by
  rcases eq_or_ne (v0 ^ 2 + v1 ^ 2) 0 with h | h
  · rw [h]; simp
  have hpos : 0 < Real.sqrt (v0 ^ 2 + v1 ^ 2) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) (Ne.symm h))
  have hs : |v1| ≤ Real.sqrt (v0 ^ 2 + v1 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  exact hs

/-- depth below the axis is less than one on the selected component -/
lemma depth_lt_one (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (s : LeftEnergyState μ c) : -relativePosition μ (s : Phase) 1 < 1 := by
  obtain ⟨ρ, hρ, hbound⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
  have h := hbound s s.2
  have e : relativePosition μ (s : Phase) 1 = leviCivitaPosition μ (s : Phase) 1 := by
    simp [relativePosition]
  rw [e]
  nlinarith [sq_nonneg (leviCivitaPosition μ (s : Phase) 0 + μ),
    sq_nonneg (leviCivitaPosition μ (s : Phase) 1 + 1)]

theorem far_shooting_family_rest (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ Γ : ℝ → ℝ × ℝ,
      Γ (-1) = (-(Real.sqrt 2 / 2), 0) ∧
      (∀ t ∈ Set.Ico (-1 : ℝ) 1,
        -1 ≤ (Γ t).1 ∧ (Γ t).1 ≤ 1 ∧ 0 ≤ (Γ t).2 ∧ (Γ t).2 ≤ 1) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < (Γ t).2 ∧
        ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
          (∀ u ∈ Set.Ioo 0 τ,
            relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc 0 τ) ∧
          relativePosition μ ((φ τ x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ τ x : LeftEnergyState μ c) : Phase)) 0 ∧
          shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase) = Γ t) ∧
      ((ContinuousOn Γ (Set.Icc (-1) 1) ∧
        ((((Γ 1).1 = -1 ∨ (Γ 1).1 = 1) ∧ 0 < (Γ 1).2) ∨
          ((Γ 1).2 = 0 ∧ Real.sqrt 2 / 2 < (Γ 1).1)) ∧
        -1 ≤ (Γ 1).1 ∧ (Γ 1).1 ≤ 1 ∧ 0 ≤ (Γ 1).2 ∧ (Γ 1).2 ≤ 1) ∨
       (ContinuousOn Γ (Set.Ico (-1) 1) ∧ ∃ d : ℝ, 0 < d ∧
        (∀ s : LeftEnergyState μ c, relativePosition μ (s : Phase) 0 = 0 →
          relativePosition μ (s : Phase) 1 < 0 →
          0 < jacobiVelocity (leviCivitaToJacobi μ (s : Phase)) 0 →
          -relativePosition μ (s : Phase) 1 < d) ∧
        Filter.Tendsto (fun t : ℝ => (Γ t).2) (nhdsWithin 1 (Set.Iio 1)) (nhds d))) := by
  obtain ⟨b, hb, E, S, T, hFc, hL, hEnd, hreal⟩ :=
    birkhoff_far_crossing_curve_rest μ c hμ0 hμ1 hc φ hφ
  obtain ⟨Γ0, hΓ0c, hΓ0m, hΓ0i, hΓ0R⟩ := curve_of_left_limit _ b hb hFc _ hL
  have hr2 : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  set C : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hC
  have hval : ∀ r ∈ Ioo 0 b,
      shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) ∈ C := by
    intro r hr
    obtain ⟨-, -, -, -, -, hend, -, -, -⟩ := hreal r hr
    have h1 := abs_le.1 (abs_sine_le_one
      (jacobiVelocity (leviCivitaToJacobi μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) 0)
      (jacobiVelocity (leviCivitaToJacobi μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) 1))
    have h2 := depth_lt_one μ c hμ0 hμ1 hc (φ (T r) (S r))
    exact ⟨⟨h1.1, h1.2⟩, ⟨by simp only [shootingCoordinates]; linarith,
      by simp only [shootingCoordinates]; linarith⟩⟩
  refine ⟨Γ0, hΓ0m, ?_, ?_, ?_⟩
  · intro l hl
    rcases eq_or_lt_of_le hl.1 with h | h
    · subst h; rw [hΓ0m]
      exact ⟨by linarith [hr2], by linarith [Real.sqrt_nonneg 2], le_refl _, zero_le_one⟩
    obtain ⟨hm, hv⟩ := hΓ0i l ⟨h, hl.2⟩
    have := hval _ hm
    rw [← hv] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  · intro l hl
    obtain ⟨hm, hv⟩ := hΓ0i l hl
    obtain ⟨h0, h3, h1, hT, hlow, hend, hmono, hx, hvel⟩ := hreal _ hm
    rw [hv]
    refine ⟨?_, S _, T _, hT, h0, h3, h1, hlow, hmono, hx, hvel, rfl⟩
    simp only [shootingCoordinates]; linarith
  rcases hEnd with ⟨hE, hR⟩ | ⟨hE2, hEb, hR⟩
  · obtain ⟨hc', hΓ1⟩ := hΓ0R E hR
    have hEC : E ∈ C := by
      have hcl : IsClosed C := isClosed_Icc.prod isClosed_Icc
      exact hcl.mem_of_tendsto hR (Filter.mem_of_superset (Ioo_mem_nhdsLT hb) hval)
    refine Or.inl ⟨hc', by rw [hΓ1]; exact hE, ?_⟩
    rw [hΓ1]; exact ⟨hEC.1.1, hEC.1.2, hEC.2.1, hEC.2.2⟩
  · refine Or.inr ⟨hΓ0c, E.2, hE2, hEb, ?_⟩
    have hmap : Tendsto (fun l : ℝ => b * (1 + l) / 2) (𝓝[<] 1) (𝓝[<] b) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun l : ℝ => b * (1 + l) / 2) (𝓝 1) (𝓝 (b * (1 + 1) / 2)) :=
          (by fun_prop : Continuous fun l : ℝ => b * (1 + l) / 2).tendsto 1
        rw [show b * (1 + 1) / 2 = b by ring] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with l hl
        simp only [mem_Iio] at hl ⊢; nlinarith
    have hcomp := hR.comp hmap
    apply hcomp.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with l hl
    simp only [Function.comp]
    rw [(hΓ0i l hl).2]

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ Γ : ℝ → ℝ × ℝ,
      Γ (-1) = (-(Real.sqrt 2 / 2), 0) ∧
      (∀ t ∈ Set.Ico (-1 : ℝ) 1,
        -1 ≤ (Γ t).1 ∧ (Γ t).1 ≤ 1 ∧ 0 ≤ (Γ t).2 ∧ (Γ t).2 ≤ 1) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < (Γ t).2 ∧
        ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
          (∀ u ∈ Set.Ioo 0 τ,
            relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc 0 τ) ∧
          relativePosition μ ((φ τ x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ τ x : LeftEnergyState μ c) : Phase)) 0 ∧
          shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase) = Γ t) ∧
      ((ContinuousOn Γ (Set.Icc (-1) 1) ∧
        ((((Γ 1).1 = -1 ∨ (Γ 1).1 = 1) ∧ 0 < (Γ 1).2) ∨
          ((Γ 1).2 = 0 ∧ Real.sqrt 2 / 2 < (Γ 1).1)) ∧
        -1 ≤ (Γ 1).1 ∧ (Γ 1).1 ≤ 1 ∧ 0 ≤ (Γ 1).2 ∧ (Γ 1).2 ≤ 1) ∨
       (ContinuousOn Γ (Set.Ico (-1) 1) ∧ ∃ d : ℝ, 0 < d ∧
        (∀ s : LeftEnergyState μ c, relativePosition μ (s : Phase) 0 = 0 →
          relativePosition μ (s : Phase) 1 < 0 →
          0 < jacobiVelocity (leviCivitaToJacobi μ (s : Phase)) 0 →
          -relativePosition μ (s : Phase) 1 < d) ∧
        Filter.Tendsto (fun t : ℝ => (Γ t).2) (nhdsWithin 1 (Set.Iio 1)) (nhds d))) :=
  far_shooting_family_rest μ c hμ0 hμ1 hc φ hφ
