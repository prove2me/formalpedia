-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_near_shooting_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T08:52:36.802253+00:00
-- url     : https://prove2.me/submissions/ccca1154-a8ec-4a61-9c4d-61d23e1198d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_crossing_curve
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_quadrant_monotone
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

open BirkhoffGlobalSection Set Filter Topology

/-- A continuous map on an open interval with one-sided limits at both ends extends to a
continuous curve on `[-1,1]`. -/
lemma curve_of_limits (F : ℝ → ℝ × ℝ) (b : ℝ) (hb : 0 < b) (hF : ContinuousOn F (Ioo 0 b))
    (L R : ℝ × ℝ) (hL : Tendsto F (𝓝[>] 0) (𝓝 L)) (hR : Tendsto F (𝓝[<] b) (𝓝 R)) :
    ∃ Γ : ℝ → ℝ × ℝ, ContinuousOn Γ (Icc (-1) 1) ∧ Γ (-1) = L ∧ Γ 1 = R ∧
      ∀ l ∈ Ioo (-1 : ℝ) 1, b * (1 + l) / 2 ∈ Ioo 0 b ∧ Γ l = F (b * (1 + l) / 2) := by
  set E := extendFrom (Ioo 0 b) F
  have hE : ContinuousOn E (Icc 0 b) := continuousOn_Icc_extendFrom_Ioo hF hL hR
  refine ⟨fun l => E (b * (1 + l) / 2), ?_, ?_, ?_, ?_⟩
  · apply hE.comp (by fun_prop)
    intro l hl
    constructor <;> nlinarith [hl.1, hl.2]
  · simp only; rw [show b * (1 + -1) / 2 = 0 by ring]
    exact eq_lim_at_left_extendFrom_Ioo hb hL
  · simp only; rw [show b * (1 + 1) / 2 = b by ring]
    exact eq_lim_at_right_extendFrom_Ioo hb hR
  · intro l hl
    have hm : b * (1 + l) / 2 ∈ Ioo 0 b := by
      constructor <;> nlinarith [hl.1, hl.2]
    exact ⟨hm, extendFrom_extends hF _ hm⟩

lemma abs_sine_lt_one (v0 v1 : ℝ) (h : 0 < v0) : |v1 / Real.sqrt (v0 ^ 2 + v1 ^ 2)| < 1 := by
  have hs : |v1| < Real.sqrt (v0 ^ 2 + v1 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hpos : 0 < Real.sqrt (v0 ^ 2 + v1 ^ 2) := lt_of_le_of_lt (abs_nonneg _) hs
  rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
  exact hs

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

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ Γ : ℝ → ℝ × ℝ, ∃ α : ℝ, -1 < α ∧ α < -(Real.sqrt 2 / 2) ∧
      ContinuousOn Γ (Set.Icc (-1) 1) ∧
      Γ (-1) = (α, 0) ∧ Γ 1 = (Real.sqrt 2 / 2, 0) ∧
      (∀ s ∈ Set.Icc (-1 : ℝ) 1,
        -1 ≤ (Γ s).1 ∧ (Γ s).1 ≤ 1 ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ 1) ∧
      ∀ s ∈ Set.Ioo (-1 : ℝ) 1, |(Γ s).1| < 1 ∧ 0 < (Γ s).2 ∧
        ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 1 = 0 ∧ (x : Phase) 2 = 0 ∧ (x : Phase) 0 ≠ 0 ∧
          (∀ t ∈ Set.Ioo (-τ) 0,
            relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc (-τ) 0) ∧
          relativePosition μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ (-τ) x : LeftEnergyState μ c) : Phase)) 0 ∧
          shootingCoordinates μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) = Γ s := by
  obtain ⟨b, hb, α, hα1, hα2, S, T, hFc, hL, hR, hreal⟩ :=
    birkhoff_near_crossing_curve μ c hμ0 hμ1 hc φ hφ
  obtain ⟨Γ0, hΓ0c, hΓ0m, hΓ0p, hΓ0i⟩ := curve_of_limits _ b hb hFc _ _ hL hR
  have hr2 : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  -- data at an interior parameter
  have key : ∀ l ∈ Ioo (-1 : ℝ) 1, |(Γ0 (-l)).1| < 1 ∧ 0 < (Γ0 (-l)).2 ∧ (Γ0 (-l)).2 < 1 ∧
      ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 1 = 0 ∧ (x : Phase) 2 = 0 ∧ (x : Phase) 0 ≠ 0 ∧
          (∀ t ∈ Set.Ioo (-τ) 0,
            relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc (-τ) 0) ∧
          relativePosition μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ (-τ) x : LeftEnergyState μ c) : Phase)) 0 ∧
          shootingCoordinates μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) = Γ0 (-l) := by
    intro l hl
    have hl' : -l ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hl.2], by linarith [hl.1]⟩
    obtain ⟨hm, hval⟩ := hΓ0i (-l) hl'
    obtain ⟨h1, h2, h0, hT, hq, hend, hx⟩ := hreal _ hm
    obtain ⟨hmono, hv⟩ := birkhoff_near_quadrant_monotone μ c hμ0 hμ1 hc φ hφ _ _ hT h1 h2 h0
      hq hend
    rw [hval]
    refine ⟨?_, ?_, ?_, S _, T _, hT, h1, h2, h0, fun t ht => (hq t ht).2, hmono, hx, hv, rfl⟩
    · simp only [shootingCoordinates]; exact abs_sine_lt_one _ _ hv
    · simp only [shootingCoordinates]; linarith
    · simp only [shootingCoordinates]; exact depth_lt_one μ c hμ0 hμ1 hc _
  refine ⟨fun l => Γ0 (-l), α, hα1, hα2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hΓ0c.comp continuousOn_neg (fun l hl => ⟨by linarith [hl.2], by linarith [hl.1]⟩)
  · simpa using hΓ0p
  · simpa using hΓ0m
  · intro l hl
    rcases eq_or_lt_of_le hl.1 with h | h
    · subst h; simp only [neg_neg, hΓ0p]; refine ⟨hα1.le, by linarith [Real.sqrt_nonneg 2], le_refl _, zero_le_one⟩
    rcases eq_or_lt_of_le hl.2 with h' | h'
    · subst h'; simp only [hΓ0m]
      refine ⟨by linarith [Real.sqrt_nonneg 2], hr2, le_refl _, zero_le_one⟩
    obtain ⟨hs, hη, hη1, -⟩ := key l ⟨h, h'⟩
    have := abs_lt.1 hs
    exact ⟨this.1.le, this.2.le, hη.le, hη1.le⟩
  · intro l hl
    obtain ⟨hs, hη, -, rest⟩ := key l hl
    exact ⟨hs, hη, rest⟩
