-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_shooting_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T08:52:37.75157+00:00
-- url     : https://prove2.me/submissions/97470b81-84c1-4e29-9a15-e26b369a0ab7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_crossing_curve
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
    ∃ Γ : ℝ → ℝ × ℝ,
      ContinuousOn Γ (Set.Icc (-1) 1) ∧
      Γ (-1) = (-(Real.sqrt 2 / 2), 0) ∧
      ((((Γ 1).1 = -1 ∨ (Γ 1).1 = 1) ∧ 0 < (Γ 1).2) ∨
        ((Γ 1).2 = 0 ∧ Real.sqrt 2 / 2 < (Γ 1).1)) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1,
        -1 ≤ (Γ t).1 ∧ (Γ t).1 ≤ 1 ∧ 0 ≤ (Γ t).2 ∧ (Γ t).2 ≤ 1) ∧
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < (Γ t).2 ∧
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
          shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase) = Γ t := by
  obtain ⟨b, hb, E, hE, S, T, hFc, hL, hR, hreal⟩ :=
    birkhoff_far_crossing_curve μ c hμ0 hμ1 hc φ hφ
  obtain ⟨Γ0, hΓ0c, hΓ0m, hΓ0p, hΓ0i⟩ := curve_of_limits _ b hb hFc _ _ hL hR
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
  have hEC : E ∈ C := by
    have hcl : IsClosed C := isClosed_Icc.prod isClosed_Icc
    exact hcl.mem_of_tendsto hR (Filter.mem_of_superset (Ioo_mem_nhdsLT hb) hval)
  refine ⟨Γ0, hΓ0c, hΓ0m, by rw [hΓ0p]; exact hE, ?_, ?_⟩
  · intro l hl
    rcases eq_or_lt_of_le hl.1 with h | h
    · subst h; rw [hΓ0m]
      exact ⟨by linarith [hr2], by linarith [Real.sqrt_nonneg 2], le_refl _, zero_le_one⟩
    rcases eq_or_lt_of_le hl.2 with h' | h'
    · subst h'; rw [hΓ0p]; exact ⟨hEC.1.1, hEC.1.2, hEC.2.1, hEC.2.2⟩
    obtain ⟨hm, hv⟩ := hΓ0i l ⟨h, h'⟩
    have := hval _ hm
    rw [← hv] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  · intro l hl
    obtain ⟨hm, hv⟩ := hΓ0i l hl
    obtain ⟨h0, h3, h1, hT, hlow, hend, hmono, hx, hvel⟩ := hreal _ hm
    rw [hv]
    refine ⟨?_, S _, T _, hT, h0, h3, h1, hlow, hmono, hx, hvel, rfl⟩
    simp only [shootingCoordinates]; linarith
