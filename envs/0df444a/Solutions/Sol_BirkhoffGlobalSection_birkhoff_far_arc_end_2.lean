-- Prove2me | solution 2 for BirkhoffGlobalSection.birkhoff_far_arc_end
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T22:01:02.155828+00:00
-- url     : https://prove2.me/submissions/d7c661a6-e5ad-4a78-b455-56b462c8bc4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_degeneration
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_collision_strict
import Theorems.Thm_BirkhoffGlobalSection_far_crossing_coordinates_collision_extension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open BirkhoffGlobalSection Set Filter Topology Function

set_option autoImplicit false

/- This sketch reorganizes the endpoint argument in Mazecto's accepted
Prove2Me sketch e2fdab6a-c86e-45f3-8dcb-25889b3ea428. The collision chart
is isolated in a separately proved reusable theorem; trajectory degeneration
remains an imported open theorem. -/

private lemma far_start_continuous (μ c : ℝ) :
    Continuous (farShootingStart μ c) := by
  unfold farShootingStart
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals fun_prop (disch := intro r; positivity)

private lemma relative_position_formula_check (μ : ℝ) (s : Phase) :
    relativePosition μ s 0 = 2 * (s 0 ^ 2 - s 1 ^ 2) ∧
      relativePosition μ s 1 = 4 * s 0 * s 1 := by
  simp [relativePosition, leviCivitaPosition]

/-- The crossing state lies on the far diagonal, using only continuity of the flow. -/
private lemma far_crossing_diagonal (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (x : LeftEnergyState μ c) (τ : ℝ)
    (hx1 : 0 < (x : Phase) 1) (harc : IsFarShootingArc φ x τ) :
    0 < ((φ τ x : LeftEnergyState μ c) : Phase) 1 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 =
        -((φ τ x : LeftEnergyState μ c) : Phase) 1 := by
  obtain ⟨hτ, hy, hend, hcross, -⟩ := harc
  have hpos : 0 < ((φ τ x : LeftEnergyState μ c) : Phase) 1 := by
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun u => ((φ u x : LeftEnergyState μ c) : Phase) 1)
        (Icc 0 τ) := by
      exact ((continuous_apply 1).comp (continuous_subtype_val.comp
        (φ.continuous continuous_id continuous_const))).continuousOn
    have h0 : ((φ 0 x : LeftEnergyState μ c) : Phase) 1 = (x : Phase) 1 := by simp
    have hmem : (0 : ℝ) ∈ Icc ((fun u => ((φ u x : LeftEnergyState μ c) : Phase) 1) τ)
        ((fun u => ((φ u x : LeftEnergyState μ c) : Phase) 1) 0) :=
      ⟨hneg, by simp only; rw [h0]; exact hx1.le⟩
    obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' hτ.le hcont hmem
    simp only at hu0
    have hu' : u ≠ 0 := by rintro rfl; rw [h0] at hu0; linarith
    rcases eq_or_lt_of_le hu.2 with h | h
    · subst h
      have := hend
      rw [(relative_position_formula_check μ _).2, hu0] at this
      simp at this
    · have := hy u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu'), h⟩
      rw [(relative_position_formula_check μ _).2, hu0] at this
      simp at this
  refine ⟨hpos, ?_⟩
  have hy' := hend
  rw [(relative_position_formula_check μ _).2] at hy'
  have hxr := hcross
  rw [(relative_position_formula_check μ _).1] at hxr
  have h0 : ((φ τ x : LeftEnergyState μ c) : Phase) 0 < 0 := by
    by_contra h
    push Not at h
    nlinarith
  have e : (((φ τ x : LeftEnergyState μ c) : Phase) 0 -
      ((φ τ x : LeftEnergyState μ c) : Phase) 1) *
      (((φ τ x : LeftEnergyState μ c) : Phase) 0 +
      ((φ τ x : LeftEnergyState μ c) : Phase) 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 e with h | h <;> linarith


/-- A noncollision tangency has continuous shooting coordinates on a vertical side. -/
private lemma tangency_coordinates (μ : ℝ) (s : Phase)
    (hy : relativePosition μ s 1 < 0)
    (hvx : jacobiVelocity (leviCivitaToJacobi μ s) 0 = 0)
    (hvy : jacobiVelocity (leviCivitaToJacobi μ s) 1 ≠ 0) :
    ContinuousAt (shootingCoordinates μ) s ∧
      (((shootingCoordinates μ s).1 = -1 ∨ (shootingCoordinates μ s).1 = 1) ∧
        0 < (shootingCoordinates μ s).2) := by
  have hy' : 4 * s 0 * s 1 < 0 := by
    simpa [relativePosition, leviCivitaPosition] using hy
  have hs0 : s 0 ≠ 0 := by
    intro h
    simp [h] at hy'
  have hP : s 0 ^ 2 + s 1 ^ 2 ≠ 0 := by positivity
  have hxcont : ContinuousAt (fun z : Phase => jacobiVelocity (leviCivitaToJacobi μ z) 0) s := by
    simp only [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum,
      zNormSq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    fun_prop (disch := assumption)
  have hycont : ContinuousAt (fun z : Phase => jacobiVelocity (leviCivitaToJacobi μ z) 1) s := by
    simp only [jacobiVelocity, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum,
      zNormSq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    fun_prop (disch := assumption)
  have hden : Real.sqrt (jacobiVelocity (leviCivitaToJacobi μ s) 0 ^ 2 +
      jacobiVelocity (leviCivitaToJacobi μ s) 1 ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.2 _).ne'
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hvy)
  constructor
  · unfold shootingCoordinates
    apply ContinuousAt.prodMk
    · exact hycont.div ((hxcont.pow 2).add (hycont.pow 2)).sqrt hden
    · unfold relativePosition leviCivitaPosition
      fun_prop
  · constructor
    · dsimp only [shootingCoordinates]
      rw [hvx, zero_pow (by decide), zero_add, Real.sqrt_sq_eq_abs]
      rcases lt_or_gt_of_ne hvy with h | h
      · left
        rw [abs_of_neg h]
        field_simp
      · right
        rw [abs_of_pos h, div_self hvy]
    · exact neg_pos.mpr hy

/-- Joint continuity transports crossing-time convergence through any coordinate
formula continuous at the limiting state and agreeing at actual crossings. -/
private lemma crossing_coordinates_converge (μ c : ℝ)
    (φ : Flow ℝ (LeftEnergyState μ c)) (b : ℝ) (hb : 0 < b)
    (xb : LeftEnergyState μ c) (hxb : (xb : Phase) = farShootingStart μ c b) (T : ℝ)
    (hconv : ∀ η > 0, ∃ δ > 0, ∀ r ∈ Ioo (b - δ) b,
      ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → |τ - T| < η)
    (H : Phase → ℝ × ℝ) (hH : ContinuousAt H ((φ T xb : LeftEnergyState μ c) : Phase))
    (hagrees : ∀ r, 0 < r → ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
        shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase) =
          H ((φ τ x : LeftEnergyState μ c) : Phase)) :
    ∀ η > 0, ∃ δ > 0, ∀ r ∈ Ioo (b - δ) b,
      ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
          dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase))
            (H ((φ T xb : LeftEnergyState μ c) : Phase)) < η := by
  intro η hη
  let F : ℝ × LeftEnergyState μ c → Phase := fun p => ((φ p.1 p.2 : LeftEnergyState μ c) : Phase)
  have hFc : Continuous F := continuous_subtype_val.comp φ.cont'
  have hHF : ContinuousAt (H ∘ F) (T, xb) :=
    ContinuousAt.comp (g := H) (f := F) (x := (T, xb)) hH hFc.continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hHF η hη
  obtain ⟨δ₁, hδ₁, hstart⟩ := Metric.continuousAt_iff.1
    ((far_start_continuous μ c).continuousAt : ContinuousAt (farShootingStart μ c) b) ε hε
  obtain ⟨δ₂, hδ₂, htime⟩ := hconv ε hε
  refine ⟨min b (min δ₁ δ₂), lt_min hb (lt_min hδ₁ hδ₂), ?_⟩
  intro r hr x τ hx harc
  have hr0 : 0 < r := by linarith [hr.1, min_le_left b (min δ₁ δ₂)]
  have hrδ₁ : dist r b < δ₁ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hr.2])]
    linarith [hr.1, min_le_left δ₁ δ₂, min_le_right b (min δ₁ δ₂)]
  have hrδ₂ : r ∈ Ioo (b - δ₂) b :=
    ⟨by linarith [hr.1, min_le_right δ₁ δ₂, min_le_right b (min δ₁ δ₂)], hr.2⟩
  rw [hagrees r hr0 x τ hx harc]
  apply @hball (τ, x)
  rw [Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [Real.dist_eq]
    exact htime r hrδ₂ x τ hx harc
  · rw [Subtype.dist_eq, hx, hxb]
    exact hstart hrδ₁

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c b ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)) :
    ∃ E : ℝ × ℝ,
      (((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
      ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
          dist (shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase)) E < η := by
  obtain ⟨xb, hxb, T, hT, hy, hvx, _, hcase, hconv⟩ :=
    birkhoff_far_arc_degeneration μ c hμ0 hμ1 hc φ hφ b hb hgood hbad
  have hb1 : (xb : Phase) 1 = b := by rw [hxb]; simp [farShootingStart]
  let s₀ : Phase := ((φ T xb : LeftEnergyState μ c) : Phase)
  rcases hcase with ⟨hc0, hc1⟩ | ⟨hyT, hvx0, hvy⟩
  · obtain ⟨hw0, hw1⟩ := birkhoff_far_collision_strict μ c hμ0 hμ1 hc φ hφ
      xb T hT (by rw [hb1]; exact hb) hy hvx hc0 hc1
    obtain ⟨H, hH, hH2, hH1, hagrees⟩ :=
      far_crossing_coordinates_collision_extension μ s₀ hc0 hc1 hw0 hw1
    refine ⟨H s₀, Or.inr ⟨hH2, hH1⟩, ?_⟩
    apply crossing_coordinates_converge μ c φ b hb xb hxb T hconv H hH
    intro r hr x τ hx harc
    have hx1 : 0 < (x : Phase) 1 := by rw [hx]; simpa [farShootingStart] using hr
    obtain ⟨hpos, hdiag⟩ := far_crossing_diagonal μ c φ x τ hx1 harc
    exact hagrees _ hpos hdiag
  · obtain ⟨hcont, hside⟩ := tangency_coordinates μ s₀ hyT hvx0 hvy
    exact ⟨shootingCoordinates μ s₀, Or.inl hside,
      crossing_coordinates_converge μ c φ b hb xb hxb T hconv
        (shootingCoordinates μ) hcont (fun _ _ _ _ _ _ => rfl)⟩
