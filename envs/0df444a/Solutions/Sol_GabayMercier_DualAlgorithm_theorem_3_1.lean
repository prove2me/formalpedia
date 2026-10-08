-- Prove2me | solution 1 for GabayMercier.DualAlgorithm.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:25:59.376595+00:00
-- url     : https://prove2.me/submissions/d82ad40b-879a-4cfe-9197-9bccf8317c4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model
import Theorems.Thm_GabayMercier_DualAlgorithm_theorem_2_1_exists
import Theorems.Thm_GabayMercier_DualAlgorithm_theorem_2_1_saddle_props
import Theorems.Thm_GabayMercier_DualAlgorithm_proposition_2_1
import Theorems.Thm_GabayMercier_DualAlgorithm_P_lam_tendsto_and_v_tendsto
import Theorems.Thm_GabayMercier_DualAlgorithm_y_tendsto
import Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_20

open Filter Topology InertialFB.IFB

set_option autoImplicit false

namespace GMd85a

open GabayMercier.DualAlgorithm


/-- Glue for theorem_3_1: given the facts supplied by the sibling theorems for one saddle point
`(vs', ys', ls')` (saddle_props, uniqueness, P_lam_tendsto_and_v_tendsto, y_tendsto, eq_3_20),
the parent conclusion follows. -/
theorem glue {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : V →L[ℝ] Y) (γ r ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (v : ℕ → V) (y lam : ℕ → Y) (vs : V) (ys ls : Y) (hys : ys = A vs)
    (hP : Tendsto (fun n => projRange A (lam n - ls)) atTop (𝓝 0))
    (hv : Tendsto v atTop (𝓝 vs)) (hy : Tendsto y atTop (𝓝 ys))
    (h320 : ∀ N : ℕ,
      γ * ∑ n ∈ Finset.range (N + 1), ‖y (n + 1) - ys‖ ^ 2
        + (r - ρ / 2) * ∑ n ∈ Finset.range (N + 1),
            ‖(ContinuousLinearMap.id ℝ Y - projRange A) (y (n + 1) - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam (N + 1) - ls)‖ ^ 2
      ≤ r / 2 * ‖projRange A (y 0 - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam 0 - ls)‖ ^ 2) :
    Tendsto v atTop (𝓝 vs) ∧ Tendsto y atTop (𝓝 (A vs)) ∧
      Bornology.IsBounded (Set.range lam) := by
  refine ⟨hv, hys ▸ hy, ?_⟩
  set Q := ContinuousLinearMap.id ℝ Y - projRange A with hQ
  set R := r / 2 * ‖projRange A (y 0 - ys)‖ ^ 2
    + 1 / (2 * ρ) * ‖Q (lam 0 - ls)‖ ^ 2 with hR
  have hr0 : 0 < r := by linarith
  have hR0 : 0 ≤ R := by positivity
  -- bound on the (I - P) part
  have hQb : ∀ n, ‖Q (lam n - ls)‖ ≤ ‖Q (lam 0 - ls)‖ + 1 + 2 * ρ * R := by
    intro n
    rcases n with _ | N
    · linarith [norm_nonneg (Q (lam 0 - ls)), (mul_nonneg (by positivity) hR0 : (0:ℝ) ≤ 2 * ρ * R)]
    · have h := h320 N
      have s1 : 0 ≤ γ * ∑ n ∈ Finset.range (N + 1), ‖y (n + 1) - ys‖ ^ 2 :=
        mul_nonneg hγ.le (Finset.sum_nonneg (fun _ _ => by positivity))
      have s2 : 0 ≤ (r - ρ / 2) * ∑ n ∈ Finset.range (N + 1), ‖Q (y (n + 1) - ys)‖ ^ 2 :=
        mul_nonneg (by linarith) (Finset.sum_nonneg (fun _ _ => by positivity))
      have h3 : 1 / (2 * ρ) * ‖Q (lam (N + 1) - ls)‖ ^ 2 ≤ R := by linarith
      have h4 : ‖Q (lam (N + 1) - ls)‖ ^ 2 ≤ 2 * ρ * R := by
        have hpos : 0 < 2 * ρ := by positivity
        have := mul_le_mul_of_nonneg_left h3 hpos.le
        rwa [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
      nlinarith [norm_nonneg (Q (lam 0 - ls)), norm_nonneg (Q (lam (N + 1) - ls)),
        sq_nonneg (‖Q (lam (N + 1) - ls)‖ - 1)]
  -- bound on the P part
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖projRange A (lam n - ls)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hP).exists_norm_le
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖ls‖ + C + (‖Q (lam 0 - ls)‖ + 1 + 2 * ρ * R), ?_⟩
  rintro _ ⟨n, rfl⟩
  have hsplit : lam n = ls + projRange A (lam n - ls) + Q (lam n - ls) := by
    simp [hQ]
  rw [hsplit]
  calc ‖ls + projRange A (lam n - ls) + Q (lam n - ls)‖
      ≤ ‖ls + projRange A (lam n - ls)‖ + ‖Q (lam n - ls)‖ := norm_add_le _ _
    _ ≤ ‖ls‖ + ‖projRange A (lam n - ls)‖ + ‖Q (lam n - ls)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith [hC n, hQb n]

end GMd85a

open GabayMercier.DualAlgorithm in
theorem solution {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hq : Qualification A f₂) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (hvs : IsSolution A f₁ f₂ b vs) :
    Tendsto v atTop (𝓝 vs) ∧ Tendsto y atTop (𝓝 (A vs)) ∧
      Bornology.IsBounded (Set.range lam) := by
  obtain ⟨vs', ys', ls', hsp⟩ := theorem_2_1_exists A f₁ f₁' f₂ b γ α h hq
  obtain ⟨hsol', hys', -, -⟩ := theorem_2_1_saddle_props A f₁ f₂ b h.f₂_proper vs' ys' ls' hsp
  have hdom : ∃ v₀ : V, f₂ (A v₀) ≠ ⊤ := by
    refine ⟨vs, fun htop => hvs.1 ?_⟩
    simp only [objective, htop]
    exact EReal.coe_add_top _
  have heq : vs' = vs := (proposition_2_1 A f₁ f₁' f₂ b γ α h hdom).unique hsol' hvs
  subst heq
  obtain ⟨hP, hv⟩ := P_lam_tendsto_and_v_tendsto A f₁ f₁' f₂ b γ α h r ρ hr hρ v y lam hrun
    vs' ys' ls' hsp hρr
  have hy := y_tendsto A f₁ f₁' f₂ b γ α h r ρ hr hρ v y lam hrun vs' ys' ls' hsp hρr.le
  have h320 := eq_3_20 A f₁ f₁' f₂ b γ α h r ρ hr hρ v y lam hrun vs' ys' ls' hsp
  exact GMd85a.glue A γ r ρ h.γ_pos hρ hρr v y lam vs' ys' ls' hys' hP hv hy h320
