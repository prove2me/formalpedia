-- Prove2me | solution 1 for FiniteEnergyPlane.cylJ_iteratedFDeriv_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T22:39:20.559601+00:00
-- url     : https://prove2.me/submissions/e26b2ded-16be-498c-bd56-19f795042930

import Definitions.Def_FiniteEnergyPlane_Tube
import Mathlib
import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_FiniteEnergyPlane_TubeFamily





/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

/-!
# Q-N, layer 1: weights, `L⁴` from exponential decay, and the `+∞` bound on `cylJ` (local)

* `IsSlopeWeight.eq_right` / `eq_left`: a slope weight is affine on `[1, ∞)` and `(-∞, -1]`.
* `memLp_four_of_exp_bound`: a measurable `f` with `‖f (s, t)‖ ≤ C e^{-κ|s|}` lies in `L⁴(cylMeasure)`.
* `cylJ_iteratedFDeriv_bdd_aux`: under `IsStdTubeStructure`, every derivative of
  `(s, t, w) ↦ cylJ Jbar s t w` is bounded on `[s₁, ∞) × ℝ × closedBall 0 (ρ/2)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Bounded derivatives of `cylJ` at `+∞` -/

/-- Every derivative of `Jinf` is bounded on `ℝ × closedBall 0 (ρ/2)`. -/
lemma jinf_iteratedFDeriv_bdd (ρ : ℝ) (hρ : 0 < ρ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jinf (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hper : ∀ (t : ℝ) (w : ℂ), Jinf (t + 1, w) = Jinf (t, w)) (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2), ‖iteratedFDeriv ℝ m Jinf (t, w)‖ ≤ C := by
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ) := (isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ)))
  have hcont : ContinuousOn (iteratedFDeriv ℝ m Jinf) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    (hJ.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top)
      hU.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen m hU hx).symm)
  have hsub : Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) (ρ / 2) ⊆ Set.univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (subset_univ _) (closedBall_subset_ball (by linarith))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) (ρ / 2))).exists_bound_of_continuousOn
    (hcont.mono hsub)
  refine ⟨C, fun t w hw => ?_⟩
  have hfun : (fun z : ℝ × ℂ => Jinf (z + ((1 : ℝ), (0 : ℂ)))) = Jinf := by
    funext z; obtain ⟨t, w⟩ := z; simp [hper]
  have hP : Function.Periodic (fun t : ℝ => ‖iteratedFDeriv ℝ m Jinf (t, w)‖) 1 := by
    intro t
    have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Jinf) m ((1 : ℝ), (0 : ℂ)) (t, w)
    rw [hfun] at this
    simp only [Prod.mk_add_mk, add_zero] at this
    exact congrArg norm this.symm
  obtain ⟨y, hy, hy'⟩ := hP.exists_mem_Ico₀ one_pos t
  rw [hy']
  exact hC (y, w) ⟨Ico_subset_Icc_self hy, hw⟩

/-- **`+∞` base bound.** Under `IsStdTubeStructure`, every derivative of
`(s, t, w) ↦ cylJ Jbar s t w` is bounded on `[s₁, ∞) × ℝ × closedBall 0 (ρ/2)`. -/
theorem cylJ_iteratedFDeriv_bdd_aux (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (m : ℕ) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2) (s, t, w)‖ ≤ C := by
  obtain ⟨-, -, -, hJ, hper, ⟨⟨s₀, hD⟩, hdec⟩, -, -⟩ := hstd
  obtain ⟨C₁, s₂, hC₁⟩ := hdec m
  obtain ⟨C₂, hC₂⟩ := jinf_iteratedFDeriv_bdd ρ hρ Jinf hJ hper m
  set f : ℝ × ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ :=
    fun q => cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2) with hf
  set π₂ : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℂ := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ) with hπ
  set g : ℝ × ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ := Jinf ∘ π₂ with hg
  have hsplit : (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2) = f + g := by
    funext q; simp [hf, hg, hπ]
  refine ⟨max C₁ 0 + C₂ * 1, max (max s₂ (s₀ + 1)) 0, fun s hs t w hw => ?_⟩
  have hs₂ : s₂ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs₀ : s₀ < s := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs; linarith
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
  have hwρ : w ∈ ball (0 : ℂ) ρ := closedBall_subset_ball (by linarith) hw
  -- `f` is smooth near `(s, t, w)`
  have hVf : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hmemf : (s, t, w) ∈ Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ :=
    ⟨hs₀, mem_univ _, hwρ⟩
  have hfa : ContDiffAt ℝ m f (s, t, w) :=
    ((hD.contDiffAt (hVf.mem_nhds hmemf)).of_le (by exact_mod_cast le_top))
  -- `g = Jinf ∘ π₂` is smooth near `(s, t, w)`
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ) := (isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ)))
  have hmemg : π₂ (s, t, w) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨mem_univ _, hwρ⟩
  have hJa : ContDiffAt ℝ m Jinf (π₂ (s, t, w)) :=
    (hJ.contDiffAt (hU.mem_nhds hmemg)).of_le (by exact_mod_cast le_top)
  have hga : ContDiffAt ℝ m g (s, t, w) := hJa.comp _ π₂.contDiff.contDiffAt
  rw [hsplit, iteratedFDeriv_add_apply hfa hga]
  -- the decay part
  have h1 : ‖iteratedFDeriv ℝ m f (s, t, w)‖ ≤ max C₁ 0 := by
    have := hC₁ s hs₂ t w hwρ
    have he : Real.exp (-(b * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc _ ≤ C₁ * Real.exp (-(b * s)) := this
      _ ≤ max C₁ 0 * Real.exp (-(b * s)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C₁ 0 * 1 := mul_le_mul_of_nonneg_left he (le_max_right _ _)
      _ = max C₁ 0 := mul_one _
  -- the `Jinf` part, through the projection
  have h2 : ‖iteratedFDeriv ℝ m g (s, t, w)‖ ≤ C₂ * 1 := by
    have hpre : IsOpen (π₂ ⁻¹' (Set.univ ×ˢ ball (0 : ℂ) ρ)) := hU.preimage π₂.continuous
    have hmem' : (s, t, w) ∈ π₂ ⁻¹' (Set.univ ×ˢ ball (0 : ℂ) ρ) := hmemg
    have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right π₂ hJ hU.uniqueDiffOn
      hpre.uniqueDiffOn hmemg (i := m) (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen m hpre hmem',
      iteratedFDerivWithin_of_isOpen m hU hmemg] at hcomp
    rw [hg, hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _i : Fin m, ‖π₂‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => by
        rw [hπ]; exact ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℂ))
    have hC2 : ‖iteratedFDeriv ℝ m Jinf (π₂ (s, t, w))‖ ≤ C₂ := hC₂ t w hw
    have hC2' : 0 ≤ C₂ := (norm_nonneg _).trans hC2
    calc _ ≤ ‖iteratedFDeriv ℝ m Jinf (π₂ (s, t, w))‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_right hC2 zero_le_one
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (m : ℕ) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDeriv ℝ m (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2) (s, t, w)‖ ≤ C :=
  cylJ_iteratedFDeriv_bdd_aux ρ b hρ hb Jbar Jinf Sinf hstd m
