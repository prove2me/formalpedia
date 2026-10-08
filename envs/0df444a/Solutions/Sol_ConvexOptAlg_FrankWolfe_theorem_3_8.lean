-- Prove2me | solution 1 for ConvexOptAlg.FrankWolfe.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:45:01.24156+00:00
-- url     : https://prove2.me/submissions/493b9db3-3609-4667-8de2-bae26ab94320

import Theorems.Thm_ConvexOptAlg_FrankWolfe_thm_3_8_step
import Theorems.Thm_ConvexOptAlg_FrankWolfe_thm_3_8_init
import Theorems.Thm_ConvexOptAlg_FrankWolfe_thm_3_8_induction

open ConvexOptAlg.FrankWolfe

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hopt : ∀ z ∈ X, f xstar ≤ f z)
    (γ : ℕ → ℝ) (hγ : ∀ s : ℕ, 1 ≤ s → γ s = 2 / ((s : ℝ) + 1))
    (x y : ℕ → E) (hrun : IsFrankWolfeRun X f' γ x y)
    (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * Metric.diam X ^ 2 / ((t : ℝ) + 1) := by
  have hγrange (s : ℕ) (hs : 1 ≤ s) : γ s ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hγ s hs]
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < s + 1)).mpr
      linarith
  have hγ1 : γ 1 = 1 := by
    have h := hγ 1 le_rfl
    norm_num at h
    exact h
  have hinit := thm_3_8_init X hXc hXconv f f' β hβ hf hsmooth
    xstar hxstar hopt γ hγ1 x y hrun
  apply thm_3_8_induction (fun n => f (x n) - f xstar) β (Metric.diam X) hβ hinit
    (fun s hs => ?_) t ht
  have hs' : 1 ≤ s := by omega
  simpa only [hγ s hs'] using
    thm_3_8_step X hXc hXconv f f' β hβ hf hsmooth
      xstar hxstar hopt γ hγrange x y hrun s hs'
