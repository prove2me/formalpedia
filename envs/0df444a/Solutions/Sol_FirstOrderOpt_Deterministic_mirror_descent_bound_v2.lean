-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.mirror_descent_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T20:51:04.662889+00:00
-- url     : https://prove2.me/submissions/16c623db-88b4-45b5-99ea-736cabd4a128

/-
Formalization by Alexander Richard Towell (queelius), with substantial OpenAI
Codex assistance in proof construction, verification and documentation.
Mathematical source: Guanghui Lan, First-order and Stochastic Optimization
Methods for Machine Learning, Springer 2020, Theorem 3.5, p.61.
The actual accepted three-point proof by Nickrobbins95 (target
0486961f-f909-4c98-96ee-4631a57b9649; submission
69ea7e6a-3618-4fc1-b0cb-bb3dfff633eb) is reproduced below in its own namespace;
its body is unchanged. It is prior work, not a new result of this contribution.
Community (Bot) supplied the corrected platform formulation: convex f, closed
convex X, and the genuine distance-generating-function Bregman distance.
The new formalization supplies the norm bound, squared-distance estimate,
weighted telescope on the full interval, terminal nonnegativity and Jensen.
Lean/Mathlib contributors supply the foundational library. No new mathematical
theorem or independent human proof review is claimed. This proves the corrected
statement only, not its retired false predecessor.
-/
import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace Nickrobbins95

set_option autoImplicit false

open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (xt xt1 : E) (gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * gt xt1 + ν.V xt xt1 ≤ γt * gt x + ν.V xt x) :
    ∀ x ∈ X, γt * gt (xt1 - x) + ν.V xt xt1 ≤ ν.V xt x - ν.V xt1 x := by
  intro x hx
  set f : E → ℝ := fun u => γt * gt u + (ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt)) with hf
  have hfV : ∀ u, f u = γt * gt u + ν.V xt u := by
    intro u
    simp only [hf, DistanceGeneratingFunction.V, map_sub]
  have hloc : IsLocalMinOn f X xt1 := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin (fun u hu => ?_)
    show f xt1 ≤ f u
    rw [hfV, hfV]
    exact hmin u hu
  have hder : HasFDerivWithinAt f
      (γt • gt + (ν.dω xt1 - ν.dω xt)) X xt1 := by
    have h1 : HasFDerivWithinAt (fun u => γt * gt u) (γt • gt) X xt1 :=
      gt.hasFDerivWithinAt.const_mul γt
    have h2 : HasFDerivWithinAt (fun u => ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt))
        (ν.dω xt1 - ν.dω xt) X xt1 :=
      ((ν.hasFDerivWithinAt xt1 hxt1).sub_const _).sub
        ((ν.dω xt).hasFDerivWithinAt.sub_const _)
    exact h1.add h2
  have hseg : segment ℝ xt1 x ⊆ X := hXconv.segment_subset hxt1 hx
  have hcone := sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnn := hloc.hasFDerivWithinAt_nonneg hder hcone
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, map_sub] at hnn
  simp only [DistanceGeneratingFunction.V, map_sub]
  linarith

end Nickrobbins95

open FirstOrderOpt.Prox
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f : E → ℝ) (hfconv : ConvexOn ℝ X f)
    (ν : DistanceGeneratingFunction X) (M : ℝ) (hM : 0 < M)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (γ : ℕ → ℝ)
    (hx : ∀ t, x t ∈ X) (hγ : ∀ t, 0 < γ t) (hgnorm : ∀ t, ‖g t‖ ≤ M)
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + (g t) (y - x t) ≤ f y)
    (hmin : ∀ t, ∀ y ∈ X, γ t * (g t) (x (t + 1)) + ν.V (x t) (x (t + 1)) ≤
      γ t * (g t) y + ν.V (x t) y)
    (s k : ℕ) (hsk : s ≤ k)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y)
    (xbar : E)
    (hxbar : xbar = (∑ t ∈ Finset.Icc s k, γ t)⁻¹ • ∑ t ∈ Finset.Icc s k, γ t • x t) :
    f xbar - f xstar ≤ (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (ν.V (x s) xstar + (1 / 2) * M ^ 2 * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2) := by
  have hV (a b : E) (ha : a ∈ X) (hb : b ∈ X) :
      (1 / 2 : ℝ) * ‖b - a‖ ^ 2 ≤ ν.V a b := by
    have hh := ν.strongConvex a ha b hb
    unfold DistanceGeneratingFunction.V
    linarith
  have hstep (t : ℕ) : γ t * (f (x t) - f xstar) ≤
      ν.V (x t) xstar - ν.V (x (t+1)) xstar + (1/2) * M^2 * (γ t)^2 := by
    have hp := Nickrobbins95.solution X hXconv hXclosed ν (x t) (x (t+1))
      (g t) (γ t) (hx t) (hx (t+1)) (hmin t) xstar hxstar
    have hs := mul_le_mul_of_nonneg_left (hsub t xstar hxstar) (le_of_lt (hγ t))
    have hn : g t (x t - x (t+1)) ≤ M * ‖x (t+1) - x t‖ := by
      calc
        g t (x t - x (t+1)) ≤ ‖g t (x t - x (t+1))‖ := le_abs_self _
        _ ≤ ‖g t‖ * ‖x t - x (t+1)‖ := (g t).le_opNorm _
        _ ≤ M * ‖x t - x (t+1)‖ := mul_le_mul_of_nonneg_right (hgnorm t) (norm_nonneg _)
        _ = M * ‖x (t+1) - x t‖ := by rw [norm_sub_rev]
    have hn' := mul_le_mul_of_nonneg_left hn (le_of_lt (hγ t))
    have hv := hV (x t) (x (t+1)) (hx t) (hx (t+1))
    have hsq := sq_nonneg (M * γ t - ‖x (t+1) - x t‖)
    simp only [map_sub] at hp hs hn'
    nlinarith
  have htel (j : ℕ) (hj : s ≤ j) :
      ∑ t ∈ Finset.Icc s j, γ t * (f (x t) - f xstar) ≤
        ν.V (x s) xstar - ν.V (x (j+1)) xstar +
          (1/2) * M^2 * ∑ t ∈ Finset.Icc s j, (γ t)^2 := by
    induction j, hj using Nat.le_induction with
    | base => simpa using hstep s
    | succ j hj ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hj), Finset.sum_Icc_succ_top (Nat.le_succ_of_le hj)]
      have hh := hstep (j+1)
      nlinarith
  have hvn : 0 ≤ ν.V (x (k+1)) xstar :=
    le_trans (by positivity) (hV (x (k+1)) xstar (hx (k+1)) hxstar)
  have hsum : ∑ t ∈ Finset.Icc s k, γ t * (f (x t) - f xstar) ≤
      ν.V (x s) xstar + (1/2) * M^2 * ∑ t ∈ Finset.Icc s k, (γ t)^2 := by
    have hh := htel k hsk
    linarith
  have hpos : 0 < ∑ t ∈ Finset.Icc s k, γ t :=
    Finset.sum_pos (fun t ht => hγ t) (Finset.nonempty_Icc.mpr hsk)
  have hjensen := hfconv.map_centerMass_le
    (t := Finset.Icc s k) (w := γ) (p := x)
    (fun t ht => (hγ t).le) hpos (fun t ht => hx t)
  simp only [Finset.centerMass, Function.comp_def, smul_eq_mul] at hjensen
  rw [← hxbar] at hjensen
  have hscaled := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
  have hidentity : (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (∑ t ∈ Finset.Icc s k, γ t * (f (x t) - f xstar)) =
      (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (∑ t ∈ Finset.Icc s k, γ t * f (x t)) - f xstar := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp
  rw [hidentity] at hscaled
  linarith
