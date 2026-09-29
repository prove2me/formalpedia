-- Prove2me | solution 1 for BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-09T12:36:59.24158+00:00
-- url     : https://prove2.me/submissions/8377fd6b-6707-4be2-847c-9daa5719c92b

-- Generated from ChapterSirkDiffusiveDecay.lean — solution of BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
import Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_heatFlow_zero
import Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_hasDerivAt_heatFlow_normSq
open BookProof.ChapterSirkDiffusiveDecay










noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) {mu : ℝ} (hA : IsCoercive A mu) (v : E)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heatFlow A t v‖ ≤ Real.exp (-(mu * t)) * ‖v‖ := by

  -- the Grönwall functional
  set G : ℝ → ℝ := fun s => ‖heatFlow A s v‖ ^ 2 * Real.exp (2 * mu * s) with hG
  have hderiv : ∀ s : ℝ, HasDerivAt G
      ((-2 * (inner ℂ (heatFlow A s v) (A (heatFlow A s v)) : ℂ).re
        + 2 * mu * ‖heatFlow A s v‖ ^ 2) * Real.exp (2 * mu * s)) s := by
    intro s
    have h1 := hasDerivAt_heatFlow_normSq A v s
    have h2 : HasDerivAt (fun r : ℝ => Real.exp (2 * mu * r))
        (2 * mu * Real.exp (2 * mu * s)) s := by
      have := (((hasDerivAt_id s).const_mul (2 * mu)).exp)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have := h1.mul h2
    convert this using 1
    · rfl
    · rfl
    · rfl
    · ring
  have hnonpos : ∀ s : ℝ, deriv G s ≤ 0 := by
    intro s
    rw [(hderiv s).deriv]
    have hco := hA (heatFlow A s v)
    have hexp : 0 < Real.exp (2 * mu * s) := Real.exp_pos _
    have : -2 * (inner ℂ (heatFlow A s v) (A (heatFlow A s v)) : ℂ).re
        + 2 * mu * ‖heatFlow A s v‖ ^ 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg this hexp.le
  have hdiff : Differentiable ℝ G := fun s => (hderiv s).differentiableAt
  have hanti : Antitone G := antitone_of_deriv_nonpos hdiff hnonpos
  have hle : G t ≤ G 0 := hanti ht
  have hG0 : G 0 = ‖v‖ ^ 2 := by
    simp [hG, heatFlow]
  rw [hG0] at hle
  -- undo the exponential weight
  have hexp : (0 : ℝ) < Real.exp (2 * mu * t) := Real.exp_pos _
  have hsq : ‖heatFlow A t v‖ ^ 2 ≤ (Real.exp (-(mu * t)) * ‖v‖) ^ 2 := by
    have h1 : ‖heatFlow A t v‖ ^ 2 ≤ ‖v‖ ^ 2 / Real.exp (2 * mu * t) := by
      rw [le_div_iff₀ hexp]
      simpa [hG] using hle
    have h2 : (Real.exp (-(mu * t)) * ‖v‖) ^ 2 = ‖v‖ ^ 2 / Real.exp (2 * mu * t) := by
      rw [mul_pow, sq (Real.exp (-(mu * t))), ← Real.exp_add, div_eq_mul_inv,
        ← Real.exp_neg]
      ring_nf
    rw [h2]
    exact h1
  have hnn : (0 : ℝ) ≤ Real.exp (-(mu * t)) * ‖v‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  nlinarith [norm_nonneg (heatFlow A t v)]
