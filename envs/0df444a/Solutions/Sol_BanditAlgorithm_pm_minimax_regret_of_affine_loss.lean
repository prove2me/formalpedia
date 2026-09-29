-- Prove2me | solution 1 for BanditAlgorithm.pm_minimax_regret_of_affine_loss
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:30:22.037794+00:00
-- url     : https://prove2.me/submissions/28ca4915-5f01-4bd8-a53d-ab7fb880edbb

import Definitions.Def_PartialMonitoringGame
import Mathlib.Data.Real.Pointwise

/-!
# Minimax regret under an affine change of the loss matrix

If two partial monitoring games share a feedback matrix and their losses differ by
`L' a i = λ * L a i + c i` (a positive rescaling and a shift that may depend on the outcome
but not on the action), then `R*_n(G') = λ * R*_n(G)`.

The regret of L&S §37.2 is built from loss *differences* `L_{A_t, i_t} - L_{a, i_t}`, so the
per-outcome shift `c` cancels identically and the scaling factors out.

This is the normalisation step needed to apply results stated for games with losses in `[0,1]`
(as in Theorems 37.15-37.17) to the classification theorem 37.11, which quantifies over games
with an arbitrary real loss matrix.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

variable {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]

/-- The interaction measure depends on the game only through its feedback matrix. -/
private lemma pmMeasure_congr (G G' : PartialMonitoringGame k d 𝕊) (hΦ : G'.Φ = G.Φ)
    (π : PMPolicy k 𝕊) : ∀ (n : ℕ) (i : Fin n → Fin d),
    pmMeasure G' π n i = pmMeasure G π n i
  | 0, _ => by simp [pmMeasure]
  | n + 1, i => by
      have hstep : pmStepKernel G' π (i (Fin.last n)) n = pmStepKernel G π (i (Fin.last n)) n := by
        simp [pmStepKernel, hΦ]
      rw [pmMeasure, pmMeasure, pmMeasure_congr G G' hΦ π n (fun t ↦ i t.castSucc), hstep]

theorem _root_.solution (G G' : PartialMonitoringGame k d 𝕊)
    (lam : ℝ) (hlam : 0 ≤ lam) (c : Fin d → ℝ)
    (hL : ∀ a i, G'.L a i = lam * G.L a i + c i) (hΦ : G'.Φ = G.Φ) (n : ℕ) :
    pmMinimaxRegret G' n = lam * pmMinimaxRegret G n := by
  classical
  have hmeas := pmMeasure_congr G G' hΦ
  -- the regret of every policy against every outcome sequence scales
  have hreg : ∀ (π : PMPolicy k 𝕊) (i : Fin n → Fin d),
      pmRegret G' π n i = lam * pmRegret G π n i := by
    intro π i
    have hint : ∀ a : Fin k,
        ∫ h, (∑ t, (G'.L (h t).1 (i t) - G'.L a (i t))) ∂(pmMeasure G' π n i)
          = lam * ∫ h, (∑ t, (G.L (h t).1 (i t) - G.L a (i t))) ∂(pmMeasure G π n i) := by
      intro a
      rw [hmeas π n i, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [hL, hL]
      ring
    rw [pmRegret, pmRegret]
    calc (⨆ a : Fin k, ∫ h, (∑ t, (G'.L (h t).1 (i t) - G'.L a (i t))) ∂(pmMeasure G' π n i))
        = ⨆ a : Fin k, lam * ∫ h, (∑ t, (G.L (h t).1 (i t) - G.L a (i t)))
            ∂(pmMeasure G π n i) := by
          exact iSup_congr hint
      _ = lam * ⨆ a : Fin k, ∫ h, (∑ t, (G.L (h t).1 (i t) - G.L a (i t)))
            ∂(pmMeasure G π n i) := (Real.mul_iSup_of_nonneg hlam _).symm
  -- and the scaling passes through the `sup` over outcomes and the `inf` over policies
  rw [pmMinimaxRegret, pmMinimaxRegret]
  calc (⨅ π : PMPolicy k 𝕊, ⨆ i : Fin n → Fin d, pmRegret G' π n i)
      = ⨅ π : PMPolicy k 𝕊, ⨆ i : Fin n → Fin d, lam * pmRegret G π n i := by
        exact iInf_congr fun π ↦ iSup_congr fun i ↦ hreg π i
    _ = ⨅ π : PMPolicy k 𝕊, lam * ⨆ i : Fin n → Fin d, pmRegret G π n i := by
        exact iInf_congr fun π ↦ (Real.mul_iSup_of_nonneg hlam _).symm
    _ = lam * ⨅ π : PMPolicy k 𝕊, ⨆ i : Fin n → Fin d, pmRegret G π n i :=
        (Real.mul_iInf_of_nonneg hlam _).symm

end BanditAlgorithm
