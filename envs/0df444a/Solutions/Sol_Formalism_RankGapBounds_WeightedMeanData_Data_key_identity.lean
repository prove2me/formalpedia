-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.Data.key_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:37.313801+00:00
-- url     : https://prove2.me/submissions/657b9813-cec9-4f84-91e7-2b7321255a06

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
open Formalism.RankGapBounds.WeightedMeanData.Data
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
namespace Formalism.RankGapBounds.WeightedMeanData.Data
theorem _root_.solution (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * D.abelian₂ C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k)
        + 2 * D.logGam / ((f : ℝ) * D.k)) := by
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have hcard : ∀ c : ℝ, ∑ _j : Fin m, c = (m : ℝ) * c := fun c => by simp
  have hcardf : ∀ c : ℝ, ∑ _ρ : Fin f, c = (f : ℝ) * c := fun c => by simp
  have hpi : Real.log (π / D.v) = Real.log π - Real.log D.v :=
    Real.log_div Real.pi_ne_zero hv.ne'
  have hff : 1 / (f : ℝ) * (f : ℝ) = 1 := by rw [one_div, inv_mul_cancel₀ hfR]
  have h1 : ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)
      = ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)
        + (m : ℝ) * (Real.log D.v - Real.log π) := by
    rw [← hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)
        = ∑ ρ : Fin f, Real.log (D.w u0 j ρ) + (f : ℝ) * (Real.log D.v - Real.log π) := by
      rw [← hcardf, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Real.log_div (mul_pos (hw j ρ) hv).ne' Real.pi_ne_zero,
        Real.log_mul (hw j ρ).ne' hv.ne']
      ring
    rw [e1]
    linear_combination (Real.log D.v - Real.log π) * hff
  have h2 : D.SDiv = (m : ℝ) * ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL)
      - (m : ℝ) * (Real.log π - Real.log D.v) * D.sumA := by
    unfold Data.SDiv Data.sumA
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [ph, Data.logOm]
    rw [hpi]
    ring
  have hMj : ∀ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
        - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))
      = ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL)
        - D.sumA * ((1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)) := by
    intro j
    unfold Data.sumA
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have h3 : D.Main u0 = (m : ℝ) * ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL)
      - D.sumA * ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ) := by
    unfold Data.Main
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hMj j), Finset.sum_sub_distrib,
      hcard, ← Finset.mul_sum]
  unfold Data.abelian₂
  linear_combination h2 - D.sumA * h1 - h3
end Formalism.RankGapBounds.WeightedMeanData.Data
