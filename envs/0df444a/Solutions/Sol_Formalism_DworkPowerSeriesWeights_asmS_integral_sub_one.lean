-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmS_integral_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:58.696289+00:00
-- url     : https://prove2.me/submissions/08e4cd34-b9c2-4462-a51e-027ab9d6a1c8

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type} {pi ρ : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) (hρ : 0 ≤ ρ) {E : MvPowerSeries ι K} (hE : Integral E)
    (hc : constantCoeff E = 1) : WtGe pi (fun _ => ρ) ρ (E - 1) := by
  classical
  intro n
  unfold MonoWtGe
  by_cases hn : n = 0
  · subst hn
    have h00 : coeff 0 (E - 1) = 0 := by
      rw [map_sub, coeff_zero_eq_constantCoeff_apply, hc, coeff_one, if_pos rfl, sub_self]
    rw [h00, norm_zero]
    exact (Real.rpow_pos_of_pos h0 _).le
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hd : ρ ≤ dot n (fun _ => ρ) := by
      unfold dot Finsupp.sum
      have hmem : i ∈ n.support := Finsupp.mem_support_iff.mpr hi
      have h1' : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      calc ρ ≤ (n i : ℝ) * ρ := by nlinarith
        _ ≤ ∑ x ∈ n.support, (n x : ℝ) * ρ :=
          Finset.single_le_sum (f := fun x => (n x : ℝ) * ρ)
            (fun x _ => mul_nonneg (Nat.cast_nonneg _) hρ) hmem
    have hc1 : coeff n (E - 1) = coeff n E := by
      rw [map_sub, coeff_one, if_neg hn, sub_zero]
    rw [hc1]
    exact (hE n).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by linarith))
end Formalism.DworkPowerSeriesWeights
