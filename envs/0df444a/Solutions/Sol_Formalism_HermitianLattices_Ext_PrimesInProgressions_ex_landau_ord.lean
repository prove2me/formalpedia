-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_landau_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:25.127846+00:00
-- url     : https://prove2.me/submissions/124d5910-ced3-48fc-8407-d5101ae921a3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLoc
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_landau_ord_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 1 ≤ B)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ) ∧
      ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log B / r := by
  obtain ⟨Z, m, hZ, hm1, hmo, hcnt, hest⟩ := ex_landau_ord_core f z₀ r B hr hB hf hfz₀ hbound
  have hsum : ∀ z : ℂ, ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) :=
    fun z => Finset.sum_congr rfl (fun ρ hρ => by rw [hmo ρ hρ])
  refine ⟨Z, hZ, fun ρ hρ => by rw [hmo ρ hρ]; exact hm1 ρ hρ, ?_, ?_⟩
  · rw [Finset.sum_congr rfl hmo]
    exact hcnt
  · intro z hz hfz
    rw [hsum z]
    exact hest z hz hfz
end Formalism.HermitianLattices.Ext.PrimesInProgressions
