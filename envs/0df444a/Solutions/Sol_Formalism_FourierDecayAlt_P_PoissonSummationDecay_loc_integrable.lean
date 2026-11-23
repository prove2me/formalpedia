-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:44.4433+00:00
-- url     : https://prove2.me/submissions/3ed2eeb5-6961-4b4e-af7d-0594fce5499b

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ)
    (hc : Continuous φ) (h : LocSummable Λ φ) : Integrable φ := by
  let b := Module.Free.chooseBasis ℤ Λ
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hDb := ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ Λ)
  have hDm := ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ Λ)
  obtain ⟨c, hcs, hcb⟩ := h (closure (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) hDb.isCompact_closure
  haveI : VAddInvariantMeasure Λ V (volume : Measure V) := ⟨fun c s _ => measure_preimage_add volume (c : V) s⟩
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [hD.lintegral_eq_tsum'']
  have hle : ∀ l : Λ, ∫⁻ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), ‖φ (l +ᵥ x)‖ₑ ≤
      ENNReal.ofReal |c l| * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) := by
    intro l
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hDm fun x hx => ?_
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal ((hcb l x (subset_closure hx)).trans (le_abs_self _))
  calc ∑' l : Λ, ∫⁻ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), ‖φ (l +ᵥ x)‖ₑ
      ≤ ∑' l : Λ, ENNReal.ofReal |c l| * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) :=
        ENNReal.tsum_le_tsum hle
    _ = ENNReal.ofReal (∑' l, |c l|) * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hcs.abs]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDb.measure_lt_top
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
