-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:29.0198+00:00
-- url     : https://prove2.me/submissions/baa9253b-ed9f-4002-8e7b-f7549256d656

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SigmaFiniteOfFcG
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_JacobianCoordinates_JL_HaarCore_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
theorem _root_.solution (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S :=
    TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  obtain ⟨hμl, hμk, hμm⟩ := pull S hS μ hμc hμi hμf
  obtain ⟨hml, hmk, hmm⟩ := pull S hS m hmc hmi hmf
  set μ' := μ.comap (Subtype.val : S → G)
  set m' := m.comap (Subtype.val : S → G)
  have hμ := Measure.isMulLeftInvariant_eq_smul μ' (Measure.haar : Measure S)
  have hm := Measure.isMulLeftInvariant_eq_smul m' (Measure.haar : Measure S)
  set d := Measure.haarScalarFactor μ' (Measure.haar : Measure S)
  set c := Measure.haarScalarFactor m' (Measure.haar : Measure S)
  have hd : d ≠ 0 := by
    intro h0
    apply hμ0
    rw [← hμm, hμ, h0, zero_smul, Measure.map_zero]
  refine ⟨((c / d : ℝ≥0) : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  have hm'' : m' = (c / d) • μ' := by
    rw [hm, hμ, smul_smul, div_mul_cancel₀ c hd]
  rw [← hmm, ← hμm, hm'', Measure.map_smul]
  rfl
end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
