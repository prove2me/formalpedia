-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:34.171334+00:00
-- url     : https://prove2.me/submissions/344a4f96-af20-4a7b-94df-ed3aa753502f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SigmaFiniteOfFcG

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
theorem _root_.solution (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  have hme : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hmap : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνc)
  refine ⟨⟨fun g => ?_⟩, ⟨fun K hK => ?_⟩, hmap⟩
  · have h1 : ((ν.comap (Subtype.val : S → G)).map (fun x => g * x)).map Subtype.val = ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul g)]
      have : (Subtype.val : S → G) ∘ (fun x : S => g * x) =
          (fun x : G => (g : G) * x) ∘ (Subtype.val : S → G) := by
        funext x; rfl
      rw [this, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact hνi g g.2
    calc (ν.comap (Subtype.val : S → G)).map (fun x => g * x)
        = (((ν.comap (Subtype.val : S → G)).map (fun x => g * x)).map Subtype.val).comap
            Subtype.val := (hme.comap_map _).symm
      _ = ν.comap Subtype.val := by rw [h1]
  · rw [hme.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore
