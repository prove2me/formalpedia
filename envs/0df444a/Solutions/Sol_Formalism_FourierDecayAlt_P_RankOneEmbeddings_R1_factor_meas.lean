-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.factor_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:45.848692+00:00
-- url     : https://prove2.me/submissions/a1695e5a-2f18-4ad7-a304-58ee9eed8345

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution {X V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace V]
    [MeasurableSpace.CountablySeparated V] (π : X → V) (hπ : Measurable π) (F : X → ℝ≥0∞) (hF : Measurable F)
    (hfib : ∀ x y, π x = π y → F x = F y) : ∃ G : V → ℝ≥0∞, Measurable G ∧ ∀ x, F x = G (π x) := by
  have h1 : Measurable[MeasurableSpace.comap π inferInstance] F := by
    intro B hB
    have hA : MeasurableSet (F ⁻¹' B) := hF hB
    have hsat : π ⁻¹' (π '' (F ⁻¹' B)) = F ⁻¹' B := by
      ext x; constructor
      · rintro ⟨y, hy, hxy⟩
        show F x ∈ B
        rw [hfib x y hxy.symm]; exact hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [← hsat] at hA
    have : MeasurableSpace.CountablySeparated (Set.range π) := MeasurableSpace.Subtype.countablySeparated
    have h2 := (hπ.measurableSet_preimage_iff_preimage_val).mp hA
    obtain ⟨B', hB', hBB⟩ := h2
    refine ⟨B', hB', ?_⟩
    rw [← hsat]
    ext x
    have := congrArg (fun S : Set (Set.range π) => (⟨π x, x, rfl⟩ : Set.range π) ∈ S) hBB
    simpa using this
  obtain ⟨G, hG, hFG⟩ := h1.exists_eq_measurable_comp
  exact ⟨G, hG, fun x => congrFun hFG x⟩
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
