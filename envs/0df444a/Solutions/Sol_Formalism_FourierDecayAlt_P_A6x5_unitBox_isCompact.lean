-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.unitBox_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:37.044381+00:00
-- url     : https://prove2.me/submissions/7a4aec1c-6493-4def-98c8-1131ada542dc

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_preimage_pow_eq_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (hD : LocalDatum K R ψ) (ϖ : Kˣ) (j : ℕ) :
    IsCompact (unitBox R ϖ j) := by
  have := hD.t2
  have hA : IsCompact ((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K)) := by
    rw [preimage_pow_eq_image]
    exact hD.isCompact.image (continuous_const.mul continuous_id)
  have hP : IsCompact ((((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K)) ×ˢ
      ((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K))) ∩ {p : K × K | p.1 * p.2 = 1}) :=
    (hA.prod hA).inter_right (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  have : unitBox R ϖ j = Prod.fst '' ((((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K)) ×ˢ
      ((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K))) ∩ {p : K × K | p.1 * p.2 = 1}) := by
    ext z
    constructor
    · rintro ⟨y, hzy, hz, hy⟩
      exact ⟨(z, y), ⟨⟨hz, hy⟩, hzy⟩, rfl⟩
    · rintro ⟨⟨z', y⟩, ⟨⟨hz, hy⟩, hzy⟩, rfl⟩
      exact ⟨y, hzy, hz, hy⟩
  rw [this]
  exact hP.image continuous_fst
end Formalism.FourierDecayAlt.P.A6x5
