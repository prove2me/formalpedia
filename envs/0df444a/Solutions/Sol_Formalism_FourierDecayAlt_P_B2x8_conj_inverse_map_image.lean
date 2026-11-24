-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:08.746639+00:00
-- url     : https://prove2.me/submissions/aef4837b-77cf-4cd2-b370-80652df1d420

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (l : ℂ) (hl : l ≠ 0) : (fun c : ℂ => l / conj c) '' {(0 : ℂ)}ᶜ = {(0 : ℂ)}ᶜ := by
  have hl' : conj l ≠ 0 := (map_ne_zero _).2 hl
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact div_ne_zero hl ((map_ne_zero _).2 hc)
  · intro hx
    have hx' : conj x ≠ 0 := (map_ne_zero _).2 hx
    refine ⟨conj l / conj x, div_ne_zero hl' hx', ?_⟩
    simp only [map_div₀, Complex.conj_conj]
    field_simp
end Formalism.FourierDecayAlt.P.B2x8
