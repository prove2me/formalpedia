-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.cut_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:05.302061+00:00
-- url     : https://prove2.me/submissions/a94177aa-d953-4dd4-bc07-9aaf147cfe85

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution [TopologicalSpace K] (m : ℕ) (Om : Set K) (hOm : IsOmega (m + 1) Om) (t c z : Kˣ)
    (hc : (c : K) ∈ cutSet m Om t) (hz : z ^ (m + 1) = (-t) ^ m * c) : (z : K) ∈ Om := by
  obtain ⟨z₀, hz₀, hzc⟩ := hc
  obtain ⟨u, rfl⟩ := hOm.2.2.1 z₀ hz₀
  have h1 : ((z * u⁻¹ : Kˣ) : K) ^ (m + 1) = 1 := by
    have h2 : (z * u⁻¹) ^ (m + 1) = 1 := by
      have hu : u ^ (m + 1) = (-t) ^ m * c := Units.ext (by push_cast; exact hzc)
      rw [mul_pow, inv_pow, hz, hu, mul_inv_cancel]
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have h3 := hOm.2.2.2 u hz₀ _ h1
  simpa using h3
end Formalism.FourierDecayAlt.P.GermSumLattices
