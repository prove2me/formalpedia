-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.cut_Q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:29.669168+00:00
-- url     : https://prove2.me/submissions/d0ee2e2c-b6ef-4cf8-9b3e-adc1f533fe2e

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
theorem _root_.solution (m : ℕ) (Om : Set K) (t c : Kˣ) (hc : (c : K) ∈ cutSet m Om t) :
    (c : K) * (t : K) ^ m ∈ (fun z : K => (-1) ^ m * z ^ (m + 1)) '' Om := by
  obtain ⟨z, hz, hzc⟩ := hc
  refine ⟨z, hz, ?_⟩
  simp only
  rw [hzc, neg_pow (t : K) m]
  have h1 : ((-1 : K) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  linear_combination ((t : K) ^ m * c) * h1
end Formalism.FourierDecayAlt.P.GermSumLattices
