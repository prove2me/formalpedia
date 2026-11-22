-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.Near.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:41.757627+00:00
-- url     : https://prove2.me/submissions/72770298-238f-46c3-a5c4-ba49091dc428

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.A6x8
namespace Near
theorem _root_.solution {a x y : K} (ha : a ∈ R) (hx : Near R a x) (hy : Near R a y) : Near R a (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨r + q + a * r * q, R.add_mem (R.add_mem hr hq) (R.mul_mem (R.mul_mem ha hr) hq), by ring⟩
end Near
end Formalism.FourierDecayAlt.P.A6x8
