-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.pow_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:13.349918+00:00
-- url     : https://prove2.me/submissions/8c7c4677-0873-4e6b-9770-8c173efc1fd1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_near_sum

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
theorem _root_.solution {c : K} (hc : c ∈ R) (s : ℕ) {x y : K} (hx : Near R ((s : K) * c) x)
    (hy : Near R ((s : K) * c) y) : ∃ q ∈ R, x ^ s - y ^ s = (s : K) * (x - y) * (1 + c * q) := by
  have ha : (s : K) * c ∈ R := R.mul_mem (natCast_mem R s) hc
  obtain ⟨q, hq, e⟩ := near_sum (R := R) s (fun i => x ^ i * y ^ (s - 1 - i))
    (fun i => (hx.pow ha i).mul ha (hy.pow ha _))
  refine ⟨q, hq, ?_⟩
  rw [← geom_sum₂_mul, e]; ring
end Formalism.FourierDecayAlt.P.A6x8
