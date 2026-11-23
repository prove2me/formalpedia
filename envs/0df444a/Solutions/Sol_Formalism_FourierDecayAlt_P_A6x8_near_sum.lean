-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.near_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:16.68297+00:00
-- url     : https://prove2.me/submissions/81af90db-719b-43dd-a803-1c7e9beb28e7

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
theorem _root_.solution {a : K} (n : ℕ) (f : ℕ → K) (hf : ∀ i, Near R a (f i)) :
    ∃ q ∈ R, ∑ i ∈ Finset.range n, f i = (n : K) + a * q := by
  induction n with
  | zero => exact ⟨0, R.zero_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, e⟩ := ih
    obtain ⟨r, hr, e'⟩ := hf n
    exact ⟨q + r, R.add_mem hq hr, by rw [Finset.sum_range_succ, e, e']; push_cast; ring⟩
end Formalism.FourierDecayAlt.P.A6x8
