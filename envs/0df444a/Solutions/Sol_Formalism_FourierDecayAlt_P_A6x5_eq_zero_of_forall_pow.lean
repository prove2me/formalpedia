-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.eq_zero_of_forall_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:57.874947+00:00
-- url     : https://prove2.me/submissions/2d0de20f-4d66-4e28-9bb8-a261d2443de3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_eq_zero_of_ideal_compact

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
theorem _root_.solution (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (x : K)
    (hx : ∀ N : ℕ, ∃ r ∈ R, x = (ϖ : K) ^ N * r) : x = 0 := by
  have := hD.t2
  have := hD.red
  refine eq_zero_of_ideal_compact hn (R : Set K) hD.isCompact x ?_
  intro a
  obtain ⟨m, hm⟩ := hϖ a
  obtain ⟨r, hr, hxr⟩ := hx m
  have : a * x = (ϖ : K) ^ m * a * r := by rw [hxr]; ring
  rw [this]
  exact R.mul_mem hm hr
end Formalism.FourierDecayAlt.P.A6x5
