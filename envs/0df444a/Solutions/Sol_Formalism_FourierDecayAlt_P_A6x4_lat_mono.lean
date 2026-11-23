-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.lat_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.471605+00:00
-- url     : https://prove2.me/submissions/404eea65-233b-4b79-8a43-ca52ef273d03

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_pow_mul_pow_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {p q : K} (hpq : p * q = 1) (hp : p ∈ R) {m m' : ℕ} (h : m ≤ m') {x : K}
    (hx : q ^ m' * x ∈ R) : q ^ m * x ∈ R := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : q ^ m * x = p ^ d * (q ^ (m + d) * x) := by
    have h1 := pow_mul_pow_one hpq d
    rw [pow_add]
    linear_combination (-(q ^ m * x)) * h1
  rw [e]
  exact R.mul_mem (R.pow_mem hp d) hx
end Formalism.FourierDecayAlt.P.A6x4
