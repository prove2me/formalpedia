-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:54.802574+00:00
-- url     : https://prove2.me/submissions/2405b367-fce7-4aff-a589-ce99c1b45315

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Near_mul

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Adic
theorem _root_.solution (h : Adic R ϖ) {C : Set K} (hC : IsCompact C) :
    ∃ a : ℕ, ∀ x ∈ C, (ϖ : K) ^ a * x ∈ R := by
  obtain ⟨a, ha⟩ := hC.elim_directed_cover (fun a : ℕ => {x : K | (ϖ : K) ^ a * x ∈ R})
    (fun a => h.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => by
      obtain ⟨m, hm⟩ := h.absorb x
      exact Set.mem_iUnion.2 ⟨m, hm⟩)
    (Monotone.directed_le (by
      intro a b hab x hx
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      have : (ϖ : K) ^ (a + d) * x = (ϖ : K) ^ d * ((ϖ : K) ^ a * x) := by ring
      show (ϖ : K) ^ (a + d) * x ∈ R
      rw [this]; exact R.mul_mem (R.pow_mem h.mem d) hx))
  exact ⟨a, fun x hx => ha hx⟩
end Adic
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
