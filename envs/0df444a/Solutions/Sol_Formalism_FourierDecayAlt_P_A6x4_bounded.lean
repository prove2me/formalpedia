-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:59.364235+00:00
-- url     : https://prove2.me/submissions/678df625-bc94-4bdd-b4b9-16cec4309d3c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

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
theorem _root_.solution (hD : LocalDatum K R ψ) {p : K} (hp : p ∈ R)
    (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {C : Set K} (hC : IsCompact C) :
    ∃ m : ℕ, ∀ z ∈ C, p ^ m * z ∈ R := by
  obtain ⟨m, hm⟩ := hC.elim_directed_cover (fun m : ℕ => (fun x => p ^ m * x) ⁻¹' (R : Set K))
    (fun m => hD.isOpen.preimage (by fun_prop))
    (fun z _ => by
      obtain ⟨m, hm⟩ := hex z
      exact Set.mem_iUnion.2 ⟨m, hm⟩)
    (by
      apply Monotone.directed_le
      intro m m' h x hx
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : p ^ (m + d) * x = p ^ d * (p ^ m * x) := by ring
      show p ^ (m + d) * x ∈ R
      rw [e]
      exact R.mul_mem (R.pow_mem hp d) hx)
  exact ⟨m, fun z hz => hm hz⟩
end Formalism.FourierDecayAlt.P.A6x4
