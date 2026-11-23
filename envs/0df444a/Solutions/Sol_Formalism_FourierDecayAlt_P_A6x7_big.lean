-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:16.248617+00:00
-- url     : https://prove2.me/submissions/349a1697-ce09-4494-bb07-e4bf3697cee3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7
theorem _root_.solution (hD : LocalDatum K R ψ) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (C : Set K)
    (hC : IsCompact C) : ∃ n : ℕ, ∀ y ∈ C, (ϖ : K) ^ n * y ∈ R := by
  obtain ⟨n, hn⟩ := hC.elim_directed_cover
    (fun n : ℕ => (fun y => (ϖ : K) ^ n * y) ⁻¹' (R : Set K))
    (fun n => hD.isOpen.preimage (continuous_const.mul continuous_id))
    (by
      intro y _
      rw [Set.mem_iUnion]
      exact hϖ' y)
    (by
      apply directed_of_isDirected_le
      intro a b hab y hy
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      show (ϖ : K) ^ (a + k) * y ∈ R
      have e : (ϖ : K) ^ (a + k) * y = (ϖ : K) ^ k * ((ϖ : K) ^ a * y) := by rw [pow_add]; ring
      rw [e]; exact R.mul_mem (R.pow_mem hϖ k) hy)
  exact ⟨n, fun y hy => hn hy⟩
end Formalism.FourierDecayAlt.P.A6x7
