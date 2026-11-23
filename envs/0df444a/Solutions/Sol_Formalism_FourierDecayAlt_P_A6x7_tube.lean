-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.tube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:59.065151+00:00
-- url     : https://prove2.me/submissions/1ae3850c-e83f-4312-9888-0e96c3d61546

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
theorem _root_.solution {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X × Y → Z) (hF : Continuous F) (x0 : X) (C : Set Y) (hC : IsCompact C) (U : Set Z)
    (hU : IsOpen U) (h : ∀ y ∈ C, F (x0, y) ∈ U) : ∃ V ∈ 𝓝 x0, ∀ x ∈ V, ∀ y ∈ C, F (x, y) ∈ U := by
  obtain ⟨u, v, hu, -, hxu, hCv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x0)) hC
    (hU.preimage hF) (by rintro ⟨a, b⟩ ⟨ha, hb⟩; rw [Set.mem_singleton_iff] at ha; subst ha; exact h b hb)
  exact ⟨u, hu.mem_nhds (hxu rfl), fun x hx y hy => huv ⟨hx, hCv hy⟩⟩
end Formalism.FourierDecayAlt.P.A6x7
