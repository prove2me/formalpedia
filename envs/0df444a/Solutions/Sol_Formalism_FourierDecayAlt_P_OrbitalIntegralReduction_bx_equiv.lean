-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:53.580671+00:00
-- url     : https://prove2.me/submissions/2bb0b21f-24fc-4a6b-93fc-90d1985f4c72

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (Λ : AddSubgroup K)
    (f : (κ → K) → ℂ) : bx R Λ κ f = bx R Λ ι (fun a => f (fun k => a (e.symm k))) := by
  unfold bx
  rw [Fintype.card_congr e]
  congr 1
  rw [← finsum_comp_equiv (Equiv.arrowCongr e (Equiv.refl (K ⧸ Λ)))]
  rfl
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
