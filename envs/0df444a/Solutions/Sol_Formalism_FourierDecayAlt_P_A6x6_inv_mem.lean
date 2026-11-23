-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:42.844993+00:00
-- url     : https://prove2.me/submissions/38f2dcd4-778c-4ae6-ab62-e14052453f7f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_perp_of_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_psi_q_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
variable {L Λ : AddSubgroup K}
variable {ψ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hAdm : GaussAdm ψ L M) {u : Fin m → K}
    (hu : u ∈ PL (perp ψ L) m) : M⁻¹ *ᵥ u ∈ PL (perp ψ (perp ψ L)) m := by
  apply mem_perp_of_dot
  intro x hx
  have hMi : (M⁻¹).IsSymm := hM.inv
  have h1 := hAdm (x + u) (mem_PL.1 ((PL _ m).add_mem hx hu))
  rw [psi_q_add ψ h2 hMi, hAdm x (mem_PL.1 hx), hAdm u (mem_PL.1 hu), one_mul, one_mul] at h1
  exact h1
end Formalism.FourierDecayAlt.P.A6x6
