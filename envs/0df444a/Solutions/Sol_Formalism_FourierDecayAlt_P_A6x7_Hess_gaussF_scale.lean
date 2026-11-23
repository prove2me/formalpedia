-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.gaussF_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.837129+00:00
-- url     : https://prove2.me/submissions/5290fd80-303d-4c7e-a632-a8fece38a878

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_hessM_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_quad_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mem_mulLat


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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (ψ : AddChar K ℂ) (L : AddSubgroup K) (m : ℕ) (a b : Kˣ) (ξ : Fin m → K) :
    gaussF ψ (mulLat (b : K) L) (hessM m (a * b ^ 2)) ((b : K) • ξ) =
      gaussF ψ L (hessM m a) ξ := by
  classical
  have h1 : (∀ i, ((b : K) • ξ) i ∈ mulLat (b : K) L) ↔ ∀ i, ξ i ∈ L :=
    forall_congr' fun i => mem_mulLat b L (ξ i)
  have h2 : ((b : K) • ξ) ⬝ᵥ (hessM m (a * b ^ 2) *ᵥ ((b : K) • ξ)) = ξ ⬝ᵥ (hessM m a *ᵥ ξ) := by
    rw [hessM_sq, quad_scale]
    have : (b : K) * (b : K) * ((b⁻¹ : Kˣ) : K) ^ 2 = 1 := by
      have h := Units.mul_inv b
      calc (b : K) * (b : K) * ((b⁻¹ : Kˣ) : K) ^ 2
          = ((b : K) * ((b⁻¹ : Kˣ) : K)) ^ 2 := by ring
        _ = 1 := by rw [h, one_pow]
    rw [this, one_mul]
  unfold gaussF
  by_cases h : ∀ i, ξ i ∈ L
  · rw [if_pos h, if_pos (h1.2 h), h2]
  · rw [if_neg h, if_neg (fun h' => h (h1.1 h'))]
end Formalism.FourierDecayAlt.P.A6x7.Hess
