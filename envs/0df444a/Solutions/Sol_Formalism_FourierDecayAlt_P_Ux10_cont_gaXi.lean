-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.cont_gaXi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:38:58.298827+00:00
-- url     : https://prove2.me/submissions/9cb14066-c70d-4942-968d-6a9d8215f4b5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_detZj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_det_hMat_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Rn_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_Rn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ZjH
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_detZj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_detZj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_strictUpper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromRows
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromCols
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_lowW

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
variable {X : Type*} [TopologicalSpace X]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {k p s ρ : ℕ} (hR : RadicalParam) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Z : G.Mat s) (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) :
    Continuous fun ξ : Xi k p s ρ σ => gaXi k ρ σ d ξ Z γ := by
  have h1 : Continuous fun ξ : Xi k p s ρ σ => (Rn k (p + s) ρ ξ.1.1)⁻¹ :=
    cont_inv ((cont_Rn k (p + s) ρ).comp (continuous_fst.comp continuous_fst)) fun ξ =>
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (Rn_mem hR k (p + s) ρ ξ.1.1)).ne_zero
  have h2 : Continuous fun ξ : Xi k p s ρ σ => (ZjH σ d ξ.2 Z)ᴴ⁻¹ := by
    refine cont_inv (((cont_ZjH σ d Z).comp continuous_snd).matrix_conjTranspose) fun ξ => ?_
    rw [Matrix.det_conjTranspose, detZj]
    exact star_ne_zero.2 (mul_ne_zero (det_hMat_ne σ d hd) hZ)
  have h3 : Continuous fun ξ : Xi k p s ρ σ => ZjH σ d ξ.2 Z := (cont_ZjH σ d Z).comp continuous_snd
  have h4 : Continuous fun ξ : Xi k p s ρ σ => Rn k (p + s) ρ ξ.1.2 :=
    (cont_Rn k (p + s) ρ).comp (continuous_snd.comp continuous_fst)
  unfold gaXi mMap blk3
  fun_prop
end Formalism.FourierDecayAlt.P.Ux10
