-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.gaussAdm_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:09.893338+00:00
-- url     : https://prove2.me/submissions/5a10c4dc-3809-4242-aa8b-bd507d49ef38

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_hessM_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_quad_scale
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mem_mulLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



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
theorem _root_.solution (ψ : AddChar K ℂ) (L : AddSubgroup K) (m : ℕ) (a b : Kˣ)
    (hdet : IsUnit (hessM m a).det) (h : GaussAdm ψ L (hessM m a)) :
    GaussAdm ψ (mulLat (b : K) L) (hessM m (a * b ^ 2)) := by
  intro y hy
  have hy' : ∀ i, ((b : K) • y) i ∈ perp ψ L := by
    intro i l hl
    have := hy i ((b : K) * l) ((mem_mulLat b L l).2 hl)
    rw [← this]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h3 := h ((b : K) • y) hy'
  rw [← h3]
  congr 2
  have h4 : (hessM m (a * b ^ 2))⁻¹ = ((b : K) ^ 2) • (hessM m a)⁻¹ := by
    rw [hessM_sq]
    have := Matrix.inv_smul' (hessM m a) ((b⁻¹) ^ 2 : Kˣ) hdet
    rw [Units.smul_def, Units.smul_def] at this
    rw [Units.val_pow_eq_pow_val] at this
    rw [this]
    congr 1
  rw [h4]
  have h5 := quad_scale (hessM m a)⁻¹ (b : K) 1 y
  rw [one_smul] at h5
  rw [h5, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.A6x7.Hess
