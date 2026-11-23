-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.sumU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:28.973585+00:00
-- url     : https://prove2.me/submissions/bf402a13-a123-4f2f-af95-2db217abaa7a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_cells
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_part
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_lu_int
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) (n : ℕ) (f : Matrix (Fin n) (Fin n) K → ℂ)
    (hinv : ∀ u r : Matrix (Fin n) (Fin n) K, IsUpUni u → IsUpUni r → IsInt R r → f (u * r) = f u)
    (hfin : {q : upUniG K n ⧸ intSub R (upUniG K n) | f (sec_m (Quotient.out q)) ≠ 0}.Finite)
    {Λ : AddSubgroup K} (hΛ : IsLat Λ) (hΛinv : BInv Λ (fun y : Pr n → K => f (1 + EE y))) :
    ∑ᶠ q : upUniG K n ⧸ intSub R (upUniG K n), f (sec_m (Quotient.out q)) =
      bx R Λ (Pr n) (fun y => f (1 + EE y)) := by
  classical
  have hU : ∀ q : upUniG K n ⧸ intSub R (upUniG K n), IsUpUni (sec_m (Quotient.out q)) :=
    fun q => (Quotient.out q).2
  have key := bx_cells hD (Q := upUniG K n ⧸ intSub R (upUniG K n))
    (fun q => lu_co (sec_m (Quotient.out q))) (fun q => lu_M (sec_m (Quotient.out q)))
    (fun q => by rw [lu_det (hU q)]; exact isUnit_one) (lu_part R n) (fun y => f (1 + EE y))
    (fun q r hr => by
      show f (1 + EE (lu_co (sec_m (Quotient.out q)) + lu_M (sec_m (Quotient.out q)) *ᵥ r)) =
        f (1 + EE (lu_co (sec_m (Quotient.out q))))
      rw [← lu_mul (hU q), lu_eq (hU q)]
      exact hinv _ _ (hU q) (lu_up r) (lu_int hr))
    (by
      refine hfin.subset fun q hq => ?_
      have hq' : f (1 + EE (lu_co (sec_m (Quotient.out q)))) ≠ 0 := hq
      rwa [lu_eq (hU q)] at hq')
    hΛ hΛinv
  rw [key]
  refine finsum_congr fun q => ?_
  show _ = (modK R (lu_M (sec_m (Quotient.out q))).det : ℂ) *
    f (1 + EE (lu_co (sec_m (Quotient.out q))))
  rw [lu_det (hU q), modK_one, lu_eq (hU q)]
  simp
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
