-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:52.259097+00:00
-- url     : https://prove2.me/submissions/04be96fe-d471-4dcc-b627-b56ef4a9b1ce

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_skew_hpart1
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_skew_hpart2
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_hpart1
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_hpart2
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_rdV_eq
import Theorems.Thm_Formalism_REAL_rdV_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (l : Fin r) (D : Set (Mx k r)) (f : Mx k r → E) (hR : RightEq k r z l.castSucc D f)
    (g : Mx k r) (hg : g ∈ Glev k r l.castSucc ∩ D) (Z : Mx k r) (hZ : Pat k r l Z) :
    RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g =
      (ell k r z Z + star (ell k r z (dag k r Z))) • f g := by
  have hP := skew_hpart1 Z
  have hQ := skew_hpart2 Z
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
    try ring
  have hZ1 : Z = hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
    unfold hpart1 hpart2
    rw [smul_smul, hI]
    module
  have hZ2 : dag k r Z = -hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
    conv_lhs => rw [hZ1]
    rw [dag_add, dag_smul, hP, hQ, Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  have hE : ell k r z Z = ell k r z (hpart1 (Hpk k r) Z) + Complex.I * ell k r z (hpart2 (Hpk k r) Z) := by
    conv_lhs => rw [hZ1]
    rw [ell_add, ell_smul]
  have hE2 : ell k r z (dag k r Z) =
      -ell k r z (hpart1 (Hpk k r) Z) + Complex.I * ell k r z (hpart2 (Hpk k r) Z) := by
    rw [hZ2, show -hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z =
      (-1 : ℂ) • hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z by rw [neg_one_smul],
      ell_add, ell_smul, ell_smul]
    ring
  rw [rdV_eq z hz l D f hR g hg _ (pat_hpart1 hZ) hP, rdV_eq z hz l D f hR g hg _ (pat_hpart2 hZ) hQ,
    hE, hE2, smul_smul, ← add_smul]
  congr 1
  rw [Complex.star_def]
  simp only [map_add, map_mul, map_neg, Complex.conj_I]
  ring
end Formalism.FourierDecayAlt.Q.QRR
