-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.phase_fm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:54.802171+00:00
-- url     : https://prove2.me/submissions/ae991f6c-4340-4d30-8c98-93a57263ddda

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_cj_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_sUp_cj_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_sUp_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (p : lowW K S T × upUniG K S.sum)
    (hB : ∀ (j : Fin S.sum) (hj : j.val + 1 < S.sum),
      ((((dg S c j)⁻¹ : Kˣ) : K) * ((dg S c ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) j
          ⟨j.val + 1, hj⟩ ∈ R) :
    phase ψ (w := ((S, T * c) : Point K)) (fm S T c p) = phase ψ (w := ((S, T) : Point K)) p := by
  have h1 := sUp_cj_sub R (dg S c) ((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) hB
  have e1 : cj (dg S c) ((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) =
      (((fm S T c p).2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) := by
    show cj (dg S c) (p.2.1⁻¹) = (cj (dg S c) p.2.1)⁻¹
    rw [cj_inv]
  rw [e1, sUp_inv, sUp_inv] at h1
  show ψ (sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp (((fm S T c p).2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)) =
    ψ (sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp ((p.2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K))
  have e2 : sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp ((p.2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) =
      (sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp (((fm S T c p).2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)) +
      (-sUp (((fm S T c p).2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) -
        -sUp ((p.2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)) := by ring
  conv_rhs => rw [e2, AddChar.map_add_eq_mul, hψ _ h1, mul_one]
end Formalism.FourierDecayAlt.P.KernelScalingBack
