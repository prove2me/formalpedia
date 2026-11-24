-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_upper_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:50.83946+00:00
-- url     : https://prove2.me/submissions/940eddea-72ae-4156-b9b5-26fc560bdfc3

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_cpoly
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_real_infinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_isPF_xA
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_isPF_xEx
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_constant_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_real
import Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) (Y : ℂ) :
    QQ Y 0 1 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by
  have hpf : IsPF fun Y => (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by
    simp_rw [connection_upper_right_entry, connection_raising_constant_eq]
    refine isPF_add (isPF_mul (isPF_mul (isPF_const _) (sc_isPF_xA κ))
      (isPF_sub (isPF_const _) ?_)) (isPF_sum _ fun l _ => isPF_mul (sc_isPF_xEx κ {l}) (isPF_const _))
    have := isPF_cpoly (A := A) (Polynomial.X - Polynomial.C (1 / 2)) (L0.ζ * L0.GGi)
    simpa using this
  exact isPF_eq (H_poly h 0 1) hpf real_infinite (fun Y hY => connection_upper_right_real h hF hR hY) Y
end Formalism.FourierDecayAlt.P.NFx2
