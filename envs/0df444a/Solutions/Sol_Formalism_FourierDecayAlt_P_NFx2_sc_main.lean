-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:35.252799+00:00
-- url     : https://prove2.me/submissions/2804d67c-faaa-4054-b7be-b26a9ed645b8

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_Nkap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_Nskap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_nabSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_nabsSS

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
theorem _root_.solution : Formalism.FourierDecayAlt.NF.SConn := by
  intro P A _ _ _ L0 QQ κ b SS _hP h hF hR hSS
  refine ⟨sc_LL h hF, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
    ⟨h.1, rfl, h.2.1⟩, ⟨H_kstar h, ?_, fun l g hg => hSS l g hg, hR, fun l hl => ⟨sc_nabSS h hF hR hSS hl,
      sc_nabsSS h hF hR hSS hl⟩⟩, fun Y => ⟨connection_lower_left_eq h hF hR Y, connection_upper_right_eq h hF hR Y, diagonal_entry_hypothesis h Y⟩⟩
  intro f g hg
  rcases hg with hg | hg
  · exact H_kops h f g (sc_ops_of_fns L0 hg)
  · rcases hg with rfl | hg
    · exact sc_Nkap h b f
    · rw [Set.mem_singleton_iff] at hg; subst hg; exact sc_Nskap h b f
end Formalism.FourierDecayAlt.P.NFx2
