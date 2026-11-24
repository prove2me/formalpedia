-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.ty_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:43:55.266296+00:00
-- url     : https://prove2.me/submissions/e544889d-bd5a-4d75-961c-a3bacfc8a840

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_rho_succ

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
open Formalism.FourierDecayAlt.M
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (P : M.Par) {π π' : M.Ty P} (h : ∀ i ∈ Icc 1 (P.k - 1), M.rho P π i = M.rho P π' i) : π = π' := by
  funext i; apply Fin.ext
  have := h ((i : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  rw [rho_succ, rho_succ] at this
  exact_mod_cast add_left_cancel this
end Formalism.FourierDecayAlt.P.NFx2
