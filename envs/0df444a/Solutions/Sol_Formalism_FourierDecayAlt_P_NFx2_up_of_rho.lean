-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.up_of_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:48.400312+00:00
-- url     : https://prove2.me/submissions/02b42a85-bb18-40f6-9561-d179cbb4c4a7

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
theorem _root_.solution (P : M.Par) {l : ℕ} {π π' : M.Ty P}
    (h : ∀ i ∈ Icc 1 (P.k - 1), M.rho P π' i = M.rho P π i + if i = l then 1 else 0) : M.Up P l π π' := by
  intro i
  have := h ((i : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  rw [rho_succ, rho_succ] at this
  split_ifs at this with hl
  · simp only [hl, if_true]; exact_mod_cast (by linarith : ((((π' i : Fin _) : ℕ) : ℝ)) = (((π i : Fin _) : ℕ) : ℝ) + 1)
  · simp only [hl, if_false, add_zero]; exact_mod_cast (by linarith : ((((π' i : Fin _) : ℕ) : ℝ)) = (((π i : Fin _) : ℕ) : ℝ))
end Formalism.FourierDecayAlt.P.NFx2
