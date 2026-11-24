-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.up_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:31:25.763371+00:00
-- url     : https://prove2.me/submissions/79578896-8a2a-4994-bb3f-7e7dae0fec28

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

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
theorem _root_.solution (P : M.Par) {l l' : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hl' : l' ∈ Icc 1 (P.k - 1)) {π σ : M.Ty P}
    (h : M.Up P l π σ) (h' : M.Up P l' π σ) : l = l' := by
  by_contra hne
  have a := Finset.mem_Icc.1 hl
  have e1 := h ⟨l - 1, by omega⟩
  have e2 := h' ⟨l - 1, by omega⟩
  simp only at e1 e2
  split_ifs at e1 e2 <;> omega
end Formalism.FourierDecayAlt.P.NFx2
