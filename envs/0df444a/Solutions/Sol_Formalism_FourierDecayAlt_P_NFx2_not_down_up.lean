-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.not_down_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:27.228751+00:00
-- url     : https://prove2.me/submissions/2bc838f2-9b14-456d-82eb-6a7e6c4c356b

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
theorem _root_.solution (P : M.Par) {i j l : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hl : l ∈ Icc 1 (P.k - 1)) {τ μ σ : M.Ty P} (h1 : M.Up P i μ τ) (h2 : M.Up P j μ σ) (h3 : M.Up P l τ σ) : False := by
  have a := Finset.mem_Icc.1 hi; have b := Finset.mem_Icc.1 hj; have c := Finset.mem_Icc.1 hl
  have e1 := h1 ⟨l - 1, by omega⟩; have e2 := h2 ⟨l - 1, by omega⟩; have e3 := h3 ⟨l - 1, by omega⟩
  have f1 := h1 ⟨i - 1, by omega⟩; have f2 := h2 ⟨i - 1, by omega⟩; have f3 := h3 ⟨i - 1, by omega⟩
  have g1 := h1 ⟨j - 1, by omega⟩; have g2 := h2 ⟨j - 1, by omega⟩; have g3 := h3 ⟨j - 1, by omega⟩
  simp only at e1 e2 e3 f1 f2 f3 g1 g2 g3
  split_ifs at e1 e2 e3 f1 f2 f3 g1 g2 g3 <;> omega
end Formalism.FourierDecayAlt.P.NFx2
