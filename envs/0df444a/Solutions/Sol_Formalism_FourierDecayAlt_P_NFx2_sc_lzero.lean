-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_lzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:21:11.319804+00:00
-- url     : https://prove2.me/submissions/b12a6075-7100-4fd4-9346-7089b64c078c

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : Reg P Y)
    {ρ ρ' : M.Ty P} (hne : ρ' ≠ ρ) (hn : ∀ l ∈ Icc 1 (P.k - 1), ¬ M.Up P l ρ ρ') :
    proj κ ρ' * lA L0 QQ κ Y * proj κ ρ = 0 := by
  have := hF Y hY ρ ρ'
  rw [if_neg hne, zero_add, Finset.sum_eq_zero] at this
  · exact this
  · intro l hl; rw [if_neg (hn l hl)]
end Formalism.FourierDecayAlt.P.NFx2
