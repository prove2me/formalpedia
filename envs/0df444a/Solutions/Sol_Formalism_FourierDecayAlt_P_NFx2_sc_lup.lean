-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_lup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:21:10.160504+00:00
-- url     : https://prove2.me/submissions/560e4539-0df0-4673-afb8-88a86607672f

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_idx

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
theorem _root_.solution {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : Reg P Y) {l : ℕ}
    (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') :
    proj κ ρ' * lA L0 QQ κ Y * proj κ ρ = (Y + (M.rho P ρ l : ℂ) + 1)⁻¹ • (L0.GGi * SS l * proj κ ρ) := by
  have := hF Y hY ρ ρ'
  rw [if_neg (fun e => up_ne P hl hu e.symm), zero_add, Finset.sum_eq_single l] at this
  · rw [this, if_pos hu]
  · intro j hj hjl; rw [if_neg (fun hu' => hjl (up_idx P hj hl hu' hu))]
  · intro h; exact absurd hl h
end Formalism.FourierDecayAlt.P.NFx2
