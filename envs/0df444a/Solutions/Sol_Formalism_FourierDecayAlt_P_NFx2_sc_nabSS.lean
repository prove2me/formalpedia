-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_nabSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:12:03.442555+00:00
-- url     : https://prove2.me/submissions/ce697ceb-cee5-4832-b859-f38843d2bc33

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_eq_of_rblocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ss_pj_none
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_keyN
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_N_pc

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    nabDef L0 κ b * SS l = SS l * nabDef L0 κ b - L0.ζb * L0.GGi * SS l := by
  apply eq_of_rblocks κ
  intro ρ
  by_cases hex : ∃ ρ', M.Up P l ρ ρ'
  · obtain ⟨ρ', hu⟩ := hex
    have k := sc_keyN h hF hR hSS hl hu
    calc nabDef L0 κ b * SS l * proj κ ρ = nabDef L0 κ b * (SS l * proj κ ρ) := by rw [mul_assoc]
      _ = (SS l * proj κ ρ) * nabDef L0 κ b - L0.ζb * L0.GGi * (SS l * proj κ ρ) := by
        rw [← sub_eq_zero, show nabDef L0 κ b * (SS l * proj κ ρ) - ((SS l * proj κ ρ) * nabDef L0 κ b -
          L0.ζb * L0.GGi * (SS l * proj κ ρ)) = -((SS l * proj κ ρ) * nabDef L0 κ b - nabDef L0 κ b * (SS l * proj κ ρ) -
          (L0.ζb * L0.GGi) * (SS l * proj κ ρ)) by abel, k, neg_zero]
      _ = _ := by rw [mul_assoc (SS l), sc_N_pc h b ρ]; noncomm_ring
  · have h0 := ss_pj_none κ hR hex
    rw [mul_assoc, h0, mul_zero, sub_mul, mul_assoc, ← sc_N_pc h b ρ, ← mul_assoc, h0, zero_mul, mul_assoc, h0,
      mul_zero, sub_zero]
end Formalism.FourierDecayAlt.P.NFx2
