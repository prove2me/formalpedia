-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_stepE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:16.315477+00:00
-- url     : https://prove2.me/submissions/2b063a11-7131-4b9b-a8c5-08f42eca3eb4

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ss_pj_none
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_raises
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_x_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_hsh_same
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_hsh_diff

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) {Y : ℂ} (hY : Reg P Y) {j : ℕ}
    (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    ∑ l ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y * ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ * sn_hsh P l j τ Y) •
        (star (SS l) * SS j * proj κ τ) =
      (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ) +
        ∑ l ∈ (Icc 1 (P.k - 1)).erase j, M.xEx P {l, j} τ Y • (star (SS l) * SS j * proj κ τ) := by
  by_cases hτ : ∃ τ', M.Up P j τ τ'
  · obtain ⟨τ', hU⟩ := hτ
    have hx := hY τ'
    rw [sn_x_up hj hU] at hx
    have ha : (Y + M.rho P τ j + 1) ≠ 0 := left_ne_zero_of_mul hx
    have hb : M.xEx P {j} τ Y ≠ 0 := right_ne_zero_of_mul hx
    rw [← Finset.add_sum_erase _ _ hj]
    congr 1
    · rw [sn_hsh_same]; congr 1; field_simp
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hlj : l ≠ j := Finset.ne_of_mem_erase hl
      rw [sn_hsh_diff hj hlj]; congr 1; field_simp
  · have h0 := ss_pj_none κ (sn_raises hc) hτ
    have z : ∀ l, star (SS l) * SS j * proj κ τ = 0 := fun l => by rw [mul_assoc, h0, mul_zero]
    simp [z]
end Formalism.FourierDecayAlt.P.NFx2
