-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.upper_left_tail_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:13.640167+00:00
-- url     : https://prove2.me/submissions/59384a22-19db-4240-bfc5-c3a3f5178cd9

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_raises
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_sum_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_mul_projection
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_stepB
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_stepC
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_stepE

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
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {Y : ℂ} (hY : Reg P Y)
    (τ : M.Ty P) :
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y) * Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y *
        proj κ τ =
      L.GGi * (∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ)) +
        L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ) := by
  rw [mul_assoc, mul_assoc, lower_sum_mul_projection, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ j ∈ Icc 1 (P.k - 1),
      Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y * (M.xEx P {j} τ Y • (SS j * proj κ τ))) =
        L.GGi * ∑ l ∈ Icc 1 (P.k - 1),
          (M.xEx P {j} τ Y * ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ * sn_hsh P l j τ Y) •
            (star (SS l) * SS j * proj κ τ) := by
    intro j hj
    rw [mul_smul_comm, sn_stepB (sn_raises hc) hj, smul_smul, mul_smul_comm, sn_stepC hc hs, ← mul_smul_comm,
      Finset.smul_sum]
    congr 1; refine Finset.sum_congr rfl fun l _ => ?_; rw [smul_smul]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← mul_add]
  congr 1
  rw [Finset.sum_congr rfl fun j hj => sn_stepE hc hY hj τ, Finset.sum_add_distrib, sn_sum_swap]
  congr 1
  unfold Q.NFData.S4
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only
  rw [mul_assoc _ (κ _), kap_mul_pj, mul_smul_comm, mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
