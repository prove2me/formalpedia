-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:50:19.137298+00:00
-- url     : https://prove2.me/submissions/fa2327c2-b675-4594-ba1d-015517550078

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_eq_of_rblocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_quantum_determinant_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_diagonal_shift_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_regular_pairs_infinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_decomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_upper_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_norm_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_wC

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
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution : Formalism.FourierDecayAlt.NF.SNorm := by
  intro _ _ _ hNF hRP hWE P A _ _ _ L0 QQ κ b SS L hP hS _ _ _ hExt _ _ hst hc hQ
  have hGG : L.GG = L0.GG := hExt.2.2.2.2.2.2.2.2.2.2.1
  have h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y := fun Y => by rw [diagonal_entry_hypothesis hS, hGG]
  have h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y := fun Y => by
    rw [(hQ Y).1]; simp [Q.NFData.QQ, Q.NFData.x, xA]
  have h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y := fun Y => by
    rw [(hQ Y).2]; simp [Q.NFData.QQ, Q.NFData.x, xA]
  have hD3 := quantum_determinant_relation hS
  have hD4 := lower_diagonal_shift_relation hS
  have hpoly := H_poly hS 0 0
  refine ⟨fun l hl => ?_, fun Y => ?_⟩
  · show star (SS l) * SS l = κ fun ρ => ((M.Nrm P l ρ : ℝ) : ℂ)
    exact eq_of_rblocks κ fun τ => by
      rw [sn_norm_blk hc hst hP hNF hRP h22 h21 h12 hD3 hD4 hpoly hl τ, kap_mul_pj]
  · refine isPF_eq hpoly polynomial_upper_left (regular_pairs_infinite P) ?_ Y
    rintro Z ⟨hZ, hZ1⟩
    refine eq_of_rblocks κ fun τ => ?_
    have hsum : ∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Z / (Z + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ) =
        (∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Z / (Z + M.rho P τ j + 1) * ((M.Nrm P j τ : ℝ) : ℂ)) • proj κ τ := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [sn_norm_blk hc hst hP hNF hRP h22 h21 h12 hD3 hD4 hpoly hj τ, smul_smul]
    rw [sn_core hc hst h22 h21 h12 hD3 hD4 hZ hZ1 τ, upper_left_decomposition, hsum, add_mul, add_mul, mul_assoc L.GGi (κ _),
      kap_mul_pj, sn_wC hWE hP τ (hZ1 τ), add_smul, mul_add, mul_smul_comm, mul_assoc L.GGi]
    noncomm_ring
end Formalism.FourierDecayAlt.P.NFx2
