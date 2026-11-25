-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sizes_top_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:44:35.066606+00:00
-- url     : https://prove2.me/submissions/2f7e3e21-f964-4100-b56f-5577c870e49e

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_aux_statement_17
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_one_add_le_mul_one_add_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : SizesTop := by
  intro p s σ d hd hs A' hA'
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p s σ d hd
  set Cp := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  set K : ℝ := (1 + Cp) ^ 5 with hK
  have hK0 : 0 < K := by positivity
  have hps1 : (1 : ℝ) ≤ ((p + s : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p + s)
  have hps : (0 : ℝ) < 5 * ((p + s : ℕ) : ℝ) := by positivity
  set e := A' / (5 * ((p + s : ℕ) : ℝ)) with he
  have he0 : 0 ≤ e := div_nonneg hA' hps.le
  refine ⟨K ^ e, fun η CC => ?_⟩
  set m := mx (ZjH σ d η CC) with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hC η CC
  have up : ∀ {x : ℝ} {k : ℕ}, x ≤ C * m ^ k → x ≤ Cp * m ^ k := fun hx =>
    hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hm0 _))
  set X := wtH η * (1 + ‖CC‖) with hX
  have hX1 : 1 ≤ X := by
    have a1 : 1 ≤ 1 + ‖η.1.1‖ := by linarith [norm_nonneg η.1.1]
    have a2 : 1 ≤ 1 + ‖η.1.2‖ := by linarith [norm_nonneg η.1.2]
    have a3 : 1 ≤ 1 + ‖η.2.1‖ := by linarith [norm_nonneg η.2.1]
    have a4 : 1 ≤ 1 + ‖η.2.2‖ := by linarith [norm_nonneg η.2.2]
    have a5 : 1 ≤ 1 + ‖CC‖ := by linarith [norm_nonneg CC]
    rw [hX]
    unfold wtH
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 a2) a3) a4) a5
    exact this
  have hXle : X ≤ K * (1 + m) ^ (5 * p + 1) := by
    rw [hX]
    unfold wtH
    calc (1 + ‖η.1.1‖) * (1 + ‖η.1.2‖) * (1 + ‖η.2.1‖) * (1 + ‖η.2.2‖) * (1 + ‖CC‖)
        ≤ ((1 + Cp) * (1 + m) ^ p) * ((1 + Cp) * (1 + m) ^ p) * ((1 + Cp) * (1 + m) ^ p) *
            ((1 + Cp) * (1 + m) ^ p) * ((1 + Cp) * (1 + m) ^ (p + 1)) := by
          gcongr
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h1)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h2)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h3)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h4)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h5)
      _ = K * (1 + m) ^ (5 * p + 1) := by rw [hK]; ring
  have hexp : ((5 * p + 1 : ℕ) : ℝ) * e ≤ A' := by
    rw [he, mul_div_assoc', div_le_iff₀ hps]
    have : ((5 * p + 1 : ℕ) : ℝ) ≤ 5 * ((p + s : ℕ) : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    nlinarith
  have hXe : X ^ e ≤ K ^ e * (1 + m) ^ A' := by
    calc X ^ e ≤ (K * (1 + m) ^ (5 * p + 1)) ^ e := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ X) hXle he0
      _ = K ^ e * ((1 + m) ^ (5 * p + 1)) ^ e := Real.mul_rpow hK0.le (by positivity)
      _ = K ^ e * (1 + m) ^ (((5 * p + 1 : ℕ) : ℝ) * e) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ K ^ e * (1 + m) ^ A' :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 1 + m) hexp)
            (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < X) e),
    inv_mul_le_iff₀ (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + m) A')]
  linarith [mul_comm ((1 + m) ^ A') (K ^ e)]
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.Ux5
