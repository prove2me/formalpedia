-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:34.006127+00:00
-- url     : https://prove2.me/submissions/52690c9f-3979-4059-a8dc-4056df2a0e5f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_23
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_skew_entry_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (x : RC k j ρ) : ‖x‖ ≤ B.gN (Rn k j ρ x) := by
  have h0 : 0 ≤ B.gN (Rn k j ρ x) := Real.sqrt_nonneg _
  rw [norm_prod_le_iff, norm_prod_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun b => ?_
    rw [← Rn_23]
    exact entry_le_gN _ _ _
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun u => ?_
    have h := skew_entry_le x u.1.1 u.1.2
    have hu : skewOf x.2 u.1.1 u.1.2 = x.2.1 u := by
      have h1 : u.1.1 < u.1.2 := u.2
      have h2 : ¬ u.1.2 < u.1.1 := not_lt.mpr h1.le
      have h3 : u.1.1 ≠ u.1.2 := ne_of_lt h1
      simp [skewOf, G.strictUpper, Matrix.conjTranspose_apply, h1, h2, h3]
    rwa [hu] at h
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    have h := skew_entry_le x i i
    have hu : skewOf x.2 i i = Complex.I * ((x.2.2 i : ℝ) : ℂ) := by
      simp [skewOf, G.strictUpper, Matrix.conjTranspose_apply]
    rw [hu, norm_mul, Complex.norm_I, one_mul, Complex.norm_real] at h
    exact h
end Formalism.FourierDecayAlt.P.Ux6
