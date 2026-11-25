-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.Rst_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:58:53.079894+00:00
-- url     : https://prove2.me/submissions/d94ad52d-de03-4478-9f68-6677cabf0e33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_Hst_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_Rst_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gram_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_pow_eq_zero_of_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_rhoOf_sub_one_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_blk_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_ut_sub_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_map_frame
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r}
    (hpos : C2.PosPt k r z z' γ) {ρ : B.Mat k r} (hρ : ρ ∈ C2.Rst k r z z' γ) :
    (ρ - 1) ^ (2 * r + k + 1) = 0 := by
  have hγ : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hpos.1
  obtain ⟨hs, hs'⟩ := (Hst_iff hγ ρ).mp hρ.1
  have hU := (unipotent_map_frame k r z hstd.2.1).1 ρ hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  have e := Rst_rho hstd hpos hρ
  have hΦ : (PhiH k r z z' γ ρ - 1) ^ (r + 1) = 0 := by
    unfold PhiH
    have e1 : Matrix.fromBlocks (C2.uMap k r z ρ) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ)) - 1 =
        Matrix.fromBlocks (C2.uMap k r z ρ - 1) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ) - 1) := by
      rw [← Matrix.fromBlocks_one]
      ext (i | i) (j | j) <;> simp [Matrix.one_apply]
    rw [e1, blk_pow, ut_sub_pow hU.2.1, ut_sub_pow hU'.2.1, Matrix.fromBlocks_zero]
  rw [e, rhoOf_sub_one_pow _ _ _ (gram_det z z' γ hstd hpos),
    HermitianProjections.pow_eq_zero_of_le hΦ (by omega), Matrix.mul_zero, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
