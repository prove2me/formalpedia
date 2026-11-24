-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_antidiagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:33.073835+00:00
-- url     : https://prove2.me/submissions/469a0e3c-dbfb-4c07-bd2e-f2292e00b7b7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv_super
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_antiW_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_mul_antiW
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_antiW_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_simpleLow_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_simpleUp_succ

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.StabAntidiag := by
  intro s u t hu ht
  have hi := ut_inv hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [c2x2_mul_antiW, c2x2_antiW_mul]
    exact hi.1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [c2x2_mul_antiW, c2x2_antiW_mul]
    exact hi.2 _
  · calc C2.antiW s * u⁻¹ * C2.antiW s * (t • C2.antiW s) * u
        = t • (C2.antiW s * u⁻¹ * (C2.antiW s * C2.antiW s) * u) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = t • C2.antiW s := by
          rw [c2x2_antiW_sq, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (ut_unit hu),
            Matrix.mul_one]
  · rcases s with _ | n
    · simp [C2.simpleLow, C2.simpleUp]
    · rw [c2x2_simpleLow_succ, c2x2_simpleUp_succ]
      have e1 : ∀ a : Fin n, (C2.antiW (n + 1) * u⁻¹ * C2.antiW (n + 1)) a.succ a.castSucc =
          -u a.rev.castSucc a.rev.succ := by
        intro a
        rw [c2x2_mul_antiW, c2x2_antiW_mul, Fin.rev_succ, Fin.rev_castSucc]
        have := ut_inv_super hu a.rev.castSucc (by simp only [Fin.coe_castSucc]; exact Nat.succ_lt_succ a.rev.isLt)
        exact this
      simp only [e1]
      rw [Finset.sum_neg_distrib]
      have e2 : ∑ a : Fin n, u a.rev.castSucc a.rev.succ = ∑ a : Fin n, u a.castSucc a.succ :=
        Equiv.sum_comp Fin.revPerm (fun a => u a.castSucc a.succ)
      rw [e2]; ring
end Formalism.FourierDecayAlt.P
