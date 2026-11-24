-- Prove2me | solution 1 for Formalism.L2.Th1.E.KernelPtInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:46.229062+00:00
-- url     : https://prove2.me/submissions/30e298ec-a7cd-4a2b-806a-cac998675831

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_int_mul_mem
import Theorems.Thm_Formalism_L2_Th1_E_Tor_omegaK_sq
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Tor
namespace Formalism.L2.Th1.E
theorem _root_.solution (hI : PtOfInt) : KernelPtInt := by
  intro d L hd hCM l _ ι hW a b t hαt hl ht
  have hn0 : a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) ≠ 0 := fun h => hl (h ▸ dvd_zero _)
  have hq : ((((d : ℤ) + 1) / 4 : ℤ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℤ) + 1 = 4 * k := ⟨((d : ℤ) + 1) / 4, by omega⟩
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    have h4 : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
    rw [h4]
    ring
  have hnt : ((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) : ℤ) : ℂ) * t ∈ L.lattice := by
    have e : ((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) : ℤ) : ℂ) * t =
        ((a + b : ℤ) : ℂ) * (((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t) -
          (b : ℂ) * (Formalism.L2.Th1.CM.omegaK d * (((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t)) := by
      push_cast
      rw [hq]
      linear_combination ((b : ℂ) ^ 2 * t) * omegaK_sq d
    rw [e]
    exact sub_mem (int_mul_mem L _ hαt) (int_mul_mem L _ (hCM _ hαt))
  refine hI l L ι hW t (a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs
    (Int.natAbs_pos.2 hn0) (fun h => hl (Int.natCast_dvd.2 h)) ?_ ht
  have e2 : (((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs : ℕ) : ℂ) =
      (((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs : ℤ) : ℂ) := by
    simp
  rw [e2]
  rcases Int.natAbs_eq (a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)) with h | h
  · rw [← h]
    exact hnt
  · have h' : (((a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)).natAbs : ℤ)) =
        -(a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4)) := by omega
    rw [h', Int.cast_neg, neg_mul]
    exact neg_mem hnt
end Formalism.L2.Th1.E
