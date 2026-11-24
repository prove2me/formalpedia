-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.oneUnit_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:54.774043+00:00
-- url     : https://prove2.me/submissions/85aa386f-a512-4f0d-90cd-d00e78d46a01

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_norm_sum_le_one
import Theorems.Thm_Formalism_L2_Th1_E_Ser_norm_mul_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution {f g : K⟦X⟧} (hf : OneUnit f) (h : f * g = 1) : OneUnit g := by
  have h0 : constantCoeff g = 1 := by
    have := congrArg (constantCoeff (R := K)) h
    rwa [map_mul, hf.1, one_mul, map_one] at this
  refine ⟨h0, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_eq_constantCoeff_apply, h0]; simp
    · have h1 : coeff n (f * g) = 0 := by
        rw [h, coeff_one, if_neg hn.ne']
      rw [coeff_mul, ← Finset.add_sum_erase _ _ (show (0, n) ∈ antidiagonal n by simp)] at h1
      simp only [coeff_zero_eq_constantCoeff_apply, hf.1, one_mul] at h1
      rw [eq_neg_of_add_eq_zero_left h1, norm_neg]
      refine norm_sum_le_one _ _ (fun p hp => norm_mul_le_one (hf.2 _) (ih _ ?_))
      rw [Finset.mem_erase, HasAntidiagonal.mem_antidiagonal] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have : p.1 ≠ 0 := by
        intro h3
        apply hp1
        ext
        · exact h3
        · simp only; omega
      omega
end Formalism.L2.Th1.E.Ser
