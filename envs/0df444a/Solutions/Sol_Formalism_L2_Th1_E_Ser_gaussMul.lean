-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.gaussMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:46.782899+00:00
-- url     : https://prove2.me/submissions/4e8af98b-4ba2-41d2-b219-c6dbe16ee308

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_norm_sum_lt_one
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_mul

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
theorem _root_.solution {f g : K⟦X⟧} (hf : GaussOne f) (hg : GaussOne g) : GaussOne (f * g) := by
  classical
  obtain ⟨hfi, hfe⟩ := hf
  obtain ⟨hgi, hge⟩ := hg
  refine ⟨intS_mul hfi hgi, Nat.find hfe + Nat.find hge, ?_⟩
  set i := Nat.find hfe with hi
  set j := Nat.find hge with hj
  have hi1 : ‖coeff i f‖ = 1 := Nat.find_spec hfe
  have hj1 : ‖coeff j g‖ = 1 := Nat.find_spec hge
  have hilt : ∀ m, m < i → ‖coeff m f‖ < 1 := fun m hm =>
    lt_of_le_of_ne (hfi m) (Nat.find_min hfe hm)
  have hjlt : ∀ m, m < j → ‖coeff m g‖ < 1 := fun m hm =>
    lt_of_le_of_ne (hgi m) (Nat.find_min hge hm)
  rw [coeff_mul, ← Finset.add_sum_erase _ _ (show (i, j) ∈ antidiagonal (i + j) by simp)]
  have hmain : ‖coeff i f * coeff j g‖ = 1 := by rw [norm_mul, hi1, hj1, one_mul]
  have hrest : ‖∑ p ∈ (antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g‖ < 1 := by
    refine norm_sum_lt_one _ _ (fun p hp => ?_)
    rw [Finset.mem_erase, HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [norm_mul]
    have hcase : p.1 < i ∨ p.2 < j := by
      by_contra hcon
      push Not at hcon
      apply hp1
      ext
      · simp only; omega
      · simp only; omega
    rcases hcase with hc | hc
    · calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖ ≤ ‖coeff p.1 f‖ * 1 :=
            mul_le_mul_of_nonneg_left (hgi _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hilt _ hc
    · calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖ ≤ 1 * ‖coeff p.2 g‖ :=
            mul_le_mul_of_nonneg_right (hfi _) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hjlt _ hc
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hmain]; exact hrest.ne'), hmain]
  exact max_eq_left hrest.le
end Formalism.L2.Th1.E.Ser
