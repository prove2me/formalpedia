-- Prove2me | solution 1 for Formalism.L2.LamCM.degree_delta_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:35.753294+00:00
-- url     : https://prove2.me/submissions/59953071-5885-45f4-b47d-6b4f693100a1

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_log_two_pi_le_two
import Theorems.Thm_Formalism_L2_LamCM_finrank_pos_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
private lemma mLine_deg_dual {K : Type} [Field K] [NumberField K] (L : MLine K) : L.dual.deg = - L.deg := by
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  ring
section cauchy
end cauchy
section loc
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
end loc
section galois
variable {K : Type} [Field K] [NumberField K]
end galois
end Formalism.L2.LamCM
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : DegDe0 := by
  unfold DegDe0
  intro K _ _ g abelian₂ ℓ de La logOm h
  unfold CMNumbers0 at h
  obtain ⟨-, -, -, hLa, hsum, hnd, hdd⟩ := h
  have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos_real K
  have hdeg : ∀ j, (ℓ j).deg = logOm / 2 * (Module.finrank ℚ K : ℝ) := fun j => by
    have e : (ℓ j).ndeg = (ℓ j).deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [← hnd j, e, div_mul_cancel₀ _ hd.ne']
  have hs : ∑ j, (ℓ j).deg = (g : ℝ) * (logOm / 2 * (Module.finrank ℚ K : ℝ)) := by
    simp [hdeg]
  have hdual : abelian₂.dual.ndeg = - abelian₂.ndeg := by
    have e1 : abelian₂.dual.ndeg = abelian₂.dual.deg / (Module.finrank ℚ K : ℝ) := rfl
    have e2 : abelian₂.ndeg = abelian₂.deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [e1, e2, mLine_deg_dual, neg_div]
  have hLamn : (g : ℝ) * (logOm / 2) - (g : ℝ) * Real.log La ≤ abelian₂.ndeg := by
    have e2 : abelian₂.ndeg = abelian₂.deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [e2, le_div_iff₀ hd]
    rw [hs] at hsum
    linarith
  have hg : (0:ℝ) ≤ g := Nat.cast_nonneg g
  have h1 : (g:ℝ) * Real.log (2 * Real.pi) ≤ (g:ℝ) * 2 := mul_le_mul_of_nonneg_left log_two_pi_le_two hg
  have h2 : (g:ℝ) * (-logOm) ≤ (g:ℝ) * |logOm| := mul_le_mul_of_nonneg_left (neg_le_abs logOm) hg
  have h3 : (0:ℝ) ≤ (g:ℝ) * |logOm| := mul_nonneg hg (abs_nonneg logOm)
  unfold pDeg
  rw [hdual] at hdd
  linarith
end Formalism.L2.LamCM
