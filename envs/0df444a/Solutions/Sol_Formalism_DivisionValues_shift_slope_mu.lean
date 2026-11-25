-- Prove2me | solution 1 for Formalism.DivisionValues.shift_slope_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:28:46.49588+00:00
-- url     : https://prove2.me/submissions/7773252f-38ac-4fef-aa0e-5e606a0eaba4

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_index_formula
import Theorems.Thm_Formalism_DivisionValues_mu_log_conductor
import Theorems.Thm_Formalism_DivisionValues_shift_lw_pos
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_covolume_via_basis
import Theorems.Thm_Formalism_DivisionValues_idxLcv_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : ShiftMu := by
  intro K _ _ _ _ d X hX N N' hN hN' σ hσ
  obtain ⟨hfin, hlcv⟩ := idxLcv_of covolume_via_basis K d X hX N N' hN hN'
  have key : ∀ w, lw w * (idx w N N' : ℝ) = -(d : ℝ) * (lw w * (σ w : ℝ)) := fun w => by
    rw [shift_index_formula K d N N' hN w (σ w) (hσ w)]
    push_cast
    ring
  have hsum : ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w N N' : ℝ) =
      -(d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) := by
    simp_rw [key]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp
    · have hd' : (-(d : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith
      have hfs : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (σ w : ℝ)).Finite := by
        refine hfin.subset (fun w hw => ?_)
        simp only [Function.mem_support] at hw ⊢
        rw [key]
        exact mul_ne_zero hd' hw
      exact (mul_finsum _ _).symm
  have hL : lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) := by
    rw [hlcv, hsum]
    ring
  refine ⟨hL, fun hd => ⟨?_, ?_⟩⟩
  · have hd' : (-(d : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      linarith
    refine hfin.subset (fun w hw => ?_)
    simp only [Function.mem_support] at hw ⊢
    rw [key]
    refine mul_ne_zero hd' (mul_ne_zero (shift_lw_pos w).ne' ?_)
    exact_mod_cast hw
  · rw [mu_log_conductor K d hd X hX N' hN', mu_log_conductor K d hd X hX N hN, hL]
    have : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
    ring
end Formalism.DivisionValues
