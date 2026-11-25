-- Prove2me | solution 1 for Formalism.LT.LTL.step_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:59.859788+00:00
-- url     : https://prove2.me/submissions/5ec8cb92-8855-4817-ba4c-7d209eeb1824

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_master
import Theorems.Thm_Formalism_LT_LTL_defect_divBy
import Theorems.Thm_Formalism_LT_LTL_norm_pi_sub_pow
import Theorems.Thm_Formalism_LT_LTL_coeff_corr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}
namespace Formalism.LT.LTL
theorem _root_.solution (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {N : ℕ} (hN : 1 ≤ N) {P : MvPowerSeries ι K} (h : Inv e e' a N P) :
    Inv e e' a (N + 1) (P + corr e e' π N P) ∧ Low (N + 1) (corr e e' π N P) := by
  have hπ0 : 0 < ‖π‖ := hS.2.2.1
  have hπ1 : ‖π‖ < 1 := hS.2.2.2.1
  have hnorm := norm_pi_sub_pow hπ0 hπ1 (r := N + 1) (by omega)
  have hne : π - π ^ (N + 1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; linarith
  have hlowc : Low (N + 1) (corr e e' π N P) := by
    intro d hd; rw [coeff_corr, if_neg (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hlowc⟩
  · rw [map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp),
      add_zero]
  · intro d
    rw [map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.2.1 d) ?_)
    rw [coeff_corr]
    split_ifs
    · rw [norm_div, hnorm]
      exact div_le_one_of_le₀ (defect_divBy hS he he' h.1 h.2.1 d) (norm_nonneg _)
    · simp
  · intro i
    rw [map_add, h.2.2.1 i, hlowc _ (by rw [Finsupp.degree_single]; omega), add_zero]
  · have hP'0 : MvPowerSeries.constantCoeff (P + corr e e' π N P) = 0 := by
      rw [map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp),
        add_zero]
    have hdiff : Low (N + 1) (P + corr e e' π N P - P) := by
      rw [add_sub_cancel_left]; exact hlowc
    intro d hd
    have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hP'0 h.1 hdiff d (by omega)
    rw [add_sub_cancel_left, coeff_corr] at hm
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
    · rw [if_neg (by omega), mul_zero, h.2.2.2 d hlt, sub_zero] at hm
      exact hm
    · rw [if_pos heq] at hm
      have : (π ^ (N + 1) - π) * (MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1))) =
          -MvPowerSeries.coeff d (Ldef e e' P) := by
        field_simp; ring
      linear_combination hm + this
end Formalism.LT.LTL
