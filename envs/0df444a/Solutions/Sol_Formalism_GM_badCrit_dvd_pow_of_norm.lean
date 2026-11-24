-- Prove2me | solution 1 for Formalism.GM.badCrit_dvd_pow_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:11.045528+00:00
-- url     : https://prove2.me/submissions/f1351991-18a0-4de3-9bfb-1674708ec852

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
namespace Formalism.GM
theorem _root_.solution {p : ℕ} [Fact p.Prime] {a : ℤ_[p]} {E : ℕ}
    (h : (p : ℝ) ^ (-(E : ℤ)) ≤ ‖a‖) : a ∣ (p : ℤ_[p]) ^ E := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact absurd h (not_le.2 (by positivity))
  rw [PadicInt.norm_eq_zpow_neg_valuation ha, zpow_le_zpow_iff_right₀ hp, neg_le_neg_iff] at h
  have hv : a.valuation ≤ E := by exact_mod_cast h
  have hsp := PadicInt.unitCoeff_spec ha
  set u := PadicInt.unitCoeff ha
  have hu : (u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by simp
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (E - a.valuation), ?_⟩
  calc (p : ℤ_[p]) ^ E = (p : ℤ_[p]) ^ a.valuation * (p : ℤ_[p]) ^ (E - a.valuation) := by
        rw [← pow_add, Nat.add_sub_cancel' hv]
    _ = ((u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) *
          (p : ℤ_[p]) ^ a.valuation * (p : ℤ_[p]) ^ (E - a.valuation) := by rw [hu, one_mul]
    _ = ((u : ℤ_[p]) * (p : ℤ_[p]) ^ a.valuation) *
          (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (E - a.valuation)) := by ring
    _ = _ := by rw [← hsp]
end Formalism.GM
