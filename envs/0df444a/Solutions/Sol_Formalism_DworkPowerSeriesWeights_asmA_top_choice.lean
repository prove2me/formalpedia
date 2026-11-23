-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_top_choice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:31.987382+00:00
-- url     : https://prove2.me/submissions/26566ddd-4303-4e1a-a12c-eae8cdcadf8c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (cap h : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (hh : ∀ e, 0 ≤ h e) (hsum : Summable h) (R : Finset ℕ) (D : ℕ∞)
    (hRodd : ∀ j ∈ R, Odd j)
    (hmin : ∀ e : ℕ, Odd e → (e : ℕ∞) < D → min (A / (l : ℝ) ^ e) (cap e) ≤ h e)
    (hD : ∀ e : ℕ, D = e → A / (l : ℝ) ^ e ≤ h e) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, D = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      A * ε + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ε) 0 ≤ ∑' e, h e := by
  classical
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hcapj : ∀ j : ℕ, Odd j → (j : ℕ∞) < D → ¬ (A / (l : ℝ) ^ j ≤ h j) → cap j ≤ h j :=
    fun j hj hjD hn => (min_le_iff.mp (hmin j hj hjD)).resolve_left hn
  by_cases hS : ∃ e : ℕ, Odd e ∧ (e : ℕ∞) < D ∧ A / (l : ℝ) ^ e ≤ h e
  · have hTs := Nat.find_spec hS
    refine ⟨((l : ℝ) ^ Nat.find hS)⁻¹, by positivity, ?_, ?_⟩
    · intro e he
      have hlt : (Nat.find hS : ℕ∞) < (e : ℕ∞) := lt_of_lt_of_eq hTs.2.1 he
      have hle : Nat.find hS ≤ e := le_of_lt (ENat.coe_lt_coe.mp hlt)
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hl1 hle)
    · apply asmA_top_core l hl A cap h hcap hh hsum R (Nat.find hS) hTs.2.2
      intro j hj hjT
      have hjD : (j : ℕ∞) < D := lt_trans (ENat.coe_lt_coe.mpr hjT) hTs.2.1
      exact hcapj j (hRodd j hj) hjD
        (fun hle => Nat.find_min hS hjT ⟨hRodd j hj, hjD, hle⟩)
  · push_neg at hS
    have hcapR : ∀ j ∈ R, (j : ℕ∞) < D → cap j ≤ h j := fun j hj hjD =>
      hcapj j (hRodd j hj) hjD (not_le.mpr (hS j (hRodd j hj) hjD))
    by_cases hDt : D = ⊤
    · subst hDt
      refine ⟨0, le_rfl, fun e he => absurd he (ENat.top_ne_coe e), ?_⟩
      calc A * 0 + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * 0) 0 = ∑ j ∈ R, cap j := by simp
        _ ≤ ∑ j ∈ R, h j := Finset.sum_le_sum fun j hj => hcapR j hj (ENat.coe_lt_top j)
        _ ≤ ∑' e, h e := Summable.sum_le_tsum R (fun i _ => hh i) hsum
    · obtain ⟨e0, rfl⟩ := ENat.ne_top_iff_exists.mp hDt
      refine ⟨((l : ℝ) ^ e0)⁻¹, by positivity, fun e he => ?_, ?_⟩
      · have : e0 = e := by exact_mod_cast he
        rw [this]
      · exact asmA_top_core l hl A cap h hcap hh hsum R e0 (hD e0 rfl)
          (fun j hj hjT => hcapR j hj (ENat.coe_lt_coe.mpr hjT))
end Formalism.DworkPowerSeriesWeights
