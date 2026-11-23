-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.characterMean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:29.792869+00:00
-- url     : https://prove2.me/submissions/388bc7db-f02b-40ef-8ce7-168a4c1a5490

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_sum_reps_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_reps_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.CharMean := by
  intro K _ ψ L₁ L₂ S hle hS a ha
  have hc : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 (reps_nonempty hS)).ne'
  split_ifs with h
  · have : ∑ σ ∈ S, ψ (a * σ) = ∑ σ ∈ S, (1 : ℂ) :=
      Finset.sum_congr rfl fun σ hσ => h σ (hS.1 σ hσ)
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc]
  · have h' : ∃ l ∈ L₂, ψ (a * l) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact h hcon
    obtain ⟨l₀, hl₀, hne⟩ := h'
    rw [sum_reps_eq_zero hle hS (fun x => ψ (a * x)) ?_ ha hl₀ hne, mul_zero]
    intro x _ y _
    show ψ (a * (x + y)) = ψ (a * x) * ψ (a * y)
    rw [mul_add, AddChar.map_add_eq_mul]
end Formalism.FourierDecayAlt.P
