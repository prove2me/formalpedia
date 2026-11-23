-- Prove2me | solution 1 for Formalism.REAL.half_sum_roots_standard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:00.361579+00:00
-- url     : https://prove2.me/submissions/dd36af35-885a-46ce-922d-ee931d0e3fd2

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : RhoStd := by
  intro n ε a
  unfold rhoC rhoN
  have k1 : #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} = #{b | a < b} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : a < b <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k2 : #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = #{b | b < a} := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h1 : b < a <;> by_cases h2 : ε b = ε a <;> simp [h1, h2]
  have k3 : #{b | a < b} = n - 1 - (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext b; simp]
    exact Fin.card_Ioi a
  have k4 : #{b | b < a} = (a : ℕ) := by
    rw [show (univ.filter fun b : Fin n => b < a) = Finset.Iio a by ext b; simp]
    exact Fin.card_Iio a
  have ha := a.isLt
  have r1 : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℝ)
      + ((a : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show #{b | a < b ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a} + (a : ℕ) + 1 = n by omega)
  have r2 : ((#{b | b < a ∧ ε b = ε a} : ℕ) : ℝ) + ((#{b | b < a ∧ ε b ≠ ε a} : ℕ) : ℝ)
      = ((a : ℕ) : ℝ) := by
    exact_mod_cast (show #{b | b < a ∧ ε b = ε a} + #{b | b < a ∧ ε b ≠ ε a} = (a : ℕ) by omega)
  linarith
end Formalism.REAL
