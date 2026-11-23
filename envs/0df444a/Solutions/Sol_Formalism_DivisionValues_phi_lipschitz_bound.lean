-- Prove2me | solution 1 for Formalism.DivisionValues.phi_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.616243+00:00
-- url     : https://prove2.me/submissions/a2e5ea79-f2e2-43a6-a013-affa9ae10216

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_phi_difference_le_mul_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : PhLip := by
  unfold PhLip
  intro y y' A hy hy' hyA hy'A
  have key : ∀ a a' : ℝ, 1 ≤ a' → a' ≤ a → a ≤ A →
      |Formalism.LatticeIndexTer.ph a - Formalism.LatticeIndexTer.ph a'| ≤ |a - a'| * Real.log A := by
    intro a a' ha' haa' haA
    obtain ⟨h0, h1⟩ := phi_difference_le_mul_log a a' ha' haa'
    have hlog : Real.log a ≤ Real.log A := Real.log_le_log (by linarith) haA
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - a')]
    calc Formalism.LatticeIndexTer.ph a - Formalism.LatticeIndexTer.ph a' ≤ (a - a') * Real.log a := h1
      _ ≤ (a - a') * Real.log A := mul_le_mul_of_nonneg_left hlog (by linarith)
  rcases le_total y' y with h | h
  · exact key y y' hy' h hyA
  · rw [abs_sub_comm, abs_sub_comm y y']
    exact key y' y hy h hy'A
end Formalism.DivisionValues
