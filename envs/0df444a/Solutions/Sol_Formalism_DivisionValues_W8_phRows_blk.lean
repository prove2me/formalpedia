-- Prove2me | solution 1 for Formalism.DivisionValues.W8.phRows_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:20.4277+00:00
-- url     : https://prove2.me/submissions/a9dfdadd-d3f6-4690-915e-faead89107bb

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_W8_log_nat_le
import Theorems.Thm_Formalism_DivisionValues_W8_ph_nat_le
import Theorems.Thm_Formalism_DivisionValues_W8_phRows_cons

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
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {A Bl : ℝ} (blk : Multiset ℕ) (hA : 1 ≤ Real.log A) (hb : (blk.sum : ℝ) ≤ Bl)
    (hBl : Bl ≤ A) : phRows blk ≤ Bl * Real.log A := by
  have hL0 : 0 ≤ Real.log A := by linarith
  have hmem : ∀ r ∈ blk, (r : ℝ) ≤ A := by
    intro r hr
    have h1 : r ≤ blk.sum := Multiset.le_sum_of_mem hr
    have h2 : (r : ℝ) ≤ blk.sum := by exact_mod_cast h1
    linarith
  have hsum : ∀ s : Multiset ℕ, (∀ r ∈ s, (r : ℝ) ≤ A) →
      phRows s ≤ (s.sum : ℝ) * Real.log A := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro _
      simp [phRows]
    · intro a s ih hs
      rw [phRows_cons, Multiset.sum_cons, Nat.cast_add]
      have ha := ph_nat_le a (log_nat_le a hA (hs a (Multiset.mem_cons.mpr (Or.inl rfl))))
      have hs' := ih (fun r hr => hs r (Multiset.mem_cons.mpr (Or.inr hr)))
      linarith
  have h1 := hsum blk hmem
  have h2 := mul_le_mul_of_nonneg_right hb hL0
  linarith
end Formalism.DivisionValues.W8
