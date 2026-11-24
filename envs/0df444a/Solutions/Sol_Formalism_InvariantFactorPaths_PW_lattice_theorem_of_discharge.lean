-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.lattice_theorem_of_discharge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:22.714834+00:00
-- url     : https://prove2.me/submissions/b17344da-91f4-4490-99b5-de62be3c0a11

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeTheoremOfDischarge
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_setTies_deg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hM : Formalism.GM.M.TheoremM) (hD : HeightBoundImplication) : LatticeTheoremHeightBound := by
  obtain ⟨C₀, hC₀, hM⟩ := hM
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq hL4
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ ?_
  intro n hn
  have hle : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
    intro i
    have hi := Fintype.mem_piFinset.mp hn i
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hj' : j < Yl i := Finset.mem_range.mp hj
    rw [← hji]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt hj')) _
  have hdeg' : ∀ x, (LL.setTies T n).deg x ≤ 2 * a := fun x =>
    (setTies_deg_le LL T n _ hle x).trans (hdeg x)
  obtain ⟨hP, hW, -⟩ := hD p N r (LL.setTies T n) ρ a κ hdeg' hineq hκ
  exact ⟨hP, hW, hL4 n hn⟩
end Formalism.InvariantFactorPaths.PW
