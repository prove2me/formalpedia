-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.uw_fixed_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:07.225356+00:00
-- url     : https://prove2.me/submissions/3726cda3-bf88-4c3d-ad8c-8ac882f3d932

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨_, hfix, _⟩ := hh
  rcases hc with hc | hc
  · have e := (hfix ⟨c.val, hc⟩).1
    have he : eI k r ⟨c.val, hc⟩ = c := Fin.ext rfl
    rw [he] at e
    exact col_of_fix e p
  · have hcl := c.isLt
    have hc' : 2 * r + k - c.val < r := by omega
    have e := (hfix ⟨2 * r + k - c.val, hc'⟩).2
    have he : esI k r ⟨2 * r + k - c.val, hc'⟩ = c := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - c.val) = c.val
      omega
    rw [he] at e
    exact col_of_fix e p
end Formalism.QuantumDeterminants.WeylGroupFacts
