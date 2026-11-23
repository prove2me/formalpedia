-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.curve_tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:28.109011+00:00
-- url     : https://prove2.me/submissions/0ab3883e-2085-4eda-97d4-996699785b28

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD

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
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)
namespace CompanionTheory.D.Inhab.HWRep
theorem _root_.solution {a b : Fin k} (hab : a ≤ b) (t : ℂ) :
    (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ).BlockTriangular id := by
  intro c d h
  have h' : d < c := h
  have : ¬(a = c ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact absurd hab (not_le.2 h')
  simp [Matrix.one_apply, h'.ne', Matrix.single_apply, this]
end CompanionTheory.D.Inhab.HWRep
