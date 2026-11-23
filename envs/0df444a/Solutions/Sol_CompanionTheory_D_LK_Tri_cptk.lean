-- Prove2me | solution 1 for CompanionTheory.D.LK.Tri.cptk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:13.511465+00:00
-- url     : https://prove2.me/submissions/6dff8836-2756-4142-a81a-a8dc702d9c5f

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport

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
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
namespace Tri
theorem _root_.solution {ε : Fin n → Bool} {i j k : Pos n} (h : Tri ε i j k) : cpt ε k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  show ε k.1.1 = ε k.1.2
  rw [h4, h5, h1, h3]; exact h2
end Tri
end CompanionTheory.D.LK
