-- Prove2me | solution 1 for CompanionTheory.D.LK.sup_of_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:04.946433+00:00
-- url     : https://prove2.me/submissions/c710a1b0-99cf-433f-bc4d-f1b78edfd8a8

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator

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
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x : Cn n V} {y : Cn n W} (hx : Sup ε B j x)
    (h : ∀ A, x A = 0 → y A = 0) : Sup ε B j y := fun A hA => hx A fun h0 => hA (h A h0)
end CompanionTheory.D.LK
