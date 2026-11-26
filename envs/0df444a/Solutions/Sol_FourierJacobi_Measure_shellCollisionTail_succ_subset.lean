-- Prove2me | solution 1 for FourierJacobi.Measure.shellCollisionTail_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:05.987067+00:00
-- url     : https://prove2.me/submissions/b6ae1356-8c82-41e8-b2b4-f11defafab82

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (a : K) (n : ℤ) (c : ℕ) :
    shellCollisionTail K a n (c + 1) ⊆ shellCollisionTail K a n c := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change ((n + (c : ℤ) : ℤ) : WithTop ℤ) ≤ localFieldValuation K (x - a)
  have hx' : ((n + ((c + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
      localFieldValuation K (x - a) := hx.2
  apply le_trans ?_ hx'
  exact_mod_cast (show n + (c : ℤ) ≤ n + ((c + 1 : ℕ) : ℤ) by omega)
end FourierJacobi.Measure
