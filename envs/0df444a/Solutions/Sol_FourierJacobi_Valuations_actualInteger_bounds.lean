-- Prove2me | solution 1 for FourierJacobi.Valuations.actualInteger_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:48.846071+00:00
-- url     : https://prove2.me/submissions/da959847-41d3-418e-a1ba-c3babc680a26

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_le_entry
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum_le_zero
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
import Theorems.Thm_FourierJacobi_Valuations_twice_entry_minimum_le_minor
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    2 * actualEntryInteger v a x y z ≤ actualMinorInteger v a x y z ∧
    actualMinorInteger v a x y z ≤ actualEntryInteger v a x y z ∧
    actualEntryInteger v a x y z ≤ 0 := by
  have h1 := twice_entry_minimum_le_minor v (g (a:K) x y z)
  have h2 := actual_minor_minimum_le_entry v (a:K) x y z (Units.ne_zero a)
  have h3 := actual_entry_minimum_le_zero v (a:K) x y z
  rw [← actualEntryInteger_coe v a x y z,
    ← actualMinorInteger_coe v a x y z, ← WithTop.coe_add] at h1
  rw [← actualEntryInteger_coe v a x y z,
    ← actualMinorInteger_coe v a x y z] at h2
  rw [← actualEntryInteger_coe v a x y z] at h3
  have h1' := WithTop.coe_le_coe.mp h1
  have h2' := WithTop.coe_le_coe.mp h2
  have h3' : actualEntryInteger v a x y z ≤ 0 := by exact_mod_cast h3
  exact ⟨by omega, h2', h3'⟩
end FourierJacobi.Valuations
