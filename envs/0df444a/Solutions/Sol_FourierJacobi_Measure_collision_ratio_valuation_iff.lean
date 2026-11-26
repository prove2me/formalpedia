-- Prove2me | solution 1 for FourierJacobi.Measure.collision_ratio_valuation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:09.173112+00:00
-- url     : https://prove2.me/submissions/41f9e0ae-b7bc-480a-91ce-6b97e1be6551

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.jointCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (x y z : K) (j s : ℤ) (c : ℕ)
    (hx : localFieldValuation K x = (j : WithTop ℤ))
    (hz : localFieldValuation K z = (s : WithTop ℤ)) :
    localFieldValuation K (y ^ 2 / (x * z) - 1) = ((c : ℤ) : WithTop ℤ) ↔
      localFieldValuation K (y ^ 2 - x * z) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ) := by
  have hx0 : x ≠ 0 := (localFieldValuation_ne_top K x).mp (by rw [hx]; simp)
  have hz0 : z ≠ 0 := (localFieldValuation_ne_top K z).mp (by rw [hz]; simp)
  have he : y ^ 2 / (x * z) - 1 = (y ^ 2 - x * z) / (x * z) := by
    field_simp
  rw [he, (localFieldValuation K).map_div, (localFieldValuation K).map_mul, hx, hz,
    ← WithTop.coe_add]
  generalize localFieldValuation K (y ^ 2 - x * z) = v
  induction v using WithTop.recTopCoe with
  | top =>
    change ((⊤ : WithTop ℤ) = ((c : ℤ) : WithTop ℤ)) ↔
      ((⊤ : WithTop ℤ) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ))
    simp only [WithTop.top_ne_coe]
  | coe d =>
    change ((d - (j + s) : ℤ) : WithTop ℤ) = ((c : ℤ) : WithTop ℤ) ↔
      (d : WithTop ℤ) = ((j + s + (c : ℤ) : ℤ) : WithTop ℤ)
    simp only [WithTop.coe_inj]
    omega
end FourierJacobi.Measure
