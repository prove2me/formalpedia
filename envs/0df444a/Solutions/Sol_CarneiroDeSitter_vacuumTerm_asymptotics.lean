-- Prove2me | solution 1 for CarneiroDeSitter.vacuumTerm_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:49:15.860994+00:00
-- url     : https://prove2.me/submissions/1eeb48d9-db31-4692-93f4-4f340379b477

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set
namespace CarneiroDeSitter

theorem vt (m : ℝ) (hm : 0 < m) :
    (fun H => vacuumTerm m H) ~[atTop] (fun H => H ^ 4) ∧
    (fun H => vacuumTerm m H) ~[𝓝[>] 0] (fun H => 4 * m ^ 3 * H) := by
  constructor
  · apply IsEquivalent.trans (v := fun H : ℝ => H ^ 4 * (1 + 4*m/H + 6*m^2/H^2 + 4*m^3/H^3))
    · apply EventuallyEq.isEquivalent
      filter_upwards [eventually_gt_atTop 0] with H hH
      simp only [vacuumTerm]; field_simp; ring
    · have : Tendsto (fun H : ℝ => 1 + 4*m/H + 6*m^2/H^2 + 4*m^3/H^3) atTop (𝓝 1) := by
        have h1 := tendsto_inv_atTop_zero (𝕜 := ℝ)
        have : Tendsto (fun H : ℝ => 1 + 4*m*H⁻¹ + 6*m^2*(H⁻¹)^2 + 4*m^3*(H⁻¹)^3) atTop
            (𝓝 (1 + 4*m*0 + 6*m^2*0^2 + 4*m^3*0^3)) := by
          refine ((tendsto_const_nhds.add (h1.const_mul _)).add ((h1.pow 2).const_mul _)).add ((h1.pow 3).const_mul _)
        simpa [div_eq_mul_inv, inv_pow] using this
      have := (isEquivalent_const_iff_tendsto one_ne_zero).2 this
      have h := (IsEquivalent.refl (u := fun H : ℝ => H ^ 4)).mul this
      simpa [Pi.mul_def] using h
  · apply IsEquivalent.trans (v := fun H : ℝ => (4 * m ^ 3 * H) * (1 + (6*m^2*H + 4*m*H^2 + H^3)/(4*m^3)))
    · apply EventuallyEq.isEquivalent
      filter_upwards with H
      simp only [vacuumTerm]; field_simp; ring
    · have : Tendsto (fun H : ℝ => 1 + (6*m^2*H + 4*m*H^2 + H^3)/(4*m^3)) (𝓝[>] 0) (𝓝 1) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous (fun H : ℝ => 1 + (6*m^2*H + 4*m*H^2 + H^3)/(4*m^3)) := by fun_prop
        simpa using this.tendsto 0
      have := (isEquivalent_const_iff_tendsto one_ne_zero).2 this
      have h := (IsEquivalent.refl (u := fun H : ℝ => 4 * m ^ 3 * H)).mul this
      simpa [Pi.mul_def] using h

end CarneiroDeSitter

open Real Filter Topology Asymptotics MeasureTheory Set CarneiroDeSitter

theorem solution (m : ℝ) (hm : 0 < m) :
    (fun H => vacuumTerm m H) ~[atTop] (fun H => H ^ 4) ∧
    (fun H => vacuumTerm m H) ~[𝓝[>] 0] (fun H => 4 * m ^ 3 * H) := vt m hm
