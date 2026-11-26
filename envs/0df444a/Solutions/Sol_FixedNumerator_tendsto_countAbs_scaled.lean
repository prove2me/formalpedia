-- Prove2me | solution 1 for FixedNumerator.tendsto_countAbs_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:57.486871+00:00
-- url     : https://prove2.me/submissions/ce943ecb-645c-4c55-b72f-adc72a0a9638

module
public import Definitions.Def_FixedNumerator_Determinant
public import Definitions.Def_FixedNumerator_Sharp

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {a : ℕ → ℂ} {κ : ℝ}
    (hmean : Tendsto (fun x : ℝ => countAbs a x / x) atTop (𝓝 κ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun X : ℕ => countAbs a (t * X) / X) atTop (𝓝 (κ * t)) := by
  have h1 : Tendsto (fun X : ℕ => t * (X : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop ht tendsto_natCast_atTop_atTop
  have h2 := (hmean.comp h1).mul_const t
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  simp only [Function.comp]
  field_simp
end FixedNumerator
