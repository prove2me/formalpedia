-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exp_isBigO_exp_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:25.176799+00:00
-- url     : https://prove2.me/submissions/32ed5629-1786-465b-91c8-c529cae85fa9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution {c₁ α₁ c α : ℝ} (hcpos : 0 < c) (hcle : c ≤ c₁)
    (hαle : α ≤ α₁) :
    (fun r : ℝ => Real.exp (-c₁ * r ^ α₁)) =O[Filter.atTop]
      (fun r : ℝ => Real.exp (-c * r ^ α)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hc1pos : 0 < c₁ := lt_of_lt_of_le hcpos hcle
  have h1 : r ^ α ≤ r ^ α₁ := Real.rpow_le_rpow_of_exponent_le hr hαle
  have hrα : 0 ≤ r ^ α := Real.rpow_nonneg hr0 α
  have hle : c * r ^ α ≤ c₁ * r ^ α₁ := by nlinarith [hrα, hc1pos.le, h1]
  have hexp : Real.exp (-c₁ * r ^ α₁) ≤ Real.exp (-c * r ^ α) :=
    Real.exp_le_exp.mpr (by nlinarith [hle])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), one_mul]
  exact hexp
end DedekindZeta.ConeRadialReduction
