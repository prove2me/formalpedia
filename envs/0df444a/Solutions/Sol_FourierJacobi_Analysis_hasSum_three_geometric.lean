-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_three_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:07.739823+00:00
-- url     : https://prove2.me/submissions/02700983-b6de-4b2c-93dc-4ea4c482fcd8

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_geometric_norm_summable
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (C a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    HasSum (fun n : ℕ × ℕ × ℕ => C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹) := by
  have hA : (∑' n : ℕ, a ^ n) = (1 - a)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB : (∑' n : ℕ, b ^ n) = (1 - b)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have hC : (∑' n : ℕ, c ^ n) = (1 - c)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hc).tsum_eq
  have hsBC : Summable (fun n : ℕ × ℕ => b ^ n.1 * c ^ n.2) :=
    summable_mul_of_summable_norm (f := fun n : ℕ => b ^ n)
      (g := fun n : ℕ => c ^ n) (geometric_norm_summable b hb) (geometric_norm_summable c hc)
  have hBC : (∑' n : ℕ × ℕ, b ^ n.1 * c ^ n.2) =
      (1 - b)⁻¹ * (1 - c)⁻¹ := by
    rw [hsBC.tsum_prod]
    simp only [tsum_mul_left, hC, tsum_mul_right, hB]
  have hs : Summable (fun n : ℕ × ℕ × ℕ =>
      C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2) :=
    (summable_norm_three_geometric C a b c ha hb hc).of_norm
  have he : (∑' n : ℕ × ℕ × ℕ, C * a ^ n.1 * b ^ n.2.1 * c ^ n.2.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [mul_assoc, tsum_mul_left, hBC, tsum_mul_right, hA]
  exact he ▸ hs.hasSum
end FourierJacobi.Analysis
