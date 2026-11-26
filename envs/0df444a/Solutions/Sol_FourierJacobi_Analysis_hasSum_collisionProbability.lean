-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_collisionProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:09.396573+00:00
-- url     : https://prove2.me/submissions/b27de669-afee-4442-9719-cf047a1643d4

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionProbability_tail
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (hq₀ : q ≠ 0)
    (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (collisionProbability q) 1 := by
  have h := hasSum_collisionProbability_tail q 0 hq
  have he : (q⁻¹) ^ (0 + 1) * (1 - q⁻¹)⁻¹ = 1 - collisionProbability q 0 := by
    simp only [collisionProbability, if_true]
    field_simp [hq₀, hq₁]
    ring_nf
    simp [hq₀]
  rw [he] at h
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Nat.add_zero, Finset.sum_range_one] using h
end FourierJacobi.Analysis
