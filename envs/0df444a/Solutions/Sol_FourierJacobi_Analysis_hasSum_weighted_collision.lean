-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_weighted_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:49.550739+00:00
-- url     : https://prove2.me/submissions/f8ed1b59-5fca-4861-b740-2c78faa65425

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionWeight
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_weighted_collision
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution {ι : Type*} (q : ℂ) (r : ℤ)
    (j h : ι → ℤ) (f : ι → ℂ) (s : ℂ)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (hf : HasSum f s) (hfn : Summable (fun p => ‖f p‖)) :
    HasSum (fun p : ι × ℕ => f p.1 * collisionWeight q r (j p.1) (h p.1) p.2) s := by
  have hs := (summable_norm_weighted_collision q r j h f hq hfn).of_norm
  have he : (∑' p : ι × ℕ, f p.1 * collisionWeight q r (j p.1) (h p.1) p.2) = s := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, (hasSum_collisionWeight q r _ _ hq₀ hq₁ hq).tsum_eq,
      mul_one, hf.tsum_eq]
  exact he ▸ hs.hasSum
end FourierJacobi.Analysis
