-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i0_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:09.362468+00:00
-- url     : https://prove2.me/submissions/59f0ac28-f187-46e9-896c-321a12733553

import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I0Master
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_master
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_tsum_i0_full
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 0)
      (∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide))) := by
  have hs := (summable_norm_i0_master q t d U V T h).of_norm
  have hs' : Summable (fun p : (ℤ × ℤ × ℤ) × ℕ =>
      masterTerm q t d U V T 0 (latticeDepthEquiv p)) :=
    latticeDepthEquiv.summable_iff.mpr hs
  apply latticeDepthEquiv.hasSum_iff.mp
  have he : (∑' p : (ℤ × ℤ × ℤ) × ℕ,
      masterTerm q t d U V T 0 (latticeDepthEquiv p)) =
        ∑ i : Fin 10, Algebra.regionTerms t d (T * U) (T * V) (i.castLE (by decide)) := by
    rw [hs'.tsum_prod]
    simp only [masterTerm_zero, latticeDepthEquiv, Equiv.coe_fn_mk,
      tsum_ite_eq, tsum_i0_full t d U V T h.t2 h.p h.n h.e h.f h.g]
  exact he ▸ hs'.hasSum
end FourierJacobi.Analysis
