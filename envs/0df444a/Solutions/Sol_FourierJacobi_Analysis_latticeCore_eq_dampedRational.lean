-- Prove2me | solution 1 for FourierJacobi.Analysis.latticeCore_eq_dampedRational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:30.88945+00:00
-- url     : https://prove2.me/submissions/e12df20b-135d-4283-abce-bd44ccc2152f

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Theorems.Thm_FourierJacobi_Analysis_central_master_sum_eq_rows
import Theorems.Thm_FourierJacobi_Analysis_natural_master_parameters
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_unitary
import Theorems.Thm_FourierJacobi_Analysis_geometricRange_of_bounds
import Theorems.Thm_FourierJacobi_Analysis_paperC_eq_poincare


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    latticeCore q a b d T = dampedRational (inverseSqrt q) a b d T := by
  obtain ⟨ht, hq0, hq1, hq2, hqt⟩ := natural_master_parameters hq
  have hq' : 1 < q := by linarith
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inverseSqrt_pos hq') hd₀)
  unfold latticeCore dampedRational
  rw [paperC_eq_poincare q (by linarith)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact central_master_sum_eq_rows (q : ℂ) (inverseSqrt q : ℂ) d
    (weylU a b i) (weylV a b i) (T : ℂ) ht hd hq0 hq1 hq2 hqt
    (geometricRange_of_bounds (inverseSqrt_pos hq') (inverseSqrt_lt_one hq')
      hT₀ hT₁ hd₀ hd₁ hstrict (weylU_unitary ha hb i) (weylV_unitary ha hb i))
end FourierJacobi.Analysis
