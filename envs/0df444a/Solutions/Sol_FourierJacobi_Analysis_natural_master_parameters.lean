-- Prove2me | solution 1 for FourierJacobi.Analysis.natural_master_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:09:35.68206+00:00
-- url     : https://prove2.me/submissions/6d9148c6-a9d6-4d5a-8401-f8f8a7ee3f89

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_coe_mul


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution {q : ℝ} (hq : 2 < q) :
    (inverseSqrt q : ℂ) ≠ 0 ∧ (q : ℂ) ≠ 0 ∧
      (q : ℂ) - 1 ≠ 0 ∧ (q : ℂ) - 2 ≠ 0 ∧
      (q : ℂ) * (inverseSqrt q : ℂ) ^ 2 = 1 := by
  have hq' : 1 < q := by linarith
  refine ⟨?_, ?_, ?_, ?_, inverseSqrt_coe_mul q hq'⟩
  · exact_mod_cast ne_of_gt (inverseSqrt_pos hq')
  · exact_mod_cast (ne_of_gt (show 0 < q by linarith))
  · exact_mod_cast (ne_of_gt (show 0 < q - 1 by linarith))
  · exact_mod_cast (ne_of_gt (show 0 < q - 2 by linarith))
end FourierJacobi.Analysis
