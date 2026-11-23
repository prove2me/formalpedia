-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.log_ydat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:18.238663+00:00
-- url     : https://prove2.me/submissions/fd9fb6c5-dacb-466f-a526-7db824a97397

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : Real.log (Ydat n f rd g b)
      = Real.log n + Real.log f + Real.log rd + Real.log g + Real.log b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  unfold Ydat
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
end Formalism.HermitianLatticeCounting.P
