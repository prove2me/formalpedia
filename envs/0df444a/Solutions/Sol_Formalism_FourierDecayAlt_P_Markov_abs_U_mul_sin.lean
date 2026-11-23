-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.abs_U_mul_sin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:18.580089+00:00
-- url     : https://prove2.me/submissions/7dfd8701-d3df-4062-9405-4d45074a7fe9

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (n k : ℕ) (hn : n ≠ 0) :
    |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| * |sin (th n k)| = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← abs_mul, Chebyshev.U_real_cos]
  have : ((((n : ℤ) - 1 : ℤ) : ℝ) + 1) * th n k = k * π + π / 2 := by
    push_cast; simp only [th]; field_simp; ring
  rw [this, sin_add_pi_div_two, cos_nat_mul_pi]
  simp
end Formalism.FourierDecayAlt.P.Markov
