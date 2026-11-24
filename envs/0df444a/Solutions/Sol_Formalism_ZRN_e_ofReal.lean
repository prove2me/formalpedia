-- Prove2me | solution 1 for Formalism.ZRN.e_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:12.516176+00:00
-- url     : https://prove2.me/submissions/423f6a53-6c2b-42a5-9bb7-13935e95505b

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (n : ℕ) (σ : ℝ) : e n σ = (er n σ : ℂ) := by
  have p1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have p2 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  simp only [er, e, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_cpow p1, Complex.ofReal_cpow p2, Complex.ofReal_neg, Complex.ofReal_natCast,
    Complex.ofReal_ofNat]
end Formalism.ZRN
