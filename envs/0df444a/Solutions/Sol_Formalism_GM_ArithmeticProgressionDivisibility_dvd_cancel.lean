-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.dvd_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:55.884416+00:00
-- url     : https://prove2.me/submissions/eeb74c71-f87e-42eb-a79d-5a283b225c61

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open Formalism.GM.ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
omit [NormedAlgebra ℚ_[p] K]
namespace Formalism.GM.ArithmeticProgressionDivisibility
theorem _root_.solution {d : ℤ} (hd : IsCoprime d (p : ℤ)) (i : ℕ) {m : ℤ} (hm : (p : ℤ) ^ i ∣ d * m) :
    (p : ℤ) ^ i ∣ m := (IsCoprime.pow_left hd.symm).dvd_of_dvd_mul_left hm
end Formalism.GM.ArithmeticProgressionDivisibility
