-- Prove2me | solution 1 for FourierJacobi.Analysis.geometricRange_damped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:02.499373+00:00
-- url     : https://prove2.me/submissions/d8386399-9b38-4dcb-9e0a-c3128efdf38d

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_geometricRange_of_bounds

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution {t T : ℝ} {d U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hT₀ : 0 < T) (hT₁ : T < 1)
    (hd₀ : t ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) :
    GeometricRange (t : ℂ) d U V (T : ℂ) := by
  apply geometricRange_of_bounds ht₀ ht₁ hT₀.le hT₁.le hd₀ hd₁ ?_ hU hV
  nlinarith
end FourierJacobi.Analysis
