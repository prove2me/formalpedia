-- Prove2me | solution 1 for FourierJacobi.Analysis.geometricRange_undamped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:27.078828+00:00
-- url     : https://prove2.me/submissions/af007e0a-6a44-4ff1-b597-762bd5be79be

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_geometricRange_of_bounds
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution {t : ℝ} {d U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hd₀ : t < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) :
    GeometricRange (t : ℂ) d U V 1 := by
  simpa only [Complex.ofReal_one] using
    geometricRange_of_bounds ht₀ ht₁ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1) hd₀.le hd₁ (by simpa using hd₀) hU hV
end FourierJacobi.Analysis
