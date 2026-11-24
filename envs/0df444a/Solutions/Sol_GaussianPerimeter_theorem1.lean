-- Prove2me | solution 1 for GaussianPerimeter.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T13:08:25.616612+00:00
-- url     : https://prove2.me/submissions/081e1aaa-3e7a-464b-9fe6-d621e57856c5

module
public import Definitions.Def_GaussianPerimeter_Construction
public import Definitions.Def_GaussianPerimeter_QuadratureCertificate
public import Definitions.Def_GaussianPerimeter_Solution
public import Theorems.Thm_GaussianPerimeter_gaussianLowerBound_numeric
public import Theorems.Thm_GaussianPerimeter_lowerBound_gaussianPerimeter


set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution :
    ENNReal.ofReal (0.31258 : ℝ) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop :=
  (ENNReal.ofReal_le_ofReal gaussianLowerBound_numeric).trans
    (lowerBound_gaussianPerimeter
      (a := 6131 / 5000) (b := 2387 / 1000) (W := 6)
      (by norm_num) (by norm_num) (by norm_num))
end GaussianPerimeter
