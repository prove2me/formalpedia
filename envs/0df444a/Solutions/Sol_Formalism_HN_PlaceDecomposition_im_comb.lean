-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.im_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:11.772938+00:00
-- url     : https://prove2.me/submissions/84a426b9-00f5-4fd0-90d0-951fd9272bfc

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution {κ : Type*} [Fintype κ] (r : κ → ℝ) (c : κ → ℂ) (f : ℂ) :
    ∑ k, r k * (c k * f).im = ((∑ k, (r k : ℂ) * c k) * f).im := by
  rw [Finset.sum_mul, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Complex.im_ofReal_mul]
end Formalism.HN.PlaceDecomposition
