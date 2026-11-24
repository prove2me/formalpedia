-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.re_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:12.78944+00:00
-- url     : https://prove2.me/submissions/32790ae2-3ff5-40bb-bd84-a5acd5e38e95

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
    ∑ k, r k * (c k * f).re = ((∑ k, (r k : ℂ) * c k) * f).re := by
  rw [Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Complex.re_ofReal_mul]
end Formalism.HN.PlaceDecomposition
