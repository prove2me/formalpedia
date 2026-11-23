-- Prove2me | solution 1 for Formalism.DimensionVariation.division_inequality_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:16.865834+00:00
-- url     : https://prove2.me/submissions/7964c601-7432-4a01-a249-f8175250bcf2

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_divisor_inequality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : DivIneqExplicit6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc xe m f k N S tt η
    w'' b' lam0 C0 Lpass Eb e6 eP logOm pq w eE δ
  intro q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2 y3 y4 y5 y6
  refine Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo hu hP mlam logT
    (fun j => sizeB ν logOm f m N L La C0 j) aT
    (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) fa
    x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' 1 lam0 C0 Lpass Eb e6 eP logOm
    (fun _ => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) pq w eE δ
    q1 q2 q3 (fun j => le_refl _) q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18
    z19 z20 z21 le_rfl z23 z24 z25 z26 (by simpa using z27) z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2 ?_ y3 y4 y5 y6
  intro j
  apply mul_le_mul_of_nonneg_left _ hC
  have : 0 ≤ f * N ^ 2 := by positivity
  nlinarith
end Formalism.DimensionVariation
