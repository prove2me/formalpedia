-- Prove2me | solution 1 for Bl.general_b_fact_right_alt.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:01.840899+00:00
-- url     : https://prove2.me/submissions/d829e078-75e1-4a3a-b5ac-26c78b5b589f

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open Bl Bl.general_b_fact_right_alt
namespace Bl.general_b_fact_right_alt
theorem _root_.solution {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {ι : Type*} [Fintype ι]
    {G : MvPolynomial ι K} {d : ℕ} (hG : IsHomogeneous G d) (c : S) (f : ι → S) :
    aeval (fun v => c * f v) G = c ^ d * aeval f G := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← hG.degree_eq_sum_deg_support hs]
  ring
end Bl.general_b_fact_right_alt
