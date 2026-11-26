-- Prove2me | solution 1 for FourierJacobi.Analysis.paperD2_special_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:01.13285+00:00
-- url     : https://prove2.me/submissions/a46a4a06-6894-4302-8ce7-5a95d17f9363

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b : ℂ) :
    paperD2 q a b (inverseSqrt q : ℂ) = fourFactors a b 1 := by
  rw [paperD2_eq_d₂, d₂]
  have htne : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  rw [div_self htne]
end FourierJacobi.Analysis
