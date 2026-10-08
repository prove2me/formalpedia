-- Prove2me | solution 1 for ConnesRZ.explicit_formula_C2
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T14:41:43.781988+00:00
-- url     : https://prove2.me/submissions/4c8b71ed-0641-4f87-8f83-74e546c41a07

import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ExplicitFormula
import Theorems.Thm_Zeta23_WeilEF_EF_lit_zeta
import Theorems.Thm_ConnesRZArithmetic_explicit_formula_of_EF_lit
open Complex MeasureTheory ConnesRZ

theorem solution (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1) (weilDistribution g) :=
  ConnesRZArithmetic.explicit_formula_of_EF_lit Zeta23.zetaSeam
    (Zeta23.WeilEF.EF_lit_zeta Zeta23.zetaSeam) g hg hgc
