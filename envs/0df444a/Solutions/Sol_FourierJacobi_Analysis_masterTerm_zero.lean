-- Prove2me | solution 1 for FourierJacobi.Analysis.masterTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:44.016443+00:00
-- url     : https://prove2.me/submissions/bbc34eb0-86cc-4022-be6c-53c1080ffd0c

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (p : LatticeIndex) :
    masterTerm q t d U V T 0 p =
      if p.2.2.2 = 0 then i0Shell t d U V T (p.1, p.2.1, p.2.2.1) else 0 := by
  simp only [masterTerm, shellCoeff, collisionWeight, true_or, if_true,
    shellMonomial_zero, one_mul]
  split_ifs <;> simp
end FourierJacobi.Analysis
