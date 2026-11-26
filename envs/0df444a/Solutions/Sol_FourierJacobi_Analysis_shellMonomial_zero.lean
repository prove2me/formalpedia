-- Prove2me | solution 1 for FourierJacobi.Analysis.shellMonomial_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:32.708617+00:00
-- url     : https://prove2.me/submissions/edf6dbcb-7522-437e-9c14-8618632dcadc

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellMonomial t d U V T 0 p c = i0Shell t d U V T p := by
  rfl
end FourierJacobi.Analysis
