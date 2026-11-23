-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaConv.summable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:52.112067+00:00
-- url     : https://prove2.me/submissions/e342175f-6f68-4301-ac94-7ce986dadab8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
namespace Formalism.L2.Th1.F
namespace SigmaConv
private lemma summable_norm_lattice_rpow_neg_three (L : PeriodPair) :
    Summable (fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ)) := by
  have hfin : Module.finrank ℤ L.lattice = 2 := by
    rw [ZLattice.rank ℝ L.lattice, Complex.finrank_real_complex]
  exact ZLattice.summable_norm_rpow L.lattice (-3) (by rw [hfin]; norm_num)
end SigmaConv
open SigmaConv
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaConv
namespace Formalism.L2.Th1.F.SigmaConv
theorem _root_.solution (L : PeriodPair) (r : ℝ) :
    Summable (fun l : L.lattice => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ)) :=
  (summable_norm_lattice_rpow_neg_three L).mul_left _
end Formalism.L2.Th1.F.SigmaConv
