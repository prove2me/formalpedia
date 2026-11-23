-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaConv.eventually_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:59.677275+00:00
-- url     : https://prove2.me/submissions/6b4d539a-97af-4d01-b99c-d452b5060968

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
theorem _root_.solution (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rcases le_or_gt R 0 with hR | hR
  · exact Eventually.of_forall fun l => hR.trans (norm_nonneg _)
  have ht := (summable_norm_lattice_rpow_neg_three L).tendsto_cofinite_zero
  have hε : (0 : ℝ) < R ^ (-3 : ℝ) := Real.rpow_pos_of_pos hR _
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_cofinite_ne 0] with l hl hl0
  have hpos : 0 < ‖(l : ℂ)‖ := by
    rw [norm_pos_iff]
    exact fun h => hl0 (Subtype.ext h)
  by_contra hlt
  push_neg at hlt
  have := Real.rpow_le_rpow_of_nonpos hpos hlt.le (by norm_num : (-3 : ℝ) ≤ 0)
  linarith
end Formalism.L2.Th1.F.SigmaConv
