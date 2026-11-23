-- Prove2me | solution 1 for Formalism.FG.SolveVAux.degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:08.36007+00:00
-- url     : https://prove2.me/submissions/5ccf64b4-f778-4377-8be3-83cc3d286ac4

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
namespace Formalism.FG.SolveVAux
theorem _root_.solution {ι : Type v} (d : ι →₀ ℕ) (hd : d.degree = 1) :
    ∃ i, d = Finsupp.single i 1 := by
  classical
  have hne : d ≠ 0 := by rintro rfl; simp at hd
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra! hc; exact hne (Finsupp.ext hc)
  have hi1 : d i ≤ 1 := hd ▸ Finsupp.le_degree i d
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : d = (d - Finsupp.single i 1) + Finsupp.single i 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hdeg : d.degree = (d - Finsupp.single i 1).degree + 1 := by
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  have h0 : d - Finsupp.single i 1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
  refine ⟨i, ?_⟩
  rw [hsplit, h0, zero_add]
end Formalism.FG.SolveVAux
