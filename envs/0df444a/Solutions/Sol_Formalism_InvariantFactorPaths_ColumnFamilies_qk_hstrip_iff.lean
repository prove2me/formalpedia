-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_hstrip_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:15.28948+00:00
-- url     : https://prove2.me/submissions/96846a9e-569b-46c2-8e44-2287a60c972d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) : HStrip nu mu b ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip mu nu b := by
  unfold HStrip Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h m m' hm
      have := h m (by have := m'.2; omega)
      have e : (⟨m.1 + 1, by have := m'.2; omega⟩ : Fin n) = m' := Fin.ext hm
      rwa [e] at this
    · intro h a ha
      exact h a ⟨a.1 + 1, ha⟩ rfl
  · rw [sum_sub_distrib]
end Formalism.InvariantFactorPaths.ColumnFamilies
