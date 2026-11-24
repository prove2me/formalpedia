-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.inV_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:49:27.541686+00:00
-- url     : https://prove2.me/submissions/be89cd87-1987-49af-8a5a-f5befbc788a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ElementaryGeneratorsLevelGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} (x y : Fin (mdim k r i)) :
    InV k r i (Matrix.single (posL k r i x) (posL k r i y) (1 : ℂ)) := by
  intro p q h
  rw [Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exfalso
    have hx := x.isLt
    have hy := y.isLt
    have hi := i.isLt
    unfold mdim at hx hy
    rcases h with h | h <;> (simp only [Out, posL] at h; omega)
  · rfl
end Formalism.FourierDecayAlt.Q.EabGlW
