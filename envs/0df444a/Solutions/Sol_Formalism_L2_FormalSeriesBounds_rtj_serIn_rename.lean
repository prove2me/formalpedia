-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_serIn_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:44.901043+00:00
-- url     : https://prove2.me/submissions/990e2aef-63b0-4881-bb4c-ac4752540c85

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (e : σ ↪ τ) (F : MvPowerSeries σ K) :
    rtjSerIn (Set.range e) (MvPowerSeries.rename e F) := by
  unfold rtjSerIn
  intro μ hμ
  rw [MvPowerSeries.coeff_rename] at hμ
  obtain ⟨y, hy, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hy
  subst hy
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hi)
  exact ⟨j, rfl⟩
end Formalism.L2.FormalSeriesBounds
