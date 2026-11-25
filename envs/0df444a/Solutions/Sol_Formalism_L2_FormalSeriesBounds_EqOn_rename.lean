-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.EqOn.rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:11.964556+00:00
-- url     : https://prove2.me/submissions/c7f9e242-d185-4b36-8c42-0848dd81e3b5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds

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
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace EqOn
theorem _root_.solution {τ : Type} (e : σ ↪ τ) {A : Set τ} {F G : MvPowerSeries σ K}
    (h : ∀ μ : σ →₀ ℕ, (∀ x ∈ μ.support, e x ∈ A) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G) :
    EqOn A (MvPowerSeries.rename e F) (MvPowerSeries.rename e G) := by
  intro ν hν
  by_cases hr : ν ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨μ, rfl⟩ := hr
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename,
      MvPowerSeries.coeff_embDomain_rename]
    refine h μ fun x hx => hν ?_
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
    exact Finset.mem_coe.2 (Finset.mem_map_of_mem e hx)
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ hr, MvPowerSeries.coeff_rename_eq_zero _ _ hr]
end EqOn
end Formalism.L2.FormalSeriesBounds
