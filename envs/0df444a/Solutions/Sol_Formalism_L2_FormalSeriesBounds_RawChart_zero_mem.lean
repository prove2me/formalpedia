-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:01.623363+00:00
-- url     : https://prove2.me/submissions/38b1b7a1-c0a7-4755-8e86-56d98ff62800

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_constantCoeff_sg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
section TyS
variable {l : ℕ} (hl : 2 ≤ l)
include hl
end TyS
section Repar
end Repar
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
private theorem ge_zero_lemma (V : VF C) : V.Ge 0 (0 : C) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top
end RawChart
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [tyS_zero]
  · intro q
    rw [alongCv_zero (X.constantCoeff_sg hh _)]
    simp [tyS_zero]
end Formalism.L2.FormalSeriesBounds.RawChart
