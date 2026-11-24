-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.constantCoeff_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:52.75025+00:00
-- url     : https://prove2.me/submissions/a1604bec-b947-47dd-9833-82aa0074b4a9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change -∑ i, v i * MvPowerSeries.coeff ((0 : κ →₀ ℕ).mapDomain (fun x : κ => ((0 : Fin 2), x)) +
    Finsupp.single ((1 : Fin 2), i) 1) X.h = 0
  simp only [Finsupp.mapDomain_zero, zero_add]
  rw [Finset.sum_eq_zero, neg_zero]
  intro i _
  rw [hh _ ?_, mul_zero]
  intro s hs
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hs
  rw [hs]
  simp
end Formalism.L2.FormalSeriesBounds.RawChart
