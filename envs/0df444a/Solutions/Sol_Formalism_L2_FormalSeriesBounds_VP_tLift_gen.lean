-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.tLift_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:33:50.205665+00:00
-- url     : https://prove2.me/submissions/39e6d4b1-6fc1-4eda-ba05-8958a227b75b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_toAllS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_toAllS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ κ : Type} [Finite σ] [Finite κ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    {π : κ → MvPowerSeries σ C} (hπi : ∀ x, IntS V (π x)) (hπ0 : ∀ x, MvPowerSeries.constantCoeff (π x) = 0)
    (hπ : ∀ x, MvPowerSeries.subst A (π x) = toAllS o (E x))
    {T : MvPowerSeries κ C} (hTi : IntS V T) (hT0 : MvPowerSeries.constantCoeff T = 0) :
    ∃ T' : MvPowerSeries σ C, IntS V T' ∧ MvPowerSeries.constantCoeff T' = 0 ∧
      MvPowerSeries.subst A T' = toAllS o (MvPowerSeries.subst E T) := by
  have hπA : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.subst A (π x)) = 0 := fun x => VP.cc_subst hA (hπ0 x)
  have hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0 := fun x => by
    rw [← cc_toAllS o (E x), ← hπ x]
    exact hπA x
  refine ⟨MvPowerSeries.subst π T, IntS.subst hπ0 hπi hTi, VP.cc_subst hπ0 hT0, ?_⟩
  rw [VP.subst_subst hπ0 hA, toAllS_subst o hE]
  congr 1
  funext x
  exact hπ x
end Formalism.L2.FormalSeriesBounds.VP
