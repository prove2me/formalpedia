-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.germLift_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:46.910952+00:00
-- url     : https://prove2.me/submissions/17a8bc2f-aeef-4e06-9d8a-8110406f7088

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
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
theorem _root_.solution {σ : Type} [Finite σ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) (t : ∀ g, I o g → MvPowerSeries (I o g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (hT : ∀ w : WV (I o), ∃ T : MvPowerSeries σ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst A T = toAllS o (upG w.1 (t w.1 w.2))) :
    ∀ F ∈ IntGerm V t, ∃ G : MvPowerSeries σ C, IntS V G ∧ MvPowerSeries.subst A G = toAllS o F := by
  intro F hF
  obtain ⟨γ, hγ, rfl⟩ := hF
  choose T hTi hT0 hTA using hT
  have hE : ∀ w : WV (I o), MvPowerSeries.constantCoeff (upG w.1 (t w.1 w.2)) = 0 := fun w => by
    unfold upG
    exact VP.cc_subst (fun _ => MvPowerSeries.constantCoeff_X _) (ht0 _ _)
  refine ⟨MvPowerSeries.subst T γ, IntS.subst hT0 hTi hγ, ?_⟩
  rw [VP.subst_subst hT0 hA, toAllS_subst o hE]
  congr 1
  funext w
  exact hTA w
end Formalism.L2.FormalSeriesBounds.VP
