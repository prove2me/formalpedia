-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.germLift_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:22.526845+00:00
-- url     : https://prove2.me/submissions/4e2a8c43-0c37-448a-af67-7887dbb1e18d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_germLift_gen
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_tLift_gen
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_expAll
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb]
variable {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSt Y p H := by
  intro hsep o S t hS F hF
  have hA : ∀ q : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (expAll Y p q.2) = 0 := fun q => VP.cc_expAll Y p q.2
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (hS g).1 c
  have hTw : ∀ w : WV (I o), ∃ T : MvPowerSeries (Fin 1 × Fin dd) C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) T = toAllS o (upG w.1 (t w.1 w.2)) := by
    intro w
    obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
    obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
    obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen hA o hπi hπ0 hπ hTi hT0
    exact ⟨T', h1, h2, by rw [h3, hTe]⟩
  exact VP.germLift_gen hA o t ht0 hTw F hF
end Formalism.L2.FormalSeriesBounds
