-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.germLiftSelf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:28:25.085792+00:00
-- url     : https://prove2.me/submissions/195e1626-872e-45d7-a447-623f6fbc7b6a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_germLift_gen
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_tLift_gen
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_linPt


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
variable {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (hP : ProjSelfSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSelfSt Y p H := by
  intro hsep o S t hS F hF
  unfold pull2
  have hA : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 := VP.cc_linPt Y (uS Y p)
  refine VP.germLift_gen (I := IS I0) hA o t (fun g c => (hS g).1 c) (fun w => ?_) F hF
  obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
  obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
  obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen (I := IS I0) hA o hπi hπ0 hπ hTi hT0
  exact ⟨T', h1, h2, by rw [h3, hTe]⟩
end Formalism.L2.FormalSeriesBounds
