-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_ptPl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:05.444292+00:00
-- url     : https://prove2.me/submissions/53f3e6c4-64d4-4cf7-abf0-56ae47a49771

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt

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
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (ρ : Fin N) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  obtain ⟨c, i⟩ := q
  fin_cases c <;> simp [pt]
end Formalism.L2.FormalSeriesBounds.VP
