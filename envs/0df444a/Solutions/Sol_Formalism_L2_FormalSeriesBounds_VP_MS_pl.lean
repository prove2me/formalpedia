-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.MS_pl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:03.850342+00:00
-- url     : https://prove2.me/submissions/7ac72f06-33a3-41be-a76c-eb0df03b7e02

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
theorem _root_.solution (ρ' ρ : Fin N) (w : WVO (IS I0)) (col : Fin 2) (i : Fin dd) :
    MS Y p pl (ρ', w) (pl (ρ, col), i) = if ρ' = ρ then uS Y p w (col, i) else 0 := by
  simp only [MS, pl.injective.eq_iff, Prod.mk.injEq]
  by_cases h : ρ' = ρ
  · simp [h]
  · simp [h]
end Formalism.L2.FormalSeriesBounds.VP
