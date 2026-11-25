-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.constantCoeff_single_point_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:36.083821+00:00
-- url     : https://prove2.me/submissions/c677dcc9-8abd-414e-9acb-9a1a19c5f587

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {n : ℕ} (b : Fin n) (q : Fin 1 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2) = 0 := by
  simp [pt]
end Formalism.L2.FormalSeriesBounds.VP
