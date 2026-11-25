-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_expAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:32:38.996815+00:00
-- url     : https://prove2.me/submissions/7d57cfc6-f918-45b0-a160-4524450eba87

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst


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
theorem _root_.solution (x : Fin dd) : MvPowerSeries.constantCoeff (expAll Y p x) = 0 := by
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) f = _
    rw [Finsupp.mapDomain_zero]
  unfold expAll
  exact VP.cc_subst (fun _ => by simp [MvPowerSeries.smul_eq_C_mul]) (by rw [hu]; exact Y.ex_const x)
end Formalism.L2.FormalSeriesBounds.VP
