-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.valO_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:42.61143+00:00
-- url     : https://prove2.me/submissions/9fcbe1b4-9174-4a60-8243-a02663e3d302

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_map_prod_add


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n) :
    ValO (fun o => rd Y p H o) n (imgFam Y p Ls n) ν := by
  intro Po hPo kind hk S t ht gr hg
  obtain ⟨P, hP, hQ⟩ := hPo
  obtain ⟨f, hf, he⟩ := hv hs P hP Po hQ kind hk S t ht gr hg
  have hx := hν _ ⟨P, hP, f, hf, rfl⟩
  rw [he, map_prod_add] at hx
  exact hx
end Formalism.L2.FormalSeriesBounds.RF
