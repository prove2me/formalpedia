-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.sys_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:33.06289+00:00
-- url     : https://prove2.me/submissions/8c7bea5d-e7f2-41b2-bfbc-380e104ce965

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) (c : I g) :
    ∃ γ : Fin dd → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (un1 (Y.lg i)) =
      ∑ c' : I g, p.u g c' i • tyS V.l (fun s => S.al c s c') := by
  have hm : S.cur c ∈ (Y.raw p).TySet V g := (S.curve c).1
  obtain ⟨γ, lam, hγ, -, hlog, -⟩ := hm
  exact ⟨γ, hγ, hlog⟩
end Formalism.L2.FormalSeriesBounds.FormalGermZero
