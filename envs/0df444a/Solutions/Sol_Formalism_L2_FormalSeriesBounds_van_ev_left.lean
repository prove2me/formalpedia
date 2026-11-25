-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_ev_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:13.567747+00:00
-- url     : https://prove2.me/submissions/80d29107-372e-4e9f-bd49-0973c1c74e2a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_comp1_pt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_fin_two_eq_zero_or_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {h : PS C 2 dd}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
    {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Van (Tg dd 0) (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] h) := by
  unfold ev
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} ?_ ?_ (hh 0)
  · rintro ⟨g, i⟩
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact (van_comp1_pt hφ 0 i).const
    · exact constantCoeff_X _
  · rintro ⟨g, i⟩ hs
    have hg : g = 0 := hs
    subst hg
    exact van_comp1_pt hφ 0 i
end Formalism.L2.FormalSeriesBounds
