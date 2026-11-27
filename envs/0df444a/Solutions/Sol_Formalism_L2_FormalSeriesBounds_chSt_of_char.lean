-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.chSt_of_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:33:43.1326+00:00
-- url     : https://prove2.me/submissions/cdbf4a11-1e9e-4170-927a-2ec92c83776b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_PairData_yOf_int
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [NeZero d] (hG : CharGermSt) (Y : FBChart C V O dd) (p : PairData Y d I) (h : CHCharSt Y p)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) : RawChart.CHSt Hc := by
  intro g a hbig w hw hw0
  obtain ⟨χ, hχ, h1, h2⟩ := h g a hbig w hw hw0
  refine ⟨fun ρ x => p.yOf g (χ ρ) x, fun ρ x => p.yOf_int g (hχ ρ) x, ?_, h1, h2⟩
  intro S t ht ρ
  exact hG C V O dd Y d I p Hc (χ ρ) (hχ ρ) g S t ht
end Formalism.L2.FormalSeriesBounds
