-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.labSGeo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:02.912924+00:00
-- url     : https://prove2.me/submissions/f0b63aa6-0b0f-47f6-a0c6-8cdfebbff231

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCH
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelfCuts
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_a3uvec_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_embedding_conjugate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_embedding_integral


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
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable {Orb : Type} {d : ℕ} [NeZero d]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (hstar : ∀ a : 𝓞 E, star a = H.bar a) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d} (ha : LabSArith V io ι lab)
    (h : LabSGeoCore C3 ι Y lab) : LabSGeo C3 ι Y lab where
  em_int := fun _ _ x => embedding_integral ι _ x
  em_conj := fun o a x => by rw [← ha.conj o a]; exact (embedding_conjugate hstar ι _ x).symm
  e_int := fun _ _ i => a3uvec_int C3 hι _ i
  e_eig := h.e_eig
  e_sat := h.e_sat
  e_full := h.e_full
end Formalism.L2.FormalSeriesBounds
