-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.first_family_subset_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:06:08.392231+00:00
-- url     : https://prove2.me/submissions/0deb45ea-27ab-4405-8288-145443b69db8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_isImgS_subG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_hd_eq_one

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ}
    (plc : Fin N × Fin 2 ↪ Fin n) :
    selfConjTuplesInLattice Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc ⊆
      imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc := by
  intro Po hPo
  refine ⟨subG Dw.mult lab.tau lab.gm plc (∏ o, toAll o (Po o)), hPo, ?_⟩
  exact isImgS_subG plc (fun o => Y.rawSelf (selfOfLab ha hg o))
    (fun (ℓ : LtN Dw n) i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)) (fun o => selfLieBasisVector C3 ι lab o) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) ha.inj (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) _
end Formalism.L2.FormalSeriesBounds.RF
