-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.PairData.yOf_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:56:58.114366+00:00
-- url     : https://prove2.me/submissions/07c4b700-4920-4d04-b359-4fec9ff411a7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
private theorem ge_zero_mul_of_vf (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  unfold VF.Ge at *
  rw [V.v.map_mul]
  rw [WithTop.coe_zero] at *
  exact add_nonneg ha hb
private theorem ge_zero_finset_sum (V : VF C) {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    unfold VF.Ge
    rw [AddValuation.map_zero]
    exact le_top
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    unfold VF.Ge at h1 h2 ⊢
    exact le_trans (le_min h1 h2) (V.v.map_add _ _)
section Chart
open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
end Chart
end Formalism.L2.FormalSeriesBounds
end
end

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
namespace PairData
theorem _root_.solution {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) {χ : PS C 1 dd} (h : Y.IsChar χ)
    (x : I g) : V.Ge 0 (p.yOf g χ x) := by
  unfold PairData.yOf
  exact ge_zero_finset_sum V _ _ fun i _ => ge_zero_mul_of_vf V (h.1 _) (p.u_int g x i)
end PairData
end Formalism.L2.FormalSeriesBounds
