-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_ev_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:26.451988+00:00
-- url     : https://prove2.me/submissions/b3d95344-c0d6-413a-816b-d3299f493870

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_bil
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_comp1_pt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_comp1_pt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_single_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ne01
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const


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
variable {dd : ℕ}
variable {h : PS C 2 dd}
  (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
  {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0)
include hh hφ
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (i0 j0 : Fin dd) :
    coeff (E2 ((0 : Fin 2), i0) ((1 : Fin 2), j0)) (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) =
      ∑ j, coeff (E2 ((0 : Fin 2), i0) ((1 : Fin 2), j)) h * coeff (Finsupp.single ((0 : Fin 1), j0) 1) (φ j) := by
  unfold ev
  rw [coeff_subst_bil (T1 := Tg dd 0) (T2 := Tg dd 1) (κ := Fin dd)
    (a := fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, comp1 φ (pt C dd 1)] p.1 p.2) ?_
    (fun i => van_X (show ((0 : Fin 2), i) ∈ Tg dd 0 from rfl)) (fun j => van_comp1_pt hφ 1 j) (ne01 i0 j0)
    (fun e => absurd (show (1 : Fin 2) = 0 from e) (by decide))
    (fun e => absurd (show (0 : Fin 2) = 1 from e) (by decide)) hh]
  · have h1 : ∀ i, coeff (Finsupp.single ((0 : Fin 2), i0) 1)
        ((![pt C (n := 2) dd 0, comp1 φ (pt C dd 1)] ((0 : Fin 2), i).1) ((0 : Fin 2), i).2) = if i = i0 then 1 else 0 :=
      fun i => coeff_single_X 0 i i0
    have h2 : ∀ j, coeff (Finsupp.single ((1 : Fin 2), j0) 1)
        ((![pt C (n := 2) dd 0, comp1 φ (pt C dd 1)] ((1 : Fin 2), j).1) ((1 : Fin 2), j).2) =
          coeff (Finsupp.single ((0 : Fin 1), j0) 1) (φ j) := fun j => coeff_comp1_pt φ 1 j j0
    simp only [h1, h2]
    simp
  · rintro ⟨g, i⟩
    have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hall g with rfl | rfl
    · exact constantCoeff_X _
    · exact (van_comp1_pt hφ 1 i).const
end Formalism.L2.FormalSeriesBounds
