-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_ev_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:24.937798+00:00
-- url     : https://prove2.me/submissions/b013fc99-24b1-4166-a832-0823e61bc4e1

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
    coeff (E2 ((0 : Fin 2), i0) ((1 : Fin 2), j0)) (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] h) =
      ∑ i, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j0)) h * coeff (Finsupp.single ((0 : Fin 1), i0) 1) (φ i) := by
  unfold ev
  rw [coeff_subst_bil (T1 := Tg dd 0) (T2 := Tg dd 1) (κ := Fin dd)
    (a := fun p : Fin 2 × Fin dd => ![comp1 φ (pt C (n := 2) dd 0), pt C dd 1] p.1 p.2) ?_ (fun i => van_comp1_pt hφ 0 i)
    (fun j => van_X (show ((1 : Fin 2), j) ∈ Tg dd 1 from rfl)) (ne01 i0 j0)
    (fun e => absurd (show (1 : Fin 2) = 0 from e) (by decide))
    (fun e => absurd (show (0 : Fin 2) = 1 from e) (by decide)) hh]
  · apply Finset.sum_congr rfl
    intro i _
    have h1 : ∀ j, coeff (Finsupp.single ((1 : Fin 2), j0) 1)
        ((![comp1 φ (pt C (n := 2) dd 0), pt C dd 1] ((1 : Fin 2), j).1) ((1 : Fin 2), j).2) = if j = j0 then 1 else 0 :=
      fun j => coeff_single_X 1 j j0
    have h2 : coeff (Finsupp.single ((0 : Fin 2), i0) 1)
        ((![comp1 φ (pt C (n := 2) dd 0), pt C dd 1] ((0 : Fin 2), i).1) ((0 : Fin 2), i).2) =
          coeff (Finsupp.single ((0 : Fin 1), i0) 1) (φ i) := coeff_comp1_pt φ 0 i i0
    simp only [h1, h2]
    simp
  · rintro ⟨g, i⟩
    have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hall g with rfl | rfl
    · exact (van_comp1_pt hφ 0 i).const
    · exact constantCoeff_X _
end Formalism.L2.FormalSeriesBounds
