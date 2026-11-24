-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_sum_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:54.161675+00:00
-- url     : https://prove2.me/submissions/d569a019-baa8-4c17-887f-a138cef2beda

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_Yk
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_out_mk
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_neg_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_nsmul_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_nsmul_right
import Theorems.Thm_Formalism_IndefR_Fin_Four_out_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hχl hχr hχ0 hLL hdY
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} [Fintype (Qt k (L ⊓ X))] {y : W} (hy : y ∈ Yk L Y k) :
    ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y =
      if y ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0 := by
  classical
  have hy' := mem_Yk.1 hy
  split_ifs with hyL
  · have h1 : ∀ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 1 := fun b =>
      hLL _ (b.out : ↥(L ⊓ X)).2 y (AddSubgroup.mem_inf.2 ⟨hyL, hy'.1⟩)
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · have hne : ¬ ∀ x ∈ L ⊓ X, χ x y = 1 := fun hall => hyL (hdY y hy'.1 hall)
    push_neg at hne
    obtain ⟨u, hu, hχu⟩ := hne
    let m : Qt k (L ⊓ X) := QuotientAddGroup.mk ⟨u, hu⟩
    have hkey : ∀ b : Qt k (L ⊓ X), χ (((b + m).out : ↥(L ⊓ X)) : W) y = χ ((b.out : ↥(L ⊓ X)) : W) y * χ u y := by
      intro b
      have h1 : b + m = QuotientAddGroup.mk (b.out + ⟨u, hu⟩) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      obtain ⟨v, hv, hout⟩ := out_mk k (L ⊓ X) (b.out + ⟨u, hu⟩)
      rw [h1]
      have h2 : (((QuotientAddGroup.mk (b.out + ⟨u, hu⟩) : Qt k (L ⊓ X)).out : ↥(L ⊓ X)) : W) =
          ((b.out : ↥(L ⊓ X)) : W) + u + -(k • v) := by
        rw [eq_sub_of_add_eq hout]; push_cast; abel
      rw [h2, hχl, hχl, chi_neg_left hχl hχ0, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0,
        hLL v hv _ (AddSubgroup.mem_inf.2 ⟨hy'.2, Y.nsmul_mem hy'.1 k⟩), inv_one, mul_one]
    have hshift : ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y =
        (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y) * χ u y := by
      rw [Finset.sum_mul]
      rw [← Fintype.sum_equiv (Equiv.addRight m) (fun b => χ (((b + m).out : ↥(L ⊓ X)) : W) y)
        (fun b => χ ((b.out : ↥(L ⊓ X)) : W) y) (fun b => rfl)]
      exact Finset.sum_congr rfl fun b _ => hkey b
    have hz : (1 - χ u y) * ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 0 := by
      linear_combination hshift
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd (sub_eq_zero.1 h).symm hχu
    · exact h
end Formalism.IndefR.Fin.Four
