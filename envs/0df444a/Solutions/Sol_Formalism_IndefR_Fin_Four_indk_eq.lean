-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.indk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:28.540807+00:00
-- url     : https://prove2.me/submissions/463f22c0-e2c0-4706-8273-ba639d34b7b6

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_finite
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_sum

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
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} (hk : 0 < k) (t : W) :
    indk L X k t = (Nat.card (Gk L Y k) : ℂ)⁻¹ * ∑ᶠ g : Gk L Y k,
      χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  have hcard : (Nat.card (Gk L Y k) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold indk
  by_cases htLX : t ∈ L ∧ t ∈ X
  · rw [if_pos htLX]
    simp only [mul_one]
    rw [chi_sum hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk (AddSubgroup.mem_inf.mpr htLX)]
    split_ifs
    · exact (inv_mul_cancel₀ hcard).symm
    · simp
  · have hnot : t ∉ smulSub k (L ⊓ X) := by
      intro hm
      obtain ⟨s, hs, hst⟩ := AddSubgroup.mem_map.mp hm
      apply htLX
      rw [← hst]
      exact AddSubgroup.mem_inf.mp (nsmul_mem hs k)
    rw [if_neg hnot, if_neg htLX]
    simp
end Formalism.IndefR.Fin.Four
