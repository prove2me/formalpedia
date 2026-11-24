-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.T_indk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:43.836567+00:00
-- url     : https://prove2.me/submissions/7bfccb4c-b160-4179-94b0-f7b3b39c7889

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_finite
import Theorems.Thm_Formalism_IndefR_Fin_Four_indk_eq
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr


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
theorem _root_.solution (T : (W → ℂ) →ₗ[ℂ] V)
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀) {k : ℕ} (hk : 0 < k) :
    T (indk L X k) = Pk ρ L Y f₀ k := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  have h1 : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
    refine ⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩
    · by_contra h
      exact ht (if_neg (fun h' => h h'.2))
    · have hu' := AddSubgroup.mem_inf.mp hu
      have hiff : (t + u ∈ L ∧ t + u ∈ X) ↔ (t ∈ L ∧ t ∈ X) :=
        and_congr (L.add_mem_cancel_right hu'.1) (X.add_mem_cancel_right hu'.2)
      show (if t + 1 • u ∈ L ∧ t + 1 • u ∈ X then (1 : ℂ) else 0) = if t ∈ L ∧ t ∈ X then 1 else 0
      rw [one_smul]
      by_cases h : t ∈ L ∧ t ∈ X
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    · rw [one_smul]
      by_contra h
      exact ht (if_neg (fun h' => h h'.1))
  have hfun : indk L X k = ∑ g : Gk L Y k, ((Nat.card (Gk L Y k) : ℂ)⁻¹ •
      (fun t => χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0))) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [indk_eq hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk t, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [hfun, map_sum]
  simp only [map_smul]
  unfold Pk
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  congr 1
  have h2 := hmo _ h1 _ (Gk_out g).1
  rw [h2, hva]
end Formalism.IndefR.Fin.Four
