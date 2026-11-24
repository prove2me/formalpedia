-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.model_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:13.036801+00:00
-- url     : https://prove2.me/submissions/56764f69-7c88-40bd-85bf-afd602872744

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_finite
import Theorems.Thm_Formalism_IndefR_Fin_Four_T_formula

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
include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} (hΦ : IsSB L X Φ) :
    T Φ ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)} := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  rw [T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]
  refine finsum_induction (fun v => v ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)})
    (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) (fun q => ?_)
  show Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) ∈ _
  by_cases h0 : Φ q.out = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    unfold Pk
    rw [map_smul, finsum_eq_sum_of_fintype, map_sum]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro g _
    exact Submodule.subset_span ⟨-q.out, neg_mem (hs _ h0), (g : QY L Y).out, (Gk_out g).1, rfl⟩
end Formalism.IndefR.Fin.Four
