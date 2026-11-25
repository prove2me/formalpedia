-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.tfun_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:19.486798+00:00
-- url     : https://prove2.me/submissions/717b85c0-2777-49ac-8d99-51fd2d10253a

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_finsum_add__7757e6fab932
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_add
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_support_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)
include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') :
    tfun ρ χ L X Y f₀ (Φ + Φ') = tfun ρ χ L X Y f₀ Φ + tfun ρ χ L X Y f₀ Φ' := by
  unfold tfun
  rw [← finsum_add' (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)
    (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h')]
  refine finsum_congr fun q => ?_
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy, term, coef_add hχl hχr hχ0 hLL hfinX hoY h h' _ hy, add_smul]
  · simp only [if_neg hy, add_zero]
end Formalism.IndefR.Fin.Four
