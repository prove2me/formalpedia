-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.term_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:47:56.648798+00:00
-- url     : https://prove2.me/submissions/b6e96c12-78fd-4e32-ae30-2e7e1b6c74fa

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Theorems.Thm_Formalism_IndefR_Fin_Four_finite_nsmul_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_ne_zero

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
theorem _root_.solution {Φ : W → ℂ} (h : IsSB L X Φ) :
    (Function.support fun q : QX L X × QY L Y =>
      if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0).Finite := by
  obtain ⟨hs, k, hk, hi, hl⟩ := id h
  haveI := hfinX k hk
  haveI := hfinY k hk
  have hS1 := finite_nsmul_out (L ⊓ X) (htf k hk)
  have hS2 := finite_nsmul_out (L ⊓ Y) (htf k hk)
  refine (hS1.prod hS2).subset ?_
  rintro ⟨q1, q2⟩ hq
  rw [Function.mem_support] at hq
  split_ifs at hq with hy
  · have hc : coef χ L X Φ q1.out q2.out ≠ 0 := fun h0 => hq (by simp [term, h0])
    obtain ⟨⟨t, ht, hΦ⟩, hky⟩ := coef_ne_zero (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) h hk hi hy hc
    refine ⟨?_, ?_⟩
    · show k • q1.out ∈ L ⊓ X
      have hX : q1.out + t ∈ X := hs _ hΦ
      have hL' : k • (q1.out + t) ∈ L := hl _ hΦ
      have hx : q1.out ∈ X := by simpa using X.sub_mem hX ht.2
      refine ⟨?_, X.nsmul_mem hx k⟩
      have h5 : k • q1.out = k • (q1.out + t) - k • t := by rw [smul_add]; abel
      rw [h5]
      exact L.sub_mem hL' (L.nsmul_mem ht.1 k)
    · exact ⟨hky, Y.nsmul_mem hy k⟩
  · exact absurd rfl hq
end Formalism.IndefR.Fin.Four
