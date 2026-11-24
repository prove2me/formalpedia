-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.isSB_indk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:22.12429+00:00
-- url     : https://prove2.me/submissions/d7f5f57e-7e6b-464d-81f9-1eac87b9ee81

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq

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
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} (hk : 0 < k) : IsSB L X (indk L X k) := by
  have hmem : ∀ t, indk L X k t ≠ 0 → t ∈ L ⊓ X := by
    intro t ht
    unfold indk at ht
    split_ifs at ht with h
    · obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp h
      exact nsmul_mem hs k
    · exact absurd rfl ht
  refine ⟨fun t ht => (AddSubgroup.mem_inf.mp (hmem t ht)).2, k, hk, ?_,
    fun t ht => nsmul_mem (AddSubgroup.mem_inf.mp (hmem t ht)).1 k⟩
  intro u hu t
  have hku : k • u ∈ smulSub k (L ⊓ X) := AddSubgroup.mem_map_of_mem _ hu
  have hiff : t + k • u ∈ smulSub k (L ⊓ X) ↔ t ∈ smulSub k (L ⊓ X) :=
    (smulSub k (L ⊓ X)).add_mem_cancel_right hku
  unfold indk
  by_cases h : t ∈ smulSub k (L ⊓ X)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (mt hiff.mp h), if_neg h]
end Formalism.IndefR.Fin.Four
