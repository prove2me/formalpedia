-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.card_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:31.975072+00:00
-- url     : https://prove2.me/submissions/bd2cc8f9-aeb6-4a9f-8f0c-47bc7e7c17ab

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ s a : ℕ) (hcop : m₀.Coprime s) (hm : m₀ ≠ 0) (hs : s ≠ 0) :
    ((range (m₀ * s)).filter (fun b => b % m₀ = a % m₀ ∧ b.Coprime s)).card = s.totient := by
  have hpos : 0 < s := Nat.pos_of_ne_zero hs
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_bij (fun b _ => b % s)
  · intro b hb
    simp only [mem_filter, mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    show Nat.gcd s (b % s) = 1
    rw [Nat.gcd_comm, ← Nat.gcd_rec]
    exact hb.2.2.symm
  · intro b₁ hb₁ b₂ hb₂ h
    simp only [mem_filter, mem_range] at hb₁ hb₂
    have h1 : b₁ ≡ b₂ [MOD m₀] := hb₁.2.1.trans hb₂.2.1.symm
    have h2 : b₁ ≡ b₂ [MOD s] := h
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    have h4 : b₁ % (m₀ * s) = b₂ % (m₀ * s) := h3
    rwa [Nat.mod_eq_of_lt hb₁.1, Nat.mod_eq_of_lt hb₂.1] at h4
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop a r
    have hk1' : k % m₀ = a % m₀ := hk1
    have hk2' : k % s = r % s := hk2
    refine ⟨k % (m₀ * s), ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hm hs)), ?_, ?_⟩
      · rw [Nat.mod_mul_right_mod]
        exact hk1'
      · show Nat.gcd _ s = 1
        rw [Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mul_left_mod, hk2', Nat.mod_eq_of_lt hr.1]
        exact hr.2.symm
    · show k % (m₀ * s) % s = r
      rw [Nat.mod_mul_left_mod, hk2', Nat.mod_eq_of_lt hr.1]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
