-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.card_herm_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:24.828783+00:00
-- url     : https://prove2.me/submissions/03bbb596-b939-43b2-aec1-8fa30c107da3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_card_sum_norm_fibres
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_card_norm_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (M : ℕ) (hM : 1 ≤ M) (c : k) (hc : σ c = c) (hc0 : c ≠ 0) :
    (Nat.card {x : Fin M → k // ∑ i, σ (x i) * x i = c} : ℤ) =
      (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by
  classical
  have h := FiniteNormFibres.card_sum_norm_fibres (fun y : k => σ y * y) (fun c => σ c = c)
    (fun c y hc => by simp only [map_sub, map_mul, hσ, hc]; ring) (q : ℤ) (-1)
    (by rw [hq]; push_cast; ring) (fun c hc => by convert FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc) M c hc
  rw [if_neg hc0, mul_pow] at h
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    have h1 : q = 0 := by exact_mod_cast h0
    have := Fintype.card_pos (α := k)
    rw [hq, h1] at this
    simp at this
  have key : (q : ℤ) * ((q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M)) =
      (q : ℤ) ^ (2 * M) + (-1) ^ M * (q : ℤ) ^ M * ((q : ℤ) * 0 - 1) := by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [show M' + 1 - 1 = M' by omega]
    ring
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply mul_left_cancel₀ hq0
  rw [key]
  convert h using 3
end Formalism.HermitianLattices.Ext.L3
