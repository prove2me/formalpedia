-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_mul_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:46.46357+00:00
-- url     : https://prove2.me/submissions/5820e12e-a5b0-4af6-9751-0b7032aaeda9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
namespace Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
theorem _root_.solution {k : Type*} [Field k] [Fintype k] [DecidableEq k] (c : k) :
    ((univ.filter (fun y : k × k => y.1 * y.2 = c)).card : ℤ) =
      ((Fintype.card k : ℤ) - 1) + 1 * (Fintype.card k : ℤ) * (if c = 0 then 1 else 0) := by
  have h1 : (univ.filter (fun y : k × k => y.1 * y.2 = c)).card =
      ∑ a : k, (univ.filter (fun b : k => a * b = c)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have h2 : ∀ a : k, a ≠ 0 → (univ.filter (fun b : k => a * b = c)).card = 1 := by
    intro a ha
    rw [Finset.card_eq_one]
    refine ⟨a⁻¹ * c, ?_⟩
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [← h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    · intro h
      rw [h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hk : 1 ≤ Fintype.card k := Fintype.card_pos
  have h0 : (univ.filter (fun b : k => (0 : k) * b = c)).card = if c = 0 then Fintype.card k else 0 := by
    split_ifs with hc
    · subst hc
      simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ h
      exact hc (by rw [← h, zero_mul])
  rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)),
    Finset.sum_congr rfl fun a ha => h2 a (Finset.ne_of_mem_erase ha), h0]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  split_ifs <;> push_cast [Nat.cast_sub hk] <;> ring
end Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
