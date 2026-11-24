-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.card_dot_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:43.45212+00:00
-- url     : https://prove2.me/submissions/5085e5e5-f60f-4771-ac11-eb5a6d6b646d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_card_sum_norm_fibres
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_card_mul_fibre

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
theorem _root_.solution {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q)
    (M : ℕ) (hM : 1 ≤ M) (c : k) (hc : c ≠ 0) :
    (Nat.card {x : (Fin M → k) × (Fin M → k) // ∑ i, x.1 i * x.2 i = c} : ℤ) =
      (q : ℤ) ^ (2 * M - 1) - (q : ℤ) ^ (M - 1) := by
  classical
  have h := FiniteNormFibres.card_sum_norm_fibres (fun y : k × k => y.1 * y.2) (fun _ => True) (fun _ _ _ => trivial)
    (q : ℤ) 1 (by rw [Fintype.card_prod, hq]; push_cast; ring)
    (fun c _ => by rw [← hq]; convert FiniteNormFibres.card_mul_fibre c) M c trivial
  rw [if_neg hc, one_mul] at h
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    have h1 : q = 0 := by exact_mod_cast h0
    have := Fintype.card_pos (α := k)
    rw [hq, h1] at this
    exact lt_irrefl 0 this
  have e : {x : (Fin M → k) × (Fin M → k) // ∑ i, x.1 i * x.2 i = c} ≃
      {x : Fin M → k × k // ∑ i, (x i).1 * (x i).2 = c} :=
    (Equiv.arrowProdEquivProdArrow _ _ _).symm.subtypeEquiv (fun x => Iff.rfl)
  have key : (q : ℤ) * ((q : ℤ) ^ (2 * M - 1) - (q : ℤ) ^ (M - 1)) =
      (q : ℤ) ^ (2 * M) + (q : ℤ) ^ M * ((q : ℤ) * 0 - 1) := by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [show 2 * (M' + 1) - 1 = 2 * M' + 1 by omega, show M' + 1 - 1 = M' by omega]
    ring
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply mul_left_cancel₀ hq0
  rw [key]
  convert h using 3
end Formalism.HermitianLattices.Ext.L3
