-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_sum_norm_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:46.137829+00:00
-- url     : https://prove2.me/submissions/234aa317-de69-46b0-ab8d-7cc410954009

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
theorem _root_.solution {k X : Type*} [AddCommGroup k] [DecidableEq k] [Fintype X]
    (N : X → k) (S : k → Prop) (hS : ∀ c y, S c → S (c - N y)) (q ε : ℤ)
    (hX : (Fintype.card X : ℤ) = q ^ 2)
    (hN : ∀ c, S c → ((univ.filter (fun y => N y = c)).card : ℤ) =
      (q - ε) + ε * q * (if c = 0 then 1 else 0)) (M : ℕ) :
    ∀ c, S c → q * ((univ.filter (fun x : Fin M → X => ∑ i, N (x i) = c)).card : ℤ) =
      q ^ (2 * M) + (ε * q) ^ M * (q * (if c = 0 then 1 else 0) - 1) := by
  induction M with
  | zero =>
    intro c _
    by_cases h0 : c = 0
    · subst h0
      simp
    · simp [h0, Ne.symm h0]
  | succ M ih =>
    intro c hc
    have hsplit : ((univ.filter (fun x : Fin (M + 1) → X => ∑ i, N (x i) = c)).card : ℤ) =
        ∑ y : X, ((univ.filter (fun x : Fin M → X => ∑ i, N (x i) = c - N y)).card : ℤ) := by
      rw [← Nat.cast_sum]
      congr 1
      simp only [Finset.card_filter]
      rw [← (Fin.consEquiv (fun _ : Fin (M + 1) => X)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        eq_sub_iff_add_eq']
    have hcount : ∑ y : X, (if c - N y = 0 then (1 : ℤ) else 0) =
        ((univ.filter fun y => N y = c).card : ℤ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [sub_eq_zero, eq_comm]
    rw [hsplit, Finset.mul_sum, Finset.sum_congr rfl fun y _ => ih (c - N y) (hS c y hc)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [hcount, hN c hc, hX]
    ring
end Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
