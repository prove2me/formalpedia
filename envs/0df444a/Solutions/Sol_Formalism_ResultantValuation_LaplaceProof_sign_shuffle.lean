-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.sign_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:45.517158+00:00
-- url     : https://prove2.me/submissions/67510d79-0a70-41ea-9317-3df88844be65

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_perm_sign_eq_inversion_sign
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_prod_finPairsLT
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_card_compl_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
section
open Finset Equiv
noncomputable section
namespace Formalism.ResultantValuation
namespace LaplaceProof
variable {a b : ℕ}
private theorem perm_inversion_sign_eq_prod {n : ℕ} (g : Perm (Fin n)) :
    Perm.signAux g = ∏ x : Fin n, ∏ y : Fin n,
      if y < x then (if g x ≤ g y then (-1 : ℤˣ) else 1) else 1 := by
  rw [Perm.signAux.eq_1, prod_finPairsLT]
  all_goals rfl
private lemma prod_fin_add_lt_split (F : Fin (a + b) → Fin (a + b) → ℤˣ) :
    ∏ x : Fin (a + b), ∏ y : Fin (a + b), (if y < x then F x y else 1) =
      (∏ i : Fin a, ∏ i' : Fin a, if i' < i then F (Fin.castAdd b i) (Fin.castAdd b i') else 1) *
      ((∏ j : Fin b, ∏ i : Fin a, F (Fin.natAdd a j) (Fin.castAdd b i)) *
       (∏ j : Fin b, ∏ j' : Fin b, if j' < j then F (Fin.natAdd a j) (Fin.natAdd a j') else 1)) := by
  have hlt : ∀ (i : Fin a) (j : Fin b), (i : ℕ) < a + (j : ℕ) := fun i j => by
    have := i.isLt
    omega
  have hnlt : ∀ (i : Fin a) (j : Fin b), ¬ (a + (j : ℕ) < (i : ℕ)) := fun i j => by
    have := i.isLt
    omega
  simp only [Fin.prod_univ_add, Finset.prod_mul_distrib, Fin.lt_iff_val_lt_val, Fin.coe_castAdd,
    Fin.coe_natAdd, add_lt_add_iff_left, hlt, hnlt, ↓reduceIte, Finset.prod_const_one, mul_one, one_mul,
    mul_assoc]
private lemma card_filter_compl_orderEmbOfFin_le (J : Finset (Fin (a + b))) (hc : Jᶜ.card = b) (t : Fin (a + b)) :
    (univ.filter (fun j : Fin b => Jᶜ.orderEmbOfFin hc j ≤ t)).card = (Jᶜ.filter (· ≤ t)).card := by
  rw [← Finset.card_map (Jᶜ.orderEmbOfFin hc).toEmbedding]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finset.orderEmbOfFin_mem _ _ _, hj⟩
  · rintro ⟨hy, hyt⟩
    have hr : y ∈ Set.range (Jᶜ.orderEmbOfFin hc) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hy
    obtain ⟨j, rfl⟩ := hr
    exact ⟨j, hyt, rfl⟩
private lemma sum_val_eq_sum_orderEmbOfFin (J : Finset (Fin (a + b))) (h : J.card = a) :
    ∑ j ∈ J, (j : ℕ) = ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) := by
  have hJ : J = Finset.univ.map (J.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hy
      have hr : y ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hy
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact Finset.orderEmbOfFin_mem _ _ _
  conv_lhs => rw [hJ]
  exact Finset.sum_map _ _ _
end LaplaceProof
end Formalism.ResultantValuation
end
end

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) :
    Perm.sign (shuffle J h hc) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ J, (j : ℕ)) := by
  rw [perm_sign_eq_inversion_sign, perm_inversion_sign_eq_prod, prod_fin_add_lt_split]
  have hA : (∏ i : Fin a, ∏ i' : Fin a, if i' < i then (if shuffle J h hc (Fin.castAdd b i) ≤
      shuffle J h hc (Fin.castAdd b i') then (-1 : ℤˣ) else 1) else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun i' _ => ?_
    split_ifs with h1 h2
    · rw [shuffle_castAdd, shuffle_castAdd, OrderEmbedding.le_iff_le] at h2
      exact absurd h2 (not_le.mpr h1)
    · rfl
    · rfl
  have hD : (∏ j : Fin b, ∏ j' : Fin b, if j' < j then (if shuffle J h hc (Fin.natAdd a j) ≤
      shuffle J h hc (Fin.natAdd a j') then (-1 : ℤˣ) else 1) else 1) = 1 := by
    refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun j' _ => ?_
    split_ifs with h1 h2
    · rw [shuffle_natAdd, shuffle_natAdd, OrderEmbedding.le_iff_le] at h2
      exact absurd h2 (not_le.mpr h1)
    · rfl
    · rfl
  rw [hA, hD, one_mul, mul_one]
  simp only [shuffle_castAdd, shuffle_natAdd]
  rw [Finset.prod_comm]
  have hrow : ∀ i : Fin a, (∏ j : Fin b, if Jᶜ.orderEmbOfFin hc j ≤ J.orderEmbOfFin h i then
      (-1 : ℤˣ) else 1) = (-1) ^ (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card := by
    intro i
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_filter_compl_orderEmbOfFin_le]
  refine (Finset.prod_congr rfl fun i _ => hrow i).trans ?_
  rw [Finset.prod_pow_eq_pow_sum, sum_val_eq_sum_orderEmbOfFin J h]
  have hsum : ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) =
      ∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + a * (a - 1) / 2 := by
    rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) a, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (card_compl_le J h i).symm
  rw [hsum]
  generalize (∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card) = C
  generalize a * (a - 1) / 2 = T
  rw [show T + (C + T) = C + 2 * T by ring, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
end Formalism.ResultantValuation.LaplaceProof
