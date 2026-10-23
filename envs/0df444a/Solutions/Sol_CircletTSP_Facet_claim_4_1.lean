-- Prove2me | solution 1 for CircletTSP.Facet.claim_4_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:18:21.944168+00:00
-- url     : https://prove2.me/submissions/56c2b1a5-8b6c-4b9d-bd09-ac40f3167aba

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

set_option autoImplicit false

namespace CircletTSP.Facet.DihedralProof

open Fin.NatCast

lemma cycLen_eq_min_sub {n : ℕ} (u v : Fin n) :
    cycLen n u v = min (u - v).val (v - u).val := by
  let : NeZero n := u.neZero
  have hu := u.isLt
  have hv := v.isLt
  have h₁ := Fin.intCast_val_sub_eq_sub_add_ite u v
  have h₂ := Fin.intCast_val_sub_eq_sub_add_ite v u
  rcases lt_trichotomy u.val v.val with h | h | h
  · have hle : u ≤ v := le_of_lt h
    have hnle : ¬ v ≤ u := by omega
    simp only [if_neg hnle, if_pos hle] at h₁ h₂
    simp only [cycLen, Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt h)]
    omega
  · have huv : u = v := Fin.ext h
    subst v
    simp [cycLen]
  · have hle : v ≤ u := le_of_lt h
    have hnle : ¬ u ≤ v := by omega
    simp only [if_neg hnle, if_pos hle] at h₁ h₂
    rw [cycLen, Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt h)]
    omega

lemma cycLen_symm {n : ℕ} (u v : Fin n) : cycLen n u v = cycLen n v u := by
  simp only [cycLen_eq_min_sub, min_comm]

lemma cycLen_sub {n : ℕ} [NeZero n] (u v a : Fin n) :
    cycLen n (u - a) (v - a) = cycLen n u v := by
  simp only [cycLen_eq_min_sub]
  have h₁ : u - a - (v - a) = u - v := by abel
  have h₂ : v - a - (u - a) = v - u := by abel
  rw [h₁, h₂]

lemma cycLen_neg {n : ℕ} [NeZero n] (u v : Fin n) :
    cycLen n (-u) (-v) = cycLen n u v := by
  simp only [cycLen_eq_min_sub]
  have h₁ : -u - -v = v - u := by abel
  have h₂ : -v - -u = u - v := by abel
  rw [h₁, h₂, min_comm]

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma tourVec_trans {n : ℕ} (π σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec (π.trans σ) (σ u) (σ v) = MetricTSP.tourVec π u v := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps]

lemma lenCount_double {n : ℕ} (i : ℕ) (hi : 0 < i) (x : Fin n → Fin n → ℝ)
    (hx : ∀ u v, x u v = x v u) :
    2 * lenCount n i x = ∑ u : Fin n, ∑ v : Fin n,
      if cycLen n u v = i then x u v else 0 := by
  have hpair (u v : Fin n) :
      (if u < v ∧ cycLen n u v = i then x u v else 0) +
        (if v < u ∧ cycLen n v u = i then x v u else 0) =
          if cycLen n u v = i then x u v else 0 := by
    rcases lt_trichotomy u v with h | h | h
    · simp only [h, not_lt_of_ge h.le, true_and, false_and, ite_false, add_zero]
    · subst v
      simp [cycLen, Ne.symm (Nat.ne_of_gt hi)]
    · simp only [h, not_lt_of_ge h.le, true_and, false_and, ite_false, zero_add,
        ← cycLen_symm u v, ← hx u v]
  have hsum := congrArg (fun f : Fin n → Fin n → ℝ => ∑ u, ∑ v, f u v) (funext fun u => funext (hpair u))
  simp only [Finset.sum_add_distrib] at hsum
  have hswap : (∑ u : Fin n, ∑ v : Fin n,
      if v < u ∧ cycLen n v u = i then x v u else 0) = lenCount n i x := by
    rw [Finset.sum_comm]
    rfl
  change lenCount n i x + _ = _ at hsum
  rw [hswap] at hsum
  linarith

lemma lenCount_trans {n : ℕ} (π σ : Equiv.Perm (Fin n))
    (hσ : ∀ u v, cycLen n (σ u) (σ v) = cycLen n u v) (i : ℕ) (hi : 0 < i) :
    lenCount n i (MetricTSP.tourVec (π.trans σ)) = lenCount n i (MetricTSP.tourVec π) := by
  have hleft := lenCount_double i hi (MetricTSP.tourVec (π.trans σ)) (tourVec_symm _)
  have hright := lenCount_double i hi (MetricTSP.tourVec π) (tourVec_symm _)
  have hsum : (∑ u : Fin n, ∑ v : Fin n,
      if cycLen n u v = i then MetricTSP.tourVec (π.trans σ) u v else 0) =
      ∑ u : Fin n, ∑ v : Fin n,
        if cycLen n u v = i then MetricTSP.tourVec π u v else 0 := by
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro v _
    rw [hσ, tourVec_trans]
  linarith

lemma circletForm_trans {n : ℕ} (π σ : Equiv.Perm (Fin n))
    (hσ : ∀ u v, cycLen n (σ u) (σ v) = cycLen n u v) :
    circletForm n (MetricTSP.tourVec (π.trans σ)) = circletForm n (MetricTSP.tourVec π) := by
  unfold circletForm
  apply Finset.sum_congr rfl
  intro i hi
  rw [lenCount_trans π σ hσ i (Finset.mem_Icc.mp hi).1]

def translation {n : ℕ} [NeZero n] (a : Fin n) : Equiv.Perm (Fin n) where
  toFun u := u - a
  invFun u := u + a
  left_inv _ := sub_add_cancel _ _
  right_inv _ := add_sub_cancel_right _ _

def reflection (n : ℕ) [NeZero n] : Equiv.Perm (Fin n) where
  toFun u := -u
  invFun u := -u
  left_inv _ := neg_neg _
  right_inv _ := neg_neg _

lemma shift_eq_add {n : ℕ} [NeZero n] (u : Fin n) (k : ℕ) :
    shift u k = u + (k : Fin n) := by
  apply Fin.ext
  simp [shift, Fin.add_def, Nat.add_mod]

lemma adj_trans {n : ℕ} {π σ : Equiv.Perm (Fin n)} {u v : Fin n} (h : Adj π u v) :
    Adj (π.trans σ) (σ u) (σ v) := (tourVec_trans π σ u v).trans h

end CircletTSP.Facet.DihedralProof

namespace CircletTSP.Facet.DihedralProof

open Fin.NatCast

lemma reflection_images (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (u : Fin n) :
    reflection n u = shift (-u - 1) 1 ∧
    reflection n (shift u 1) = -u - 1 ∧
    reflection n (shift u (n / 2)) = shift (-u - 1) (1 + n / 2) ∧
    reflection n (shift u (1 + n / 2)) = shift (-u - 1) (n / 2) := by
  have hd : ((n / 2 : ℕ) : Fin n) + ((n / 2 : ℕ) : Fin n) = 0 := by
    rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, Fin.natCast_self]
  have hneg : -((n / 2 : ℕ) : Fin n) = ((n / 2 : ℕ) : Fin n) := by
    calc
      _ = -((n / 2 : ℕ) : Fin n) + (((n / 2 : ℕ) : Fin n) + ((n / 2 : ℕ) : Fin n)) := by rw [hd, add_zero]
      _ = _ := by abel
  simp only [reflection, Equiv.coe_fn_mk, shift_eq_add, Nat.cast_one, Nat.cast_add,
    neg_add_rev, hneg]
  constructor
  · abel
  constructor
  · abel
  constructor <;> abel

lemma reflection_exchanges (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    (∀ (π : Equiv.Perm (Fin n)) (u : Fin n), IsStructB2 π u →
      ∃ (π' : Equiv.Perm (Fin n)) (u' : Fin n),
        circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
          IsStructB1 π' u') ∧
    (∀ (π : Equiv.Perm (Fin n)) (u : Fin n), IsStructB1 π u →
      ∃ (π' : Equiv.Perm (Fin n)) (u' : Fin n),
        circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
          IsStructB2 π' u') := by
  let : NeZero n := ⟨by omega⟩
  let σ := reflection n
  have hcost (π : Equiv.Perm (Fin n)) := circletForm_trans π σ (fun a b => cycLen_neg a b)
  constructor
  · intro π u h
    refine ⟨π.trans σ, -u - 1, hcost π, ?_⟩
    obtain ⟨h₀, h₁, hd, h₁d⟩ := reflection_images n h4 u
    have he₁ := adj_trans (σ := σ) h.1
    have he₂ := adj_trans (σ := σ) h.2.1
    have he₃ := adj_trans (σ := σ) h.2.2
    change Adj (π.trans σ) (reflection n u) (reflection n (shift u 1)) at he₁
    change Adj (π.trans σ) (reflection n (shift u 1)) (reflection n (shift u (1 + n / 2))) at he₂
    change Adj (π.trans σ) (reflection n (shift u (1 + n / 2))) (reflection n (shift u (n / 2))) at he₃
    rw [h₀, h₁] at he₁
    rw [h₁, h₁d] at he₂
    rw [h₁d, hd] at he₃
    exact ⟨he₁, he₂, he₃⟩
  · intro π u h
    refine ⟨π.trans σ, -u - 1, hcost π, ?_⟩
    obtain ⟨h₀, h₁, hd, h₁d⟩ := reflection_images n h4 u
    have he₁ := adj_trans (σ := σ) h.1
    have he₂ := adj_trans (σ := σ) h.2.1
    have he₃ := adj_trans (σ := σ) h.2.2
    change Adj (π.trans σ) (reflection n (shift u 1)) (reflection n u) at he₁
    change Adj (π.trans σ) (reflection n u) (reflection n (shift u (n / 2))) at he₂
    change Adj (π.trans σ) (reflection n (shift u (n / 2))) (reflection n (shift u (1 + n / 2))) at he₃
    rw [h₁, h₀] at he₁
    rw [h₀, hd] at he₂
    rw [hd, h₁d] at he₃
    exact ⟨he₁, he₂, he₃⟩

end CircletTSP.Facet.DihedralProof

open CircletTSP.Facet

/-- Claim 4.1 (p. 13), in the form its proof gives: relabelling vertex `i` as `n - i` turns a
Hamiltonian cycle containing structure B2 of Figure 4 into one of the same circlet cost containing
structure B1, and vice versa. In particular a counterexample to Theorem 3.1 with a B2 yields one
with a B1. -/
theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    (∀ (π : Equiv.Perm (Fin n)) (u : Fin n), IsStructB2 π u →
      ∃ (π' : Equiv.Perm (Fin n)) (u' : Fin n),
        circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
          IsStructB1 π' u') ∧
    (∀ (π : Equiv.Perm (Fin n)) (u : Fin n), IsStructB1 π u →
      ∃ (π' : Equiv.Perm (Fin n)) (u' : Fin n),
        circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
          IsStructB2 π' u') :=
  DihedralProof.reflection_exchanges n hn h4


