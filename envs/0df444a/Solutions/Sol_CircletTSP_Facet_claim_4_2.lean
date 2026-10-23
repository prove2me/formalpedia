-- Prove2me | solution 1 for CircletTSP.Facet.claim_4_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:18:23.494012+00:00
-- url     : https://prove2.me/submissions/7a003075-991d-4b55-a9ef-1723561203aa

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

lemma rotation_normalizes (n : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    (IsStructA π u → ∃ π' : Equiv.Perm (Fin n),
      circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
        IsStructA π' ⟨0, hn⟩) ∧
    (IsStructB2 π u → ∃ π' : Equiv.Perm (Fin n),
      circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
        IsStructB2 π' ⟨0, hn⟩) := by
  let : NeZero n := ⟨by omega⟩
  let σ := translation u
  have hcost := circletForm_trans π σ (fun a b => cycLen_sub a b u)
  have hu : σ u = (⟨0, hn⟩ : Fin n) := by simp [σ, translation]
  have hs (k : ℕ) : σ (shift u k) = shift (⟨0, hn⟩ : Fin n) k := by
    change shift u k - u = shift (⟨0, hn⟩ : Fin n) k
    simp only [shift_eq_add]
    change (u + (k : Fin n)) - u = 0 + (k : Fin n)
    abel
  constructor
  · intro h
    refine ⟨π.trans σ, hcost, ?_⟩
    have h₁ := adj_trans (σ := σ) h.1
    have h₂ := adj_trans (σ := σ) h.2.1
    have h₃ := adj_trans (σ := σ) h.2.2
    rw [hs, hu] at h₁
    rw [hs, hu] at h₂
    rw [hs, hs] at h₃
    exact ⟨h₁, h₂, h₃⟩
  · intro h
    refine ⟨π.trans σ, hcost, ?_⟩
    have h₁ := adj_trans (σ := σ) h.1
    have h₂ := adj_trans (σ := σ) h.2.1
    have h₃ := adj_trans (σ := σ) h.2.2
    rw [hs, hu] at h₁
    rw [hs, hs] at h₂
    rw [hs, hs] at h₃
    exact ⟨h₁, h₂, h₃⟩

end CircletTSP.Facet.DihedralProof

open CircletTSP.Facet

/-- Claim 4.2 (p. 13), in the form its proof gives: a Hamiltonian cycle containing structure A
(resp. B2) of Figure 4 at some `u` can be relabelled into one of the same circlet cost containing
the same structure at `u = 1` (the vertex `0` in 0-based labels). -/
theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    (IsStructA π u → ∃ π' : Equiv.Perm (Fin n),
      circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
        IsStructA π' ⟨0, hn⟩) ∧
    (IsStructB2 π u → ∃ π' : Equiv.Perm (Fin n),
      circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
        IsStructB2 π' ⟨0, hn⟩) := by
  have _h4 := h4
  exact DihedralProof.rotation_normalizes n hn π u


