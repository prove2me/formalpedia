-- Prove2me | solution 1 for AutoregLTF.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:28:00.02645+00:00
-- url     : https://prove2.me/submissions/578c8b8c-70da-48e7-9f48-0b923dc6ec25

import Mathlib
import Definitions.Def_AutoregLTF_gen16
import Definitions.Def_AutoregLTF_sigma
import Theorems.Thm_AutoregLTF_claim_2
import Theorems.Thm_AutoregLTF_claim_3

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Lemma2
open AutoregLTF

theorem block_true_inPi (m : ℕ) (f : St) (r : ℕ) (h : block m f r = true) : InPi m r := by
  unfold block at h
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range'_1] at h
  unfold InPi
  rcases h with ((((h | ⟨j, hj, h, _⟩) | ⟨h, _⟩) | ⟨j, hj, h, _⟩) | ⟨j, hj, h, _⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, by simp [Finset.mem_Icc]; omega, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by simp [Finset.mem_Icc]; omega, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by simp [Finset.mem_Icc]; omega, h⟩)))

theorem E_false_of_not_inPi (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ) (h : ¬ InPi m r) :
    E m θ i t r = false := by
  by_contra hc
  exact h (block_true_inPi m _ r (by simpa [E] using hc))

theorem Ehat_nonneg (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ) :
    Ehat m θ i t (r : ℤ) = E m θ i (t + 1) r := by
  unfold Ehat
  have h1 : ¬ ((r : ℤ) < -(p m : ℤ)) := by omega
  have h2 : ¬ ((r : ℤ) < 0) := by omega
  simp [h1, h2]

/-- the window entry. -/
theorem window (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ)
    (IH : ∀ r' < r, gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
        (p m + 1 + r') = E m θ i (t + 1) r')
    (l : ℕ) (hl : l ≤ p m) :
    gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t) (p m + 1 + r - (l + 1))
      = Ehat m θ i t ((r : ℤ) - ((l + 1 : ℕ) : ℤ)) := by
  by_cases h : r ≤ l
  · have hk : p m + 1 + r - (l + 1) ≤ p m := by omega
    rw [gen16, if_pos hk]
    unfold hist Ehat
    by_cases h0 : p m + 1 + r - (l + 1) = 0
    · have : (r : ℤ) - ((l + 1 : ℕ) : ℤ) < -(p m : ℤ) := by omega
      rw [if_pos this]; simp [h0]
    · have h3 : ¬ ((r : ℤ) - ((l + 1 : ℕ) : ℤ) < -(p m : ℤ)) := by push_cast; omega
      have h4 : ((r : ℤ) - ((l + 1 : ℕ) : ℤ) < 0) := by push_cast; omega
      have h5 : ((r : ℤ) - ((l + 1 : ℕ) : ℤ) + p m).toNat = p m + 1 + r - (l + 1) - 1 := by
        push_cast; omega
      rw [if_neg h3, if_pos h4, h5]; simp [h0]
  · have : p m + 1 + r - (l + 1) = p m + 1 + (r - (l + 1)) := by omega
    rw [this, IH _ (by omega)]
    have : ((r : ℤ) - ((l + 1 : ℕ) : ℤ)) = ((r - (l + 1) : ℕ) : ℤ) := by push_cast; omega
    rw [this, Ehat_nonneg]

theorem sum_reindex (m : ℕ) (θ : ℕ → ℤ) (i t r : ℕ)
    (IH : ∀ r' < r, gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
        (p m + 1 + r') = E m θ i (t + 1) r') :
    (∑ ℓ : Fin (p m + 1), aCoef m θ ((ℓ.val + 1 : ℕ) : ℤ) *
      ((gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
        (p m + 1 + r - (ℓ.val + 1))).toNat : ℤ)) =
    ∑ ℓ ∈ Finset.Icc 1 (p m + 1), aCoef m θ ℓ * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ) := by
  have h1 : (∑ ℓ : Fin (p m + 1), aCoef m θ ((ℓ.val + 1 : ℕ) : ℤ) *
      ((gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
        (p m + 1 + r - (ℓ.val + 1))).toNat : ℤ)) =
      ∑ ℓ : Fin (p m + 1), aCoef m θ ((ℓ.val + 1 : ℕ) : ℤ) *
        ((Ehat m θ i t ((r : ℤ) - ((ℓ.val + 1 : ℕ) : ℤ))).toNat : ℤ) := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [window m θ i t r IH l.val (by omega)]
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun n => aCoef m θ ((n + 1 : ℕ) : ℤ) * ((Ehat m θ i t ((r : ℤ) - ((n + 1 : ℕ) : ℤ))).toNat : ℤ))]
  rw [Finset.range_eq_Ico]
  refine (Finset.sum_Ico_add' (fun ℓ : ℕ =>
    aCoef m θ (ℓ : ℤ) * ((Ehat m θ i t ((r : ℤ) - (ℓ : ℤ))).toNat : ℤ)) 0 (p m + 1) 1).trans ?_
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x; simp [Finset.mem_Ico, Finset.mem_Icc]

theorem main (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t : ℕ) :
    ∀ r, r < p m → gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
      (p m + 1 + r) = E m θ i (t + 1) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have IH : ∀ r' < r, gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
        (p m + 1 + r') = E m θ i (t + 1) r' := fun r' h => ih r' h (by omega)
    have hk : ¬ (p m + 1 + r ≤ p m) := by omega
    rw [gen16, if_neg hk]
    have hs := sum_reindex m θ i t r IH
    simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
    rw [show (∑ ℓ : Fin (p m + 1), aCoef m θ ((ℓ.val : ℤ) + 1) *
      ((gen16 (p m) (Bconst m) (fun n : ℕ => aCoef m θ n) (hist m θ i t)
        (p m + 1 + r - (ℓ.val + 1))).toNat : ℤ)) = _ from by
      simpa only [Nat.cast_add, Nat.cast_one] using hs]
    have hsig : (decide (0 ≤ -Bconst m + ∑ ℓ ∈ Finset.Icc 1 (p m + 1),
        aCoef m θ ℓ * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ))) =
        decide (0 ≤ sigma m θ i t r) := rfl
    show decide (0 ≤ -Bconst m + ∑ ℓ ∈ Finset.Icc 1 (p m + 1),
        aCoef m θ ℓ * ((Ehat m θ i t ((r : ℤ) - ℓ)).toNat : ℤ)) = _
    rw [hsig]
    by_cases hpi : InPi m r
    · rw [← Ehat_nonneg, claim_2 m hm θ hθ i hi t r hpi]
    · rw [E_false_of_not_inPi m θ i (t + 1) r hpi]
      have := claim_3 m hm θ hθ i hi t r hr hpi
      simpa using this

end AutoregLTF.Dev.Lemma2

namespace AutoregLTF
open AutoregLTF.Dev.Lemma2 in
theorem chk_lemma_2 (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ∃ B : ℤ, 0 < B ∧ ∃ a : ℕ → ℤ, ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m θ i t) (p m + 1 + r) = E m θ i (t + 1) r := by
  refine ⟨Bconst m, ?_, fun n : ℕ => aCoef m θ n, ?_⟩
  · unfold Bconst; positivity
  · intro i hi t r hr
    exact main m hm θ hθ i hi t r hr

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_lemma_2 := @AutoregLTF.chk_lemma_2
