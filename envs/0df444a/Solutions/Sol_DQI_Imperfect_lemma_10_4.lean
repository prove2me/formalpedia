-- Prove2me | solution 1 for DQI.Imperfect.lemma_10_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:53:22.70597+00:00
-- url     : https://prove2.me/submissions/e9b7aa2b-9475-4980-8ad6-258616852961

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

set_option autoImplicit false
open Finset DQI.Imperfect

lemma mm_shell_card (m k : ℕ) : (shell m k).card = Nat.choose m k := by
  classical
  have : (shell m k).card = (Finset.powersetCard k (Finset.univ : Finset (Fin m))).card := by
    refine Finset.card_nbij' (fun y => Finset.univ.filter (fun i => y i ≠ 0))
      (fun S => fun i => if i ∈ S then 1 else 0) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_coe] at hy
      rw [Finset.mem_coe]
      have hy' : wt y = k := by
        simpa [shell] using hy
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact hy'
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hS
      rw [Finset.mem_coe]
      have : (Finset.univ.filter (fun i : Fin m => (if i ∈ S then (1 : ZMod 2) else 0) ≠ 0)) = S := by
        ext i; simp
      show _ ∈ shell m k
      unfold shell
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show wt _ = k
      unfold wt
      rw [this]; exact hS.2
    · intro y hy
      funext i
      by_cases h : y i = 0
      · simp [h]
      · have : y i = 1 := by
          revert h; generalize y i = a; revert a; decide
        simp [h, this]
    · intro S hS
      ext i; simp
  rw [this, Finset.card_powersetCard]; simp

lemma mm_sq_sum {ι κ : Type*} [Fintype κ] [DecidableEq κ] (T : Finset ι) (f : ι → κ) (a : ι → ℝ)
    (hf : Set.InjOn f T) :
    ∑ s : κ, (∑ i ∈ T, if f i = s then a i else 0) ^ 2 = ∑ i ∈ T, a i ^ 2 := by
  classical
  have h1 : ∀ s : κ, (∑ i ∈ T, if f i = s then a i else 0) ^ 2
      = ∑ i ∈ T, ∑ j ∈ T, (if f i = s then a i else 0) * (if f j = s then a j else 0) := by
    intro s; rw [sq, Finset.sum_mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · simp [sq]
  · intro j hj hji
    refine Finset.sum_eq_zero (fun s _ => ?_)
    by_cases h : f j = s
    · by_cases h' : f i = s
      · exact absurd (hf hj hi (h.trans h'.symm)) hji
      · simp [h']
    · simp [h]
  · intro h; exact absurd hi h

lemma mm_sgn_sq (a : ZMod 2) : sgn a ^ 2 = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem solution (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ) :
    (∑ s, (PtD B v dec ℓ w s) ^ 2) =
        (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ∧
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ≤ w ⬝ᵥ w := by
  classical
  have hcard : ∀ k : Fin (ℓ + 1), ((Dset B dec k.val).card : ℝ) + (Fset B dec k.val).card = (Nat.choose m k.val : ℝ) := by
    intro k
    have : (Dset B dec k.val).card + (Fset B dec k.val).card = Nat.choose m k.val := by
      rw [← mm_shell_card]
      exact Finset.card_filter_add_card_filter_not _
    exact_mod_cast this
  have hpos : ∀ k : Fin (ℓ + 1), (0 : ℝ) < (Nat.choose m k.val : ℝ) := by
    intro k
    exact_mod_cast Nat.choose_pos (by omega)
  have key : ∀ k : Fin (ℓ + 1), (w k) ^ 2 * (1 - epsk B dec k.val)
      = ∑ y ∈ Dset B dec k.val, (w k / Real.sqrt (Nat.choose m k.val : ℝ) * sgn (v ⬝ᵥ y)) ^ 2 := by
    intro k
    have hC := hpos k
    have h2 := hcard k
    simp_rw [mul_pow, mul_comm _ (sgn _ ^ 2), mm_sgn_sq, one_mul]
    rw [Finset.sum_const, nsmul_eq_mul, div_pow, Real.sq_sqrt hC.le]
    unfold epsk
    have hD : ((Dset B dec k.val).card : ℝ) = (Nat.choose m k.val : ℝ) - (Fset B dec k.val).card := by linarith
    rw [hD]
    field_simp
  set T : Finset (Fin (ℓ + 1) × (Fin m → ZMod 2)) :=
    Finset.univ.filter (fun p => p.2 ∈ Dset B dec p.1.val) with hT
  have hPt : ∀ s, PtD B v dec ℓ w s = ∑ p ∈ T, if B.transpose.mulVec p.2 = s
      then w p.1 / Real.sqrt (Nat.choose m p.1.val : ℝ) * sgn (v ⬝ᵥ p.2) else 0 := by
    intro s
    unfold PtD
    rw [hT, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp only
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs <;> simp
  have hinj : Set.InjOn (fun p : Fin (ℓ + 1) × (Fin m → ZMod 2) => B.transpose.mulVec p.2) T := by
    intro p hp q hq hpq
    simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hq
    have h1 : dec (B.transpose.mulVec p.2) = p.2 := (Finset.mem_filter.1 hp).2
    have h2 : dec (B.transpose.mulVec q.2) = q.2 := (Finset.mem_filter.1 hq).2
    have h3 : p.2 = q.2 := by rw [← h1, ← h2]; exact congrArg dec hpq
    have h4 : wt p.2 = p.1.val := by simpa [shell] using (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
    have h5 : wt q.2 = q.1.val := by simpa [shell] using (Finset.mem_filter.1 (Finset.mem_filter.1 hq).1).2
    refine Prod.ext (Fin.ext ?_) h3
    rw [← h4, ← h5, h3]
  have hsum : (∑ s, (PtD B v dec ℓ w s) ^ 2) =
      ∑ k, (w k) ^ 2 * (1 - epsk B dec k.val) := by
    simp_rw [hPt]
    rw [mm_sq_sum T _ _ hinj]
    simp_rw [key]
    rw [hT, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp only
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
  refine ⟨hsum, ?_⟩
  rw [dotProduct]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have : 0 ≤ epsk B dec k.val := by
    unfold epsk; positivity
  nlinarith [sq_nonneg (w k)]
