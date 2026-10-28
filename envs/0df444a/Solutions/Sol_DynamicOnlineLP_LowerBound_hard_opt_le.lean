-- Prove2me | solution 1 for DynamicOnlineLP.LowerBound.hard_opt_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:01:19.297881+00:00
-- url     : https://prove2.me/submissions/ecebfb47-e026-4bc1-96a4-ac91b43dbe60

import Mathlib
import Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP
import Definitions.Def_DynamicOnlineLP_LowerBound_HardInstance

open DynamicOnlineLP.LowerBound in
theorem solution (z k s : ℕ) (hz : 1 ≤ z) (q : Fin z → ℕ) (hq : ∀ i, q i ≤ 2 * k) :
    OPT (hardProfit z k s q) (hardDemand z k s q) (hardCapacity z k)
      ≤ 7 * ((z : ℝ) * (k : ℝ)) := by
  have hzk : (0 : ℝ) ≤ (z : ℝ) * (k : ℝ) := by positivity
  let j0 : Fin (2 ^ z) := ⟨0, by positivity⟩
  have hd0 : ∀ c : HardCol z k s q, hardDemand z k s q c j0 = if c.2.isLeft then 0 else 1 := by
    rintro ⟨i, u⟩
    rcases u with u | u <;> simp [hardDemand, vVec, wVec, j0]
  have hpt : ∀ (x : HardCol z k s q → ℝ), (∀ c, 0 ≤ x c) → ∀ c,
      hardProfit z k s q c * x c ≤
        4 * (if c.2.isLeft then x c else 0) + 3 * (hardDemand z k s q c j0 * x c) := by
    intro x hx c
    rw [hd0]
    obtain ⟨i, u⟩ := c
    have := hx ⟨i, u⟩
    rcases u with u | u | u | u <;> simp [hardProfit] <;> linarith
  unfold OPT
  apply csSup_le
  · refine ⟨_, ⟨fun _ => 0, ⟨fun i => ?_, fun t => ⟨le_rfl, zero_le_one⟩⟩, rfl⟩⟩
    simp [hardCapacity, hzk]
  · rintro _ ⟨x, ⟨hcap, hbnd⟩, rfl⟩
    have hx0 : ∀ c, 0 ≤ x c := fun c => (hbnd c).1
    have h1 : ∑ c, hardDemand z k s q c j0 * x c ≤ (z : ℝ) * k := hcap j0
    have h2 : ∑ c : HardCol z k s q, (if c.2.isLeft then x c else 0) ≤ (z : ℝ) * k := by
      rw [Fintype.sum_sigma]
      have : ∀ i : Fin z, ∑ u : Fin k ⊕ Fin (q i) ⊕ Fin s ⊕ Fin (2 * k - q i),
          (if (⟨i, u⟩ : HardCol z k s q).2.isLeft then x ⟨i, u⟩ else 0) ≤ k := by
        intro i
        rw [Fintype.sum_sum_type]
        simp only [Sum.isLeft_inl, Sum.isLeft_inr, if_true, Bool.false_eq_true, if_false,
          Finset.sum_const_zero, add_zero]
        calc ∑ l : Fin k, x ⟨i, Sum.inl l⟩ ≤ ∑ _l : Fin k, (1 : ℝ) :=
              Finset.sum_le_sum (fun l _ => (hbnd _).2)
          _ = k := by simp
      calc ∑ i : Fin z, ∑ u : Fin k ⊕ Fin (q i) ⊕ Fin s ⊕ Fin (2 * k - q i),
            (if (⟨i, u⟩ : HardCol z k s q).2.isLeft then x ⟨i, u⟩ else 0)
          ≤ ∑ _i : Fin z, (k : ℝ) := Finset.sum_le_sum (fun i _ => this i)
        _ = (z : ℝ) * k := by simp
    unfold objective
    calc ∑ c, hardProfit z k s q c * x c
        ≤ ∑ c, (4 * (if c.2.isLeft then x c else 0) + 3 * (hardDemand z k s q c j0 * x c)) :=
          Finset.sum_le_sum (fun c _ => hpt x hx0 c)
      _ = 4 * ∑ c : HardCol z k s q, (if c.2.isLeft then x c else 0) +
            3 * ∑ c, hardDemand z k s q c j0 * x c := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 7 * ((z : ℝ) * k) := by linarith
