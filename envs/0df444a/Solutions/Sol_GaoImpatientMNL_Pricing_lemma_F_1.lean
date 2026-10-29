-- Prove2me | solution 1 for GaoImpatientMNL.Pricing.lemma_F_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:14:26.850004+00:00
-- url     : https://prove2.me/submissions/a305ae26-5d95-4c0b-a5d8-4a8666f2348d

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Relaxation

open GaoImpatientMNL.Pricing

lemma s225mb_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma s225mb_stage_le (A a b T W : ℝ) (hA : 0 ≤ A) (hT : 0 < T) (hW : 0 < W) :
    relaxedStage A a b ≤
      (((a - b) * Real.log (a * b) + (a - b) * Real.log (T / W) + A * W / T - (a - b) : ℝ) :
        EReal) := by
  unfold relaxedStage
  split_ifs with h1 h2
  · rw [h1]
    simp only [sub_self, zero_mul, zero_add, sub_zero]
    exact_mod_cast (by positivity : (0 : ℝ) ≤ A * W / T)
  · exact bot_le
  · push_neg at h2
    obtain ⟨hA0, hb0, hab⟩ := h2
    have ha0 : 0 < a := by linarith
    have hw : 0 < a - b := by linarith
    rw [EReal.coe_le_coe_iff]
    have e1 : Real.log (1 / b - 1 / a) = Real.log (a - b) - Real.log a - Real.log b := by
      rw [show 1 / b - 1 / a = (a - b) / (a * b) by field_simp,
        Real.log_div hw.ne' (by positivity), Real.log_mul ha0.ne' hb0.ne']
      ring
    have e2 : Real.log (a * b) = Real.log a + Real.log b := Real.log_mul ha0.ne' hb0.ne'
    have e3 : Real.log (T / W) = Real.log T - Real.log W := Real.log_div hT.ne' hW.ne'
    have e4 : Real.log (A * W / ((a - b) * T)) =
        Real.log A + Real.log W - Real.log (a - b) - Real.log T := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hA0.ne' hW.ne',
        Real.log_mul hw.ne' hT.ne']
      ring
    have key := Real.log_le_sub_one_of_pos (x := A * W / ((a - b) * T)) (by positivity)
    have key2 : (a - b) * Real.log (A * W / ((a - b) * T)) ≤ A * W / T - (a - b) := by
      have := mul_le_mul_of_nonneg_left key hw.le
      have e5 : (a - b) * (A * W / ((a - b) * T) - 1) = A * W / T - (a - b) := by
        field_simp
      linarith
    rw [e4] at key2
    rw [e1, e2, e3]
    nlinarith [key2]

theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (hS : Feasible S)
    (q : ℕ → ℝ) (hq : QFeasible m q) :
    infinitePatienceRevenue α S q ≤ relaxation (totalAttraction α) m q := by
  have hmono : ∀ j k, k + j ≤ m → q (k + j) ≤ q k := by
    intro j
    induction j with
    | zero => intro k _; simp
    | succ j ih =>
      intro k hk
      have h1 := (hq.2 (k + j) (by omega)).2
      have h2 := ih k (by omega)
      rw [← add_assoc]; linarith
  have hqm0 : 0 ≤ q m := by
    have := (hq.2 (m - 1) (by omega)).1
    rwa [Nat.sub_add_cancel hm] at this
  have hle1 : ∀ k ≤ m, q k ≤ 1 := by
    intro k hk
    have := hmono k 0 (by omega)
    rw [zero_add, hq.1] at this; exact this
  have hgem : ∀ k ≤ m, q m ≤ q k := by
    intro k hk
    have := hmono (m - k) k (by omega)
    rwa [Nat.add_sub_cancel' hk] at this
  have hA : ∀ k, 0 ≤ stageAttraction α S k := fun k =>
    Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  unfold relaxation
  split_ifs with h0
  · -- q m = 0 : some stage is ⊥
    rw [le_bot_iff]
    have hex : ∃ j, q j = 0 := ⟨m, h0⟩
    classical
    set j := Nat.find hex with hjdef
    have hj : q j = 0 := Nat.find_spec hex
    have hjm : j ≤ m := Nat.find_min' hex h0
    have hj0 : j ≠ 0 := by
      intro h; rw [h, hq.1] at hj; exact one_ne_zero hj
    have hprev : q (j - 1) ≠ 0 := Nat.find_min hex (by omega)
    have hk : j - 1 < m := by omega
    have hterm : relaxedStage (stageAttraction α S ⟨j - 1, hk⟩) (q (j - 1)) (q (j - 1 + 1)) = ⊥ := by
      rw [Nat.sub_add_cancel (by omega), hj]
      unfold relaxedStage
      rw [if_neg hprev, if_pos (Or.inr (Or.inl le_rfl))]
    unfold infinitePatienceRevenue
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨j - 1, hk⟩ : Fin m))]
    simp only
    rw [hterm, EReal.bot_add]
  · rcases eq_or_ne (q m) 1 with h1 | h1
    · have hall : ∀ k ≤ m, q k = 1 := fun k hk =>
        le_antisymm (hle1 k hk) (h1 ▸ hgem k hk)
      have hL : infinitePatienceRevenue α S q = 0 := by
        unfold infinitePatienceRevenue
        refine Finset.sum_eq_zero fun k _ => ?_
        unfold relaxedStage
        rw [if_pos (by rw [hall k.val k.isLt.le, hall (k.val + 1) k.isLt])]
      have hR : relaxationReal (totalAttraction α) m q = 0 := by
        unfold relaxationReal
        rw [if_pos h1, add_zero]
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_range] at hk
        rw [hall k hk.le, hall (k + 1) hk, sub_self, zero_mul]
      rw [hL, hR]; rfl
    · set T := totalAttraction α with hTdef
      set W := 1 - q m with hWdef
      have hW : 0 < W := by
        have := hle1 m le_rfl
        have : q m < 1 := lt_of_le_of_ne this h1
        rw [hWdef]; linarith
      have hT : 0 < T := by
        rw [hTdef]; unfold totalAttraction
        exact Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      have hsumA : ∑ k : Fin m, stageAttraction α S k ≤ T := by
        unfold stageAttraction
        rw [hTdef]; unfold totalAttraction
        rw [← Finset.sum_biUnion (fun k _ h _ hkh => hS k h hkh)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => (Real.exp_pos _).le)
      have hs1 : ∑ k : Fin m, (q k.val - q (k.val + 1)) * Real.log (q k.val * q (k.val + 1)) =
          ∑ k ∈ Finset.range m, (q k - q (k + 1)) * Real.log (q k * q (k + 1)) :=
        Fin.sum_univ_eq_sum_range (fun k => (q k - q (k + 1)) * Real.log (q k * q (k + 1))) m
      have hs2 : ∑ k : Fin m, (q k.val - q (k.val + 1)) = W := by
        rw [Fin.sum_univ_eq_sum_range (fun k => q k - q (k + 1)) m, Finset.sum_range_sub',
          hq.1]
      unfold infinitePatienceRevenue
      calc ∑ k : Fin m, relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))
          ≤ ∑ k : Fin m, (((q k.val - q (k.val + 1)) * Real.log (q k.val * q (k.val + 1)) +
              (q k.val - q (k.val + 1)) * Real.log (T / W) +
              stageAttraction α S k * W / T - (q k.val - q (k.val + 1)) : ℝ) : EReal) :=
            Finset.sum_le_sum fun k _ => s225mb_stage_le _ _ _ T W (hA k) hT hW
        _ = ((∑ k : Fin m, ((q k.val - q (k.val + 1)) * Real.log (q k.val * q (k.val + 1)) +
              (q k.val - q (k.val + 1)) * Real.log (T / W) +
              stageAttraction α S k * W / T - (q k.val - q (k.val + 1))) : ℝ) : EReal) :=
            (s225mb_coe_sum _ _).symm
        _ ≤ (relaxationReal T m q : EReal) := by
          rw [EReal.coe_le_coe_iff]
          unfold relaxationReal
          rw [if_neg h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_mul, hs1, hs2]
          have : (∑ k : Fin m, stageAttraction α S k) * W / T ≤ W := by
            rw [div_le_iff₀ hT]; nlinarith
          rw [← hWdef]
          linarith
