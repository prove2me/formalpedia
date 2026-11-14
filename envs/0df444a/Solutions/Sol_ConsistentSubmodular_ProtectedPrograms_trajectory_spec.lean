-- Prove2me | solution 1 for ConsistentSubmodular.ProtectedPrograms.trajectory_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:58.258891+00:00
-- url     : https://prove2.me/submissions/4080be11-21d7-4d89-a05b-73d7228d0868

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_StreamingParameters
import Theorems.Thm_ConsistentSubmodular_prefix_difference_card_le
import Theorems.Thm_ConsistentSubmodular_Objective_optimum_thinning
import Theorems.Thm_ConsistentSubmodular_ProtectedPrograms_arrived_bound
import Theorems.Thm_ConsistentSubmodular_ProtectedPrograms_value_bound

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

theorem rollingBuffer_card_le (width t : ℕ) :
    (rollingBuffer n width t).card ≤ width := by
  exact (prefix_difference_card_le (t - width) t).trans (by omega)

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace BlockSchedule

variable {n b R : ℕ} (S : BlockSchedule n b R)

theorem trajectory_recourse (hb : 0 < b) (t : ℕ) :
    recourse (S.trajectory (t + 1)) (S.trajectory t) ≤ R := by
  have hr := Nat.mod_lt t hb
  have hd0 := Nat.mod_add_div t b
  have hd1 := Nat.mod_add_div (t + 1) b
  by_cases hm : (t + 1) % b = 0
  · have hq := Nat.succ_div_of_mod_eq_zero hm
    have hlast : t % b + 1 = b := by rw [hm, hq] at hd1; nlinarith
    unfold trajectory
    rw [hm, hq, ← S.joins (t / b)]
    simpa only [hlast] using S.step (t / b) (t % b) hr
  · have hq := Nat.succ_div_of_mod_ne_zero hm
    have hnext : (t + 1) % b = t % b + 1 := by rw [hq] at hd1; omega
    unfold trajectory
    rw [hq, hnext]
    exact S.step _ _ hr

end BlockSchedule

namespace ProtectedClock

variable {n b ell R : ℕ} {F : ℕ → ℝ} {η : ℝ}

variable (C : ProtectedClock F η b ell)

theorem coreBlocks_recourse (hb : 0 < b) (P : ℕ → SetOperationPath n)
    (hinitial hjoin hlen) (t : ℕ) :
    recourse ((C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory (t + 1))
      ((C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t) ≤ R :=
  BlockSchedule.trajectory_recourse _ hb t

theorem coreBlocks_before_first (P : ℕ → SetOperationPath n) (hinitial hjoin hlen)
    (t : ℕ) (ht : t / b = 0) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t = ∅ := by
  simp [BlockSchedule.trajectory, coreBlocks, ht]

theorem coreBlocks_in_block (P : ℕ → SetOperationPath n) (hinitial hjoin hlen)
    (i t : ℕ) (ht : t / b = i + 1) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t =
      (P i).node (R * (t - C.start i)) := by
  have htval := Nat.mod_add_div t b
  rw [ht] at htval
  have hl := C.lower i
  have heq : t % b - C.delay i = t - C.start i := by
    dsimp [delay]
    have hh : t % b + (i + 1) * b = t := by nlinarith
    omega
  simp [BlockSchedule.trajectory, coreBlocks, ht, heq]

end ProtectedClock

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_sdiff_le (A B R T : Finset (Fin n)) :
    recourse (A \ R) (B \ T) ≤ recourse A B + recourse R T := by
  have hsub : ((A \ R) \ (B \ T)) ∪ ((B \ T) \ (A \ R)) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((R \ T) ∪ (T \ R)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem prefix_recourse_le {s t : ℕ} (hst : s ≤ t) :
    recourse (arrivedPrefix n t) (arrivedPrefix n s) ≤ t - s := by
  have hsub : arrivedPrefix n s ⊆ arrivedPrefix n t := arrivedPrefix_mono hst
  have he : arrivedPrefix n s \ arrivedPrefix n t = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr hsub
  simpa [recourse, he] using (prefix_difference_card_le (n := n) s t)

theorem rollingBuffer_recourse_le (width t : ℕ) :
    recourse (rollingBuffer n width (t + 1)) (rollingBuffer n width t) ≤ 2 := by
  have hnew := prefix_recourse_le (n := n) (show t ≤ t + 1 by omega)
  have hold := prefix_recourse_le (n := n) (show t - width ≤ t + 1 - width by omega)
  have hh := recourse_sdiff_le (arrivedPrefix n (t + 1)) (arrivedPrefix n t)
    (arrivedPrefix n (t + 1 - width)) (arrivedPrefix n (t - width))
  change recourse (rollingBuffer n width (t + 1)) (rollingBuffer n width t) ≤ _ at hh
  omega

end ConsistentSubmodular

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedPrograms

variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}

variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

theorem recourse_bound (hb : 0 < b) (t : ℕ) :
    recourse (P.selected (t + 1)) (P.selected t) ≤ R + 2 := by
  have hc := C.coreBlocks_recourse (R := R) hb P.path P.initial P.joins P.length t
  have hbuf := rollingBuffer_recourse_le (n := n) (4 * b) t
  have hh := recourse_union_le (P.core (t + 1)) (P.core t)
    (rollingBuffer n (4 * b) (t + 1)) (rollingBuffer n (4 * b) t)
  exact hh.trans (Nat.add_le_add hc hbuf)

theorem core_in_block (i t : ℕ) (ht : t / b = i + 1) :
    P.core t = (P.path i).node (R * (t - C.start i)) :=
  C.coreBlocks_in_block _ _ _ _ i t ht

theorem core_cardinality (t : ℕ) : (P.core t).card ≤ B := by
  cases h : t / b with
  | zero => rw [core, C.coreBlocks_before_first _ _ _ _ t h]; simp
  | succ i => rw [P.core_in_block i t h]; exact P.cardinality _ _

theorem cardinality_bound (t : ℕ) : (P.selected t).card ≤ B + 4 * b :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add (P.core_cardinality t)
    (rollingBuffer_card_le _ _))

end ProtectedPrograms

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

theorem stable_slack_comparison (α η : ℝ) (hα : α ≤ 1) (hη : 0 ≤ η) :
    (α - 14 * η) * (1 + η) ≤ (α - 2 * η) * (1 - 10 * η) := by
  nlinarith [sq_nonneg η, mul_nonneg hη (sub_nonneg.mpr hα)]

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace Objective

variable {n : ℕ} (f : Objective n)

theorem prefix_thinning_ratio {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k)
    (δ : ℝ) (hδ : δ * k ≤ r) (t : ℕ) :
    δ * f.prefixOptimum k t ≤ f.prefixOptimum r t := by
  have hh := f.optimum_thinning (arrivedPrefix n t) hrk
  have hs := mul_le_mul_of_nonneg_right hδ (f.prefixOptimum_nonnegative k t)
  change (r : ℝ) * f.prefixOptimum k t ≤ (k : ℝ) * f.prefixOptimum r t at hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  apply (mul_le_mul_iff_right₀ hk0).mp
  nlinarith only [hh, hs]

theorem transfer_comparison {N H k : ℕ} (p : TransferParameters N H k) {α : ℝ}
    (hα : α ≤ 1) (hγ : 0 ≤ α - 14 * ((1 : ℝ) / N)) (hk : 0 < k) (s t : ℕ)
    (hstable : f.prefixOptimum k t ≤ (1 + (1 : ℝ) / N) * f.prefixOptimum k s) :
    (α - 14 * ((1 : ℝ) / N)) * f.prefixOptimum k t ≤
      (α - 2 * ((1 : ℝ) / N)) * f.prefixOptimum p.core s := by
  have hη0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hβ : 0 ≤ α - 2 * ((1 : ℝ) / N) := by linarith
  have hthin := f.prefix_thinning_ratio hk p.core_le _ p.thinning s
  have hslack := stable_slack_comparison α ((1 : ℝ) / N) hα hη0
  have h1 := mul_le_mul_of_nonneg_left hstable hγ
  have h2 := mul_le_mul_of_nonneg_right hslack (f.prefixOptimum_nonnegative k s)
  have h3 := mul_le_mul_of_nonneg_left hthin hβ
  nlinarith only [h1, h2, h3]

end Objective

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedPrograms
variable {n N H k R : ℕ} {f : Objective n} {α : ℝ}
variable (p : TransferParameters N H k)
variable {C : ProtectedClock (f.prefixOptimum k) ((1 : ℝ) / N) p.block p.interval}
variable (P : ProtectedPrograms f p.core (α - 2 * ((1 : ℝ) / N)) C R
  (p.core + p.block + H))

theorem solution (hk : 0 < k) (hα : α ≤ 3 / 4)
    (hγ : 0 ≤ α - 14 * ((1 : ℝ) / N)) :
    FeasibleTrajectory k (R + 2) (fun t : Fin (n + 1) => P.selected t.val) ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k →
        (α - 14 * ((1 : ℝ) / N)) * f.value A ≤ f.value (P.selected t.val) := by
  have hη0 : 0 ≤ (1 : ℝ) / N := by positivity
  refine ⟨?_, ?_⟩
  · refine ⟨P.selected_zero, ?_, ?_⟩
    · intro t
      exact ⟨P.arrived_bound _, (P.cardinality_bound _).trans (by have := p.capacity; omega)⟩
    · intro t
      exact P.recourse_bound p.block_pos t.val
  · intro t A hA hAk
    have hopt : f.value A ≤ f.prefixOptimum k t.val := by
      simpa [Objective.prefixOptimum] using f.le_bufferedOptimum (Q := ∅) hA hAk
    have hv := P.value_bound p.block_pos hη0 (by linarith)
      (fun s t hs => f.transfer_comparison p (by linarith) hγ hk s t hs) t.val
    exact (mul_le_mul_of_nonneg_left hopt hγ).trans hv

end
