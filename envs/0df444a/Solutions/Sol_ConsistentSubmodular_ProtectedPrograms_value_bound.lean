-- Prove2me | solution 1 for ConsistentSubmodular.ProtectedPrograms.value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:07.528988+00:00
-- url     : https://prove2.me/submissions/b64c8255-e0ca-4cdf-878d-9c1672d93912

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule
import Theorems.Thm_ConsistentSubmodular_Objective_unstable_transition_buffer

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

theorem protected_buffer_subset {s t width : ℕ} (hst : s ≤ t)
    (hage : t - s ≤ width) :
    arrivedPrefix n t \ arrivedPrefix n s ⊆ rollingBuffer n width t := by
  intro e he
  simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he
  simp only [rollingBuffer, Finset.mem_sdiff, mem_arrivedPrefix]
  omega

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

theorem separated (i : ℕ) : C.start i + ell ≤ C.start (i + 1) :=
  (C.upper i).trans (by simpa [Nat.add_assoc] using C.lower (i + 1))

theorem start_mono : Monotone C.start := by
  apply monotone_nat_of_le_succ
  intro i
  exact (Nat.le_add_right _ _).trans (C.separated i)

theorem transition_age (i : ℕ) : C.start (i + 1) + ell - C.start i ≤ 2 * b := by
  have hu := C.upper (i + 1)
  have hl := C.lower i
  have hsum : C.start (i + 1) + ell ≤ C.start i + 2 * b := by nlinarith
  omega

theorem previous_buffer_protected {n : ℕ} (i t : ℕ)
    (ht0 : C.start (i + 1) ≤ t) (ht1 : t ≤ C.start (i + 1) + ell) :
    arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i) ⊆
      rollingBuffer n (4 * b) t := by
  have ha := C.transition_age i
  have hm := C.start_mono (show i ≤ i + 1 by omega)
  have hp := protected_buffer_subset (n := n) (s := C.start i) (t := t)
    (width := 4 * b) (by omega) (by omega)
  intro e he
  apply hp
  exact Finset.mem_sdiff.mpr ⟨arrivedPrefix_mono ht0 (Finset.mem_sdiff.mp he).1,
    (Finset.mem_sdiff.mp he).2⟩

theorem current_buffer_protected {n : ℕ} (i t : ℕ)
    (ht0 : C.start i ≤ t) (ht1 : t ≤ C.start (i + 1) + ell) :
    arrivedPrefix n t \ arrivedPrefix n (C.start i) ⊆ rollingBuffer n (4 * b) t := by
  have ha := C.transition_age i
  exact protected_buffer_subset ht0 (by omega)

theorem initial_buffer_full {n : ℕ} (t : ℕ) (ht : t ≤ C.start 0 + ell) :
    rollingBuffer n (4 * b) t = arrivedPrefix n t := by
  have hu := C.upper 0
  have hage : t - 4 * b = 0 := by simp only [zero_add] at hu; omega
  simp [rollingBuffer, hage, arrivedPrefix]

end ProtectedClock

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {n b ell R : ℕ} {F : ℕ → ℝ} {η : ℝ}

variable (C : ProtectedClock F η b ell)

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

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedPrograms

variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}

variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

theorem core_in_block (i t : ℕ) (ht : t / b = i + 1) :
    P.core t = (P.path i).node (R * (t - C.start i)) :=
  C.coreBlocks_in_block _ _ _ _ i t ht

end ProtectedPrograms

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedPrograms
variable {n b ell κ k R B : ℕ} {f : Objective n} {β η γ : ℝ}
variable {C : ProtectedClock (f.prefixOptimum k) η b ell}
variable (P : ProtectedPrograms f κ β C R B)

theorem solution (hb : 0 < b) (hη : 0 ≤ η) (hγ : γ ≤ (3 : ℝ) / 4)
    (compare : ∀ s t, f.prefixOptimum k t ≤ (1 + η) * f.prefixOptimum k s →
      γ * f.prefixOptimum k t ≤ β * f.prefixOptimum κ s) (t : ℕ) :
    γ * f.prefixOptimum k t ≤ f.value (P.selected t) := by
  have hself (s : ℕ) : γ * f.prefixOptimum k s ≤ β * f.prefixOptimum κ s := by
    apply compare s s
    have hh := mul_nonneg hη (f.prefixOptimum_nonnegative k s)
    nlinarith
  have hbuffer : rollingBuffer n (4 * b) t ⊆ P.selected t := Finset.subset_union_right
  have hfull (ht : t ≤ C.start 0 + ell) :
      γ * f.prefixOptimum k t ≤ f.value (P.selected t) := by
    have hp : f.prefixOptimum k t ≤ f.value (arrivedPrefix n t) := by
      have hh := f.monotone _ _ (f.bufferedOptimizer_spec (arrivedPrefix n t) ∅ k).1
      simpa [Objective.prefixOptimum, Objective.bufferedOptimum] using hh
    have hm := f.monotone _ _ (show arrivedPrefix n t ⊆ P.selected t by
      rw [← C.initial_buffer_full t ht]; exact hbuffer)
    have hc := mul_nonneg (show 0 ≤ 1 - γ by linarith) (f.prefixOptimum_nonnegative k t)
    nlinarith
  by_cases hinitial : t ≤ C.start 0 + ell
  · exact hfull hinitial
  have hr := Nat.mod_lt t hb
  have hd := Nat.mod_add_div t b
  cases hdiv : t / b with
  | zero =>
    rw [hdiv] at hd
    have hl := C.lower 0
    exact hfull (by simp only [zero_add, one_mul] at hl; omega)
  | succ i =>
    have hcore := P.core_in_block i t hdiv
    rw [hdiv] at hd
    have hlo : (i + 1) * b ≤ t := by simpa only [hdiv] using Nat.div_mul_le_self t b
    have hhi : t < (i + 2) * b := by
      simpa only [hdiv, Nat.add_assoc, Nat.mul_comm] using Nat.lt_mul_div_succ t hb
    by_cases hbefore : t < C.start i
    · have hz : R * (t - C.start i) = 0 := by simp [Nat.sub_eq_zero_of_le hbefore.le]
      rw [hz] at hcore
      cases i with
      | zero => omega
      | succ i =>
        rw [← P.joins i] at hcore
        have hu := C.upper i
        have hprev : C.start i ≤ t := by nlinarith
        have hval := P.checkpoint i t hprev hbefore.le
        have hsub := C.current_buffer_protected (n := n) i t hprev (by omega)
        have hm := f.monotone _ _ (show
            (P.path i).node (P.path i).length ∪
              (arrivedPrefix n t \ arrivedPrefix n (C.start i)) ⊆ P.selected t by
          rw [selected, hcore]
          exact Finset.union_subset_union (Finset.Subset.refl _) hsub)
        exact (hself t).trans (hval.trans hm)
    · have hstart : C.start i ≤ t := le_of_not_gt hbefore
      by_cases hfinish : C.start i + ell ≤ t
      · have hlen : (P.path i).length ≤ R * (t - C.start i) :=
          (P.length i).trans (Nat.mul_le_mul_left R (by omega))
        rw [(P.path i).stationary _ hlen] at hcore
        have hnext : t ≤ C.start (i + 1) := by
          have hh := C.lower (i + 1)
          nlinarith
        have hval := P.checkpoint i t hstart hnext
        have hsub := C.current_buffer_protected (n := n) i t hstart (by omega)
        have hm := f.monotone _ _ (show
            (P.path i).node (P.path i).length ∪
              (arrivedPrefix n t \ arrivedPrefix n (C.start i)) ⊆ P.selected t by
          rw [selected, hcore]
          exact Finset.union_subset_union (Finset.Subset.refl _) hsub)
        exact (hself t).trans (hval.trans hm)
      · have hend : t ≤ C.start i + ell := by omega
        rcases C.protection i with hstable | hunstable
        · have hct := compare (C.start i) t
            ((f.prefixOptimum_monotone k hend).trans hstable)
          cases i with
          | zero => omega
          | succ i =>
            have hval := P.transition i (R * (t - C.start (i + 1)))
            have hsub := C.previous_buffer_protected (n := n) i t hstart hend
            have hm := f.monotone _ _ (show
                (P.path (i + 1)).node (R * (t - C.start (i + 1))) ∪
                  (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)) ⊆
                  P.selected t by
              rw [selected, hcore]
              exact Finset.union_subset_union (Finset.Subset.refl _) hsub)
            exact hct.trans (hval.trans hm)
        · have hv := f.unstable_transition_buffer k C i t hstart hend hunstable
          have hm := f.monotone _ _ hbuffer
          have hc := mul_nonneg (sub_nonneg.mpr hγ) (f.prefixOptimum_nonnegative k t)
          nlinarith

end
