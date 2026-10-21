-- Prove2me | solution 1 for AvramDividend.Classical.chat06_masked_iid_prefix_full_suffix_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:04:47.644749+00:00
-- url     : https://prove2.me/submissions/472fc4e5-3ca3-4b7a-9ece-95127ae1922d

import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace AvramChat06

/-- For an iid waiting-time driver, its entire finite past prefix
at a deterministic integer cut n is independent of its *whole*
future infinite sequence. The conclusion is an independence
statement between infinite-dimensional random variables, not
merely pairwise coordinate independence. -/
theorem iid_wait_prefix_independent_future
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) :
    IndepFun (fun ω (i : Fin n) => τ i ω)
      (fun ω (j : ℕ) => τ (n + j) ω) P := by
  have hL : ∀ i : Fin n, Measurable (τ i) := fun i => hmeas i
  have hR : ∀ j : ℕ, Measurable (τ (n + j)) :=
    fun j => hmeas (n + j)
  refine IndepFun.process_indepFun_process hL hR ?_
  intro I J
  let eL : Fin n ↪ ℕ :=
    ⟨fun i => (i : ℕ), Fin.val_injective⟩
  let eR : ℕ ↪ ℕ :=
    ⟨fun j => n + j, fun a b h => Nat.add_left_cancel h⟩
  have hdisj : Disjoint (I.map eL) (J.map eR) := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    obtain ⟨a, _, hza⟩ := Finset.mem_map.mp hzL
    obtain ⟨b, _, hzb⟩ := Finset.mem_map.mp hzR
    have haLt : (a : ℕ) < n := a.isLt
    have heq : (a : ℕ) = n + b := by
      exact hza.trans hzb.symm
    have hn : n ≤ (a : ℕ) := by
      rw [heq]
      exact Nat.le_add_right n b
    exact (Nat.not_le_of_gt haLt) hn
  have hindep := hiid.indepFun_finset
    (I.map eL) (J.map eR) hdisj hmeas
  have hφ : Measurable
      (fun (g : (I.map eL) → ℝ) (i : I) =>
        g ⟨(i : ℕ), Finset.mem_map_of_mem eL i.2⟩) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hψ : Measurable
      (fun (g : (J.map eR) → ℝ) (j : J) =>
        g ⟨n + (j : ℕ), Finset.mem_map_of_mem eR j.2⟩) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  exact hindep.comp hφ hψ

/-- The full-sequence-valued, zero-padded initial segment of
iid waits is independent of the entire infinite future suffix.
The codomain is now fixed as ℕ→ℝ for every stopping index n. -/
theorem iid_masked_prefix_indep_full_suffix
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) :
    IndepFun (fun ω (i : ℕ) =>
      if h : i < n then τ i ω else 0)
      (fun ω (j : ℕ) => τ (n + j) ω) P := by
  let φ : (Fin n → ℝ) → (ℕ → ℝ) :=
    fun g i => if h : i < n then g ⟨i, h⟩ else 0
  have hφ : Measurable φ := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i < n
    · simpa [φ, hi] using
        (measurable_pi_apply (⟨i, hi⟩ : Fin n))
    · simp [φ, hi]
  have hEq : (fun ω (i : ℕ) =>
      if h : i < n then τ i ω else 0) =
      fun ω => φ (fun i : Fin n => τ i ω) := by
    funext ω i
    by_cases hi : i < n <;> simp [φ, hi]
  rw [hEq]
  exact (iid_wait_prefix_independent_future τ hτ hiid n).comp
    hφ measurable_id

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) :
    IndepFun (fun ω (i : ℕ) =>
      if h : i < n then τ i ω else 0)
      (fun ω (j : ℕ) => τ (n + j) ω) P := by
  exact iid_masked_prefix_indep_full_suffix τ hτ hiid n
