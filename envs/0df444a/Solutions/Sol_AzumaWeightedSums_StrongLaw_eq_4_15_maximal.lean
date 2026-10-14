-- Prove2me | solution 1 for AzumaWeightedSums.StrongLaw.eq_4_15_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:21:19.422414+00:00
-- url     : https://prove2.me/submissions/d028360d-db79-46ba-a8d6-5f728291c114

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

set_option autoImplicit false

namespace K2b1982cee

open MeasureTheory AzumaWeightedSums.StrongLaw

/-- Orthogonality: a bounded `ℱ (l-1)`-measurable `g` is orthogonal to the martingale difference `x l`. -/
theorem orth {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (l : ℕ) (hl : 1 ≤ l)
    (g : Ω → ℝ) (hg : StronglyMeasurable[ℱ (l - 1)] g) (C : ℝ) (hgb : ∀ᵐ ω ∂μ, |g ω| ≤ C) :
    Integrable (fun ω => g ω * x l ω) μ ∧ ∫ ω, g ω * x l ω ∂μ = 0 := by
  obtain ⟨-, hxi, hce⟩ := hx l hl
  have hgm : AEStronglyMeasurable g μ := (hg.mono (ℱ.le (l - 1))).aestronglyMeasurable
  have hint : Integrable (fun ω => g ω * x l ω) μ :=
    hxi.bdd_mul hgm (c := C) (by filter_upwards [hgb] with ω h; simpa [Real.norm_eq_abs] using h)
  refine ⟨hint, ?_⟩
  rw [← integral_condExp (ℱ.le (l - 1))]
  have h1 : μ[(fun ω => g ω * x l ω) | ℱ (l - 1)] =ᵐ[μ] fun ω => g ω * μ[x l | ℱ (l - 1)] ω :=
    condExp_mul_of_stronglyMeasurable_left hg hint hxi
  rw [integral_congr_ae h1]
  have h2 : (fun ω => g ω * μ[x l | ℱ (l - 1)] ω) =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [hce] with ω h
    simp [h]
  rw [integral_congr_ae h2]
  simp

theorem hall {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} (x : ℕ → Ω → ℝ)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ j : ℕ, 1 ≤ j → |x j ω| ≤ 1 := by
  rw [ae_all_iff]
  intro j
  by_cases hj : 1 ≤ j
  · filter_upwards [hbd j hj] with ω h _ using h
  · exact Filter.Eventually.of_forall (fun ω h => absurd h hj)

/-- One step of the second-moment recursion. -/
theorem step {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (N : ℕ) (B : Set Ω) (hB : MeasurableSet[ℱ N] B) (t c C : ℝ) (Y : Ω → ℝ)
    (hYm : StronglyMeasurable[ℱ N] Y) (hYb : ∀ᵐ ω ∂μ, |Y ω| ≤ C) :
    Integrable (B.indicator (fun ω => (t - Y ω) ^ 2)) μ ∧
    Integrable (B.indicator (fun ω => (t - (Y ω + c * x (N + 1) ω)) ^ 2)) μ ∧
    ∫ ω, B.indicator (fun ω => (t - (Y ω + c * x (N + 1) ω)) ^ 2) ω ∂μ
      ≤ ∫ ω, B.indicator (fun ω => (t - Y ω) ^ 2) ω ∂μ + c ^ 2 * μ.real B := by
  have hBm : MeasurableSet B := ℱ.le N B hB
  have hYm0 : StronglyMeasurable Y := hYm.mono (ℱ.le N)
  have hx1 : StronglyMeasurable (x (N + 1)) := ((hx (N + 1) (by omega)).1).mono (ℱ.le (N + 1))
  have hxb := hbd (N + 1) (by omega)
  have i1 : Integrable (B.indicator (fun ω => (t - Y ω) ^ 2)) μ := by
    refine Integrable.of_bound
      (((stronglyMeasurable_const.sub hYm0).pow 2).indicator hBm).aestronglyMeasurable
      ((|t| + C) ^ 2) ?_
    filter_upwards [hYb] with ω hω
    rw [Real.norm_eq_abs]
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB, abs_pow]
      have : |t - Y ω| ≤ |t| + C := (abs_sub _ _).trans (by linarith)
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    · rw [Set.indicator_of_notMem hωB, abs_zero]
      positivity
  set g : Ω → ℝ := B.indicator (fun ω => -2 * c * (t - Y ω)) with hgdef
  have hgm : StronglyMeasurable[ℱ (N + 1 - 1)] g := by
    rw [Nat.add_sub_cancel]
    exact ((stronglyMeasurable_const.sub hYm).const_mul (-2 * c)).indicator hB
  have hgb : ∀ᵐ ω ∂μ, |g ω| ≤ 2 * |c| * (|t| + C) := by
    filter_upwards [hYb] with ω hω
    have hC : 0 ≤ C := (abs_nonneg _).trans hω
    by_cases hωB : ω ∈ B
    · rw [hgdef, Set.indicator_of_mem hωB, abs_mul, abs_mul]
      have h2 : |(-2 : ℝ)| = 2 := by norm_num
      rw [h2]
      have : |t - Y ω| ≤ |t| + C := (abs_sub _ _).trans (by linarith)
      have hc : 0 ≤ 2 * |c| := by positivity
      calc 2 * |c| * |t - Y ω| ≤ 2 * |c| * (|t| + C) := mul_le_mul_of_nonneg_left this hc
        _ = 2 * |c| * (|t| + C) := rfl
    · rw [hgdef, Set.indicator_of_notMem hωB, abs_zero]
      positivity
  obtain ⟨hgi, hg0⟩ := orth ℱ x hx (N + 1) (by omega) g hgm _ hgb
  set h3 : Ω → ℝ := B.indicator (fun ω => c ^ 2 * x (N + 1) ω ^ 2) with hh3
  have h3b : ∀ᵐ ω ∂μ, h3 ω ≤ B.indicator (fun _ => c ^ 2) ω ∧ 0 ≤ h3 ω := by
    filter_upwards [hxb] with ω hω
    have hx2 : x (N + 1) ω ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (x (N + 1) ω)]
    by_cases hωB : ω ∈ B
    · rw [hh3, Set.indicator_of_mem hωB, Set.indicator_of_mem hωB]
      constructor
      · nlinarith [sq_nonneg c]
      · positivity
    · rw [hh3, Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB]
      exact ⟨le_rfl, le_rfl⟩
  have h3i : Integrable h3 μ := by
    refine Integrable.of_bound
      ((stronglyMeasurable_const.mul (hx1.pow 2)).indicator hBm).aestronglyMeasurable (c ^ 2) ?_
    filter_upwards [h3b] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.2]
    refine hω.1.trans ?_
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB]
    · rw [Set.indicator_of_notMem hωB]; positivity
  have hsplit : B.indicator (fun ω => (t - (Y ω + c * x (N + 1) ω)) ^ 2)
      = fun ω => B.indicator (fun ω => (t - Y ω) ^ 2) ω + g ω * x (N + 1) ω + h3 ω := by
    funext ω
    by_cases hωB : ω ∈ B
    · rw [hgdef, hh3, Set.indicator_of_mem hωB, Set.indicator_of_mem hωB,
        Set.indicator_of_mem hωB, Set.indicator_of_mem hωB]
      ring
    · rw [hgdef, hh3, Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB,
        Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB]
      ring
  refine ⟨i1, ?_, ?_⟩
  · rw [hsplit]; exact (i1.add hgi).add h3i
  · rw [hsplit]
    have e1 := integral_add (i1.add hgi) h3i
    have e2 := integral_add i1 hgi
    simp only [Pi.add_apply] at e1 e2
    show ∫ ω, (B.indicator (fun ω => (t - Y ω) ^ 2) ω + g ω * x (N + 1) ω + h3 ω) ∂μ ≤ _
    rw [e1, e2, hg0]
    have h3le : ∫ ω, h3 ω ∂μ ≤ c ^ 2 * μ.real B := by
      have e : ∫ ω, B.indicator (fun _ => c ^ 2) ω ∂μ = μ.real B • c ^ 2 :=
        integral_indicator_const _ hBm
      rw [smul_eq_mul] at e
      rw [mul_comm, ← e]
      exact integral_mono_ae h3i ((integrable_const _).indicator hBm) (h3b.mono fun ω h => h.1)
    linarith

/-- Second moment of `t - Y` on an `ℱ n`-event. -/
theorem moment {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (n : ℕ) (c : ℕ → ℝ) (B : Set Ω) (hB : MeasurableSet[ℱ n] B) (t : ℝ) (N : ℕ) :
    Integrable (B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2)) μ ∧
    ∫ ω, B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2) ω ∂μ
      ≤ (t ^ 2 + ∑ j ∈ Finset.Ioc n N, c j ^ 2) * μ.real B := by
  have hBm : MeasurableSet B := ℱ.le n B hB
  have hall' := hall x hbd
  have hempty : ∀ N : ℕ, N ≤ n →
      (Integrable (B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2)) μ ∧
      ∫ ω, B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2) ω ∂μ
        ≤ (t ^ 2 + ∑ j ∈ Finset.Ioc n N, c j ^ 2) * μ.real B) := by
    intro N hN
    have he : Finset.Ioc n N = ∅ := Finset.Ioc_eq_empty (by omega)
    simp only [he, Finset.sum_empty, sub_zero, add_zero]
    refine ⟨(integrable_const _).indicator hBm, ?_⟩
    rw [integral_indicator_const _ hBm, smul_eq_mul, mul_comm]
  induction N with
  | zero => exact hempty 0 (Nat.zero_le _)
  | succ N ih =>
    by_cases hnN : n ≤ N
    swap
    · exact hempty (N + 1) (by omega)
    have hYm : StronglyMeasurable[ℱ N] (fun ω => ∑ j ∈ Finset.Ioc n N, c j * x j ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      simp only [Finset.mem_Ioc] at hj
      exact (((hx j (by omega)).1).mono (ℱ.mono hj.2)).const_mul (c j)
    have hYb : ∀ᵐ ω ∂μ, |∑ j ∈ Finset.Ioc n N, c j * x j ω| ≤ ∑ j ∈ Finset.Ioc n N, |c j| := by
      filter_upwards [hall'] with ω hω
      calc |∑ j ∈ Finset.Ioc n N, c j * x j ω| ≤ ∑ j ∈ Finset.Ioc n N, |c j * x j ω| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.Ioc n N, |c j| := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_Ioc] at hj
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hω j (by omega))
    obtain ⟨-, i2, hle⟩ := step ℱ x hx hbd N B (ℱ.mono hnN B hB) t (c (N + 1)) _
      (fun ω => ∑ j ∈ Finset.Ioc n N, c j * x j ω) hYm hYb
    simp only [Finset.sum_Ioc_succ_top hnN]
    refine ⟨i2, ?_⟩
    have := ih.2
    nlinarith

/-- Cantelli on an `ℱ n`-event. -/
theorem cantelli {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (n N : ℕ) (c : ℕ → ℝ) (B D : Set Ω) (hB : MeasurableSet[ℱ n] B) (hD : MeasurableSet D)
    (hDB : D ⊆ B) (t : ℝ) (ht : 0 < t)
    (hσ : ∑ j ∈ Finset.Ioc n N, c j ^ 2 < t ^ 2)
    (hY : ∀ᵐ ω ∂μ, ω ∈ D → ∑ j ∈ Finset.Ioc n N, c j * x j ω ≤ -t) :
    μ.real D ≤ μ.real B / 2 := by
  obtain ⟨hi, hm⟩ := moment ℱ x hx hbd n c B hB t N
  have h1 : ∫ ω, D.indicator (fun _ => 4 * t ^ 2) ω ∂μ
      ≤ ∫ ω, B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2) ω ∂μ := by
    apply integral_mono_ae ((integrable_const _).indicator hD) hi
    filter_upwards [hY] with ω hω
    by_cases hωD : ω ∈ D
    · rw [Set.indicator_of_mem hωD, Set.indicator_of_mem (hDB hωD)]
      have hy := hω hωD
      nlinarith
    · rw [Set.indicator_of_notMem hωD]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  rw [integral_indicator_const _ hD, smul_eq_mul] at h1
  have hBnn : 0 ≤ μ.real B := measureReal_nonneg
  have h2 : μ.real D * (4 * t ^ 2) ≤ (2 * t ^ 2) * μ.real B := by nlinarith
  have ht2 : 0 < t ^ 2 := by positivity
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem A_mono (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {m n : ℕ} (h : m ≤ n) :
    A a m ≤ A a n := by
  unfold A
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro i hi _
    simp only [Finset.mem_Icc] at hi
    exact (ha_pos i hi.1).le

theorem a_mono' (a : ℕ → ℝ) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) {i k : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) : a i ≤ a k := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (ha_mono k (by omega))

theorem Icc_one (m : ℕ) : Finset.Icc 1 m = Finset.Ioc 0 m := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem refl_sum (a : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Finset.Ioc 0 m, a (m + 1 - j) = A a m := by
  unfold A
  rw [Icc_one]
  apply Finset.sum_nbij' (fun j => m + 1 - j) (fun j => m + 1 - j)
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj
    omega
  · intro j _
    rfl

/-- Deterministic split `S̄_{N₁} = S̄_n + F + Y` with `|F| ≤ A_{N₁} − T − A_n`. -/
theorem sbar_split {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} (x : ℕ → Ω → ℝ)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) (n N₁ : ℕ) (hn : n ≤ N₁) :
    ∀ᵐ ω ∂μ, |Sbar a x N₁ ω - Sbar a x n ω - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) * x j ω|
      ≤ A a N₁ - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) - A a n := by
  filter_upwards [hall x hbd] with ω hω
  have e1 : Sbar a x N₁ ω = ∑ j ∈ Finset.Ioc 0 n, a (N₁ + 1 - j) * x j ω
      + ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) * x j ω := by
    unfold Sbar
    rw [Icc_one, Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hn]
  have e2 : Sbar a x n ω = ∑ j ∈ Finset.Ioc 0 n, a (n + 1 - j) * x j ω := by
    unfold Sbar
    rw [Icc_one]
  have e3 : A a N₁ = ∑ j ∈ Finset.Ioc 0 n, a (N₁ + 1 - j)
      + ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) := by
    rw [← refl_sum, Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hn]
  have e4 : A a n = ∑ j ∈ Finset.Ioc 0 n, a (n + 1 - j) := (refl_sum a n).symm
  have key : |∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) * x j ω|
      ≤ ∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    simp only [Finset.mem_Ioc] at hj
    have hd : 0 ≤ a (N₁ + 1 - j) - a (n + 1 - j) :=
      sub_nonneg.2 (a_mono' a ha_mono (by omega) (by omega))
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_of_le_one_right hd (hω j (by omega))
  have eL : Sbar a x N₁ ω - Sbar a x n ω - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) * x j ω
      = ∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) * x j ω := by
    rw [e1, e2]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have eR : A a N₁ - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) - A a n
      = ∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) := by
    rw [e3, e4, Finset.sum_sub_distrib]
    ring
  rw [eL, eR]
  exact key

/-- Display (4.15). -/
theorem main {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (ε : ℝ) (hε : 0 < ε) (N₀ N₁ : ℕ) (hN₀ : 1 ≤ N₀) (hN : N₀ < N₁)
    (hA : A a N₁ ≤ (1 + ε / 3) * A a N₀) :
    μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ 2 * μ.real {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω} := by
  classical
  have hA0 : 0 < A a N₀ := by
    refine lt_of_lt_of_le (ha_pos 1 le_rfl) ?_
    unfold A
    exact Finset.single_le_sum (f := a) (fun i hi => (ha_pos i (Finset.mem_Icc.1 hi).1).le)
      (Finset.mem_Icc.2 ⟨le_rfl, hN₀⟩)
  have hSm : ∀ m k : ℕ, m ≤ k → StronglyMeasurable[ℱ k] (Sbar a x m) := by
    intro m k hmk
    show StronglyMeasurable[ℱ k] (fun ω => ∑ j ∈ Finset.Icc 1 m, a (m + 1 - j) * x j ω)
    apply Finset.stronglyMeasurable_fun_sum
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact (((hx j hj.1).1).mono (ℱ.mono (by omega))).const_mul _
  let Bs : ℕ → Set Ω := fun n =>
    {ω | ε * A a N₀ < Sbar a x n ω} ∩ ⋂ m ∈ Finset.Ioo N₀ n, {ω | Sbar a x m ω ≤ ε * A a N₀}
  have hBm : ∀ n, MeasurableSet[ℱ n] (Bs n) := by
    intro n
    show MeasurableSet[ℱ n] ({ω | ε * A a N₀ < Sbar a x n ω}
      ∩ ⋂ m ∈ Finset.Ioo N₀ n, {ω | Sbar a x m ω ≤ ε * A a N₀})
    refine (stronglyMeasurable_const.measurableSet_lt (hSm n n le_rfl)).inter ?_
    refine Finset.measurableSet_biInter _ (fun m hm => ?_)
    simp only [Finset.mem_Ioo] at hm
    exact (hSm m n hm.2.le).measurableSet_le stronglyMeasurable_const
  have hBm0 : ∀ n, MeasurableSet (Bs n) := fun n => ℱ.le n _ (hBm n)
  set G : Set Ω := {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω} with hG
  have hGm : MeasurableSet G :=
    stronglyMeasurable_const.measurableSet_lt ((hSm N₁ N₁ le_rfl).mono (ℱ.le N₁))
  have hsub : {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ⊆ ⋃ n ∈ Finset.Ioc N₀ N₁, Bs n := by
    rintro ω ⟨n, hn, hlt⟩
    set s := (Finset.Ioc N₀ N₁).filter (fun k => ε * A a N₀ < Sbar a x k ω) with hs
    have hne : s.Nonempty := ⟨n, Finset.mem_filter.2 ⟨hn, hlt⟩⟩
    have hmin : s.min' hne ∈ Finset.Ioc N₀ N₁ ∧ ε * A a N₀ < Sbar a x (s.min' hne) ω :=
      Finset.mem_filter.1 (Finset.min'_mem s hne)
    refine Set.mem_iUnion₂.2 ⟨s.min' hne, hmin.1, hmin.2, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro m hm
    by_contra hc
    rw [not_le] at hc
    simp only [Finset.mem_Ioo] at hm
    have hmax := (Finset.mem_Ioc.1 hmin.1).2
    have hms : m ∈ s := Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hm.1, by omega⟩, hc⟩
    have := Finset.min'_le s m hms
    omega
  have hstep : ∀ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n) ≤ 2 * μ.real (Bs n ∩ G) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hcpos : ∀ j ∈ Finset.Ioc n N₁, 0 ≤ a (N₁ + 1 - j) := by
      intro j hj
      simp only [Finset.mem_Ioc] at hj
      exact (ha_pos _ (by omega)).le
    set T := ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg hcpos
    have hεA : 0 < ε * A a N₀ := mul_pos hε hA0
    set t := ε * A a N₀ / 6 + T with ht
    have htpos : 0 < t := by linarith
    have hσ : ∑ j ∈ Finset.Ioc n N₁, (fun j => a (N₁ + 1 - j)) j ^ 2 < t ^ 2 := by
      have h1 : ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) ^ 2 ≤ T ^ 2 := by
        rw [sq T, hT, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hj
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hcpos hj) (hcpos j hj)
      have h2 : T ^ 2 < t ^ 2 := by nlinarith
      simp only
      linarith
    have hAn : A a N₀ ≤ A a n := A_mono a ha_pos hn.1.le
    have hY : ∀ᵐ ω ∂μ, ω ∈ Bs n \ G →
        ∑ j ∈ Finset.Ioc n N₁, (fun j => a (N₁ + 1 - j)) j * x j ω ≤ -t := by
      filter_upwards [sbar_split x hbd a ha_mono n N₁ hn.2] with ω hω hωD
      obtain ⟨⟨h1, -⟩, h2⟩ := hωD
      simp only [Set.mem_setOf_eq] at h1
      simp only [hG, Set.mem_setOf_eq, not_lt] at h2
      have h3 := (abs_le.1 hω).1
      linarith
    have hD : MeasurableSet (Bs n \ G) := (hBm0 n).diff hGm
    have hc := cantelli ℱ x hx hbd n N₁ (fun j => a (N₁ + 1 - j)) (Bs n) (Bs n \ G) (hBm n) hD
      Set.diff_subset t htpos hσ hY
    have hu : μ.real (Bs n) ≤ μ.real (Bs n ∩ G) + μ.real (Bs n \ G) := by
      calc μ.real (Bs n) = μ.real ((Bs n ∩ G) ∪ (Bs n \ G)) := by rw [Set.inter_union_diff]
        _ ≤ _ := measureReal_union_le _ _
    linarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Ioc N₀ N₁)) (fun n => Bs n ∩ G) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ioc, Set.mem_Ioc] at hi hj
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨⟨hi1, hi2⟩, -⟩ ⟨⟨hj1, hj2⟩, -⟩
    simp only [Set.mem_setOf_eq, Set.mem_iInter] at hi1 hi2 hj1 hj2
    rcases lt_or_gt_of_ne hij with h | h
    · have := hj2 i (Finset.mem_Ioo.2 ⟨hi.1, h⟩)
      linarith
    · have := hi2 j (Finset.mem_Ioo.2 ⟨hj.1, h⟩)
      linarith
  have hsum : ∑ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n ∩ G) ≤ μ.real G := by
    rw [← measureReal_biUnion_finset hdisj (fun n _ => (hBm0 n).inter hGm)]
    exact measureReal_mono (Set.iUnion₂_subset fun n _ => Set.inter_subset_right)
  calc μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ μ.real (⋃ n ∈ Finset.Ioc N₀ N₁, Bs n) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N₀ N₁, 2 * μ.real (Bs n ∩ G) := Finset.sum_le_sum hstep
    _ = 2 * ∑ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n ∩ G) := by rw [Finset.mul_sum]
    _ ≤ 2 * μ.real G := by linarith

end K2b1982cee

open MeasureTheory AzumaWeightedSums.StrongLaw in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (ε : ℝ) (hε : 0 < ε) (N₀ N₁ : ℕ) (hN₀ : 1 ≤ N₀) (hN : N₀ < N₁)
    (hA : A a N₁ ≤ (1 + ε / 3) * A a N₀) :
    μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ 2 * μ.real {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω} := by
  exact K2b1982cee.main ℱ x hx hbd a ha_pos ha_mono ε hε N₀ N₁ hN₀ hN hA
