-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.lemma7_18_borel_selector
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:00:29.157003+00:00
-- url     : https://prove2.me/submissions/6145e61c-cee7-46c5-8e97-a04d47f77538

import Mathlib



namespace BertsekasShreve.SemicontSelection

open TopologicalSpace Filter Topology Metric

section Sel718

variable {Y : Type*} [MetricSpace Y]

theorem sel718_base (d : ℕ → Y) (hd : DenseRange d) (A : NonemptyCompacts Y) :
    ∃ j, infDist (d j) (A : Set Y) < (1/2 : ℝ) ^ 0 := by
  obtain ⟨a, ha⟩ := A.nonempty
  obtain ⟨j, hj⟩ := hd.exists_dist_lt a (by norm_num : (0:ℝ) < 1)
  refine ⟨j, ?_⟩
  rw [pow_zero]
  exact lt_of_le_of_lt (infDist_le_dist_of_mem ha) (by rw [dist_comm]; exact hj)

theorem sel718_step (d : ℕ → Y) (hd : DenseRange d) (A : NonemptyCompacts Y) (n k : ℕ) (hk : infDist (d k) (A : Set Y) < (1/2 : ℝ) ^ n) :
    ∃ j, infDist (d j) (A : Set Y) < (1/2 : ℝ) ^ (n + 1) ∧ dist (d j) (d k) < (1/2 : ℝ) ^ n := by
  obtain ⟨a, ha, hda⟩ := A.isCompact.exists_infDist_eq_dist A.nonempty (d k)
  have hpos : 0 < min ((1/2 : ℝ) ^ (n + 1)) ((1/2 : ℝ) ^ n - dist (d k) a) := by
    apply lt_min (by positivity); rw [← hda]; linarith
  obtain ⟨j, hj⟩ := hd.exists_dist_lt a hpos
  rw [dist_comm] at hj
  refine ⟨j, lt_of_le_of_lt (infDist_le_dist_of_mem ha) (lt_of_lt_of_le hj (min_le_left _ _)), ?_⟩
  have h1 := lt_of_lt_of_le hj (min_le_right _ _)
  have h2 := dist_triangle (d j) a (d k)
  rw [dist_comm a (d k)] at h2
  linarith

open Classical in
noncomputable def sel718Seq (d : ℕ → Y) (hd : DenseRange d) (A : NonemptyCompacts Y) :
    (n : ℕ) → {j : ℕ // infDist (d j) (A : Set Y) < (1/2 : ℝ) ^ n}
  | 0 => ⟨Nat.find (sel718_base d hd A), Nat.find_spec (sel718_base d hd A)⟩
  | n + 1 => ⟨Nat.find (sel718_step d hd A n (sel718Seq d hd A n).1 (sel718Seq d hd A n).2),
      (Nat.find_spec (sel718_step d hd A n (sel718Seq d hd A n).1 (sel718Seq d hd A n).2)).1⟩

theorem sel718Seq_succ_dist (d : ℕ → Y) (hd : DenseRange d) (A : NonemptyCompacts Y) (n : ℕ) :
    dist (d (sel718Seq d hd A (n + 1)).1) (d (sel718Seq d hd A n).1) < (1/2 : ℝ) ^ n := by
  classical
  exact (Nat.find_spec (sel718_step d hd A n (sel718Seq d hd A n).1 (sel718Seq d hd A n).2)).2

theorem sel718Seq_measurable (d : ℕ → Y) (hd : DenseRange d) [MeasurableSpace (NonemptyCompacts Y)]
    [OpensMeasurableSpace (NonemptyCompacts Y)] (n : ℕ) :
    Measurable (fun A => (sel718Seq d hd A n).1) := by
  classical
  induction n with
  | zero =>
    show Measurable (fun A => Nat.find (sel718_base d hd A))
    apply measurable_find
    intro j
    exact (isOpen_lt ((lipschitz_infDist_set (d j)).continuous) continuous_const).measurableSet
  | succ n ih =>
    show Measurable (fun A => Nat.find (sel718_step d hd A n (sel718Seq d hd A n).1 (sel718Seq d hd A n).2))
    apply measurable_find
    intro j
    have hS : MeasurableSet {A : NonemptyCompacts Y | dist (d j) (d (sel718Seq d hd A n).1) < (1/2 : ℝ) ^ n} :=
      ih (MeasurableSet.of_discrete (s := {m : ℕ | dist (d j) (d m) < (1/2 : ℝ) ^ n}))
    exact ((isOpen_lt ((lipschitz_infDist_set (d j)).continuous) continuous_const).measurableSet).inter hS

end Sel718

theorem l718_core {Y : Type*} [MetricSpace Y] [CompactSpace Y] :
    ∃ σ : NonemptyCompacts Y → Y,
      @Measurable _ _ (borel (NonemptyCompacts Y)) (borel Y) σ ∧ ∀ A : NonemptyCompacts Y, σ A ∈ A := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · have : IsEmpty (NonemptyCompacts Y) := ⟨fun A => by obtain ⟨a, _⟩ := A.nonempty; exact hY.false a⟩
    refine ⟨fun A => isEmptyElim A, ?_, fun A => isEmptyElim A⟩
    intro s _
    have : (fun A : NonemptyCompacts Y => (isEmptyElim A : Y)) ⁻¹' s = ∅ := Set.eq_empty_of_isEmpty _
    rw [this]; exact @MeasurableSet.empty _ (borel _)
  letI : MeasurableSpace (NonemptyCompacts Y) := borel _
  haveI : BorelSpace (NonemptyCompacts Y) := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  let d := denseSeq Y
  have hd : DenseRange d := denseRange_denseSeq Y
  let p : ℕ → NonemptyCompacts Y → Y := fun n A => d (sel718Seq d hd A n).1
  have hcauchy : ∀ A, CauchySeq (fun n => p n A) := by
    intro A
    apply cauchySeq_of_le_geometric_two (C := 2)
    intro n
    rw [dist_comm]
    have := sel718Seq_succ_dist d hd A n
    have e : (2:ℝ) / 2 / 2 ^ n = (1/2 : ℝ) ^ n := by rw [div_self two_ne_zero, one_div_pow, one_div]
    rw [e]; exact this.le
  let σ : NonemptyCompacts Y → Y := fun A => limUnder atTop (fun n => p n A)
  have hlim : ∀ A, Tendsto (fun n => p n A) atTop (𝓝 (σ A)) := fun A => (hcauchy A).tendsto_limUnder
  refine ⟨σ, ?_, fun A => ?_⟩
  · apply measurable_of_tendsto_metrizable (f := p)
    · intro n
      exact (measurable_from_nat (f := d)).comp (sel718Seq_measurable d hd n)
    · exact tendsto_pi_nhds.mpr hlim
  · have hc : Tendsto (fun n => infDist (p n A) (A : Set Y)) atTop (𝓝 (infDist (σ A) (A : Set Y))) :=
      ((continuous_infDist_pt _).tendsto _).comp (hlim A)
    have h0 : Tendsto (fun n => infDist (p n A) (A : Set Y)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => infDist_nonneg) (fun n => (sel718Seq d hd A n).2.le)
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := tendsto_nhds_unique hc h0
    exact (A.isCompact.isClosed.mem_iff_infDist_zero A.nonempty).mpr this

end BertsekasShreve.SemicontSelection

open BertsekasShreve.SemicontSelection
open TopologicalSpace BertsekasShreve.SemicontSelection

theorem solution {Y : Type*} [MetricSpace Y] [CompactSpace Y] :
    ∃ σ : NonemptyCompacts Y → Y,
      @Measurable _ _ (borel (NonemptyCompacts Y)) (borel Y) σ ∧ ∀ A : NonemptyCompacts Y, σ A ∈ A := by
  exact l718_core
