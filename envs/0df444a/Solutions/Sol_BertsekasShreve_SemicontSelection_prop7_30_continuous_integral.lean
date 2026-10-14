-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.prop7_30_continuous_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:52:14.033457+00:00
-- url     : https://prove2.me/submissions/74cffec5-1630-4099-b30d-85e642e1d61d

import Mathlib



namespace BertsekasShreve.SemicontSelection

open MeasureTheory TopologicalSpace Filter Topology

theorem p730_core {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : BoundedContinuousFunction (X × Y) ℝ) :
    Continuous (fun x => ∫ y, f (x, y) ∂(q x : Measure Y)) := by
  rw [continuous_iff_seqContinuous]
  intro xs x hxs
  -- slice functions
  let sl : X → BoundedContinuousFunction Y ℝ := fun z => f.compContinuous ⟨fun y => (z, y), by fun_prop⟩
  have hsl : ∀ z y, sl z y = f (z, y) := fun z y => rfl
  have hqs : Tendsto (fun n => q (xs n)) atTop (𝓝 (q x)) := (hq.tendsto x).comp hxs
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hqs
  -- compact tails
  let S : ℕ → Set X := fun N => insert x (Set.range fun m => xs (N + m))
  have hS : ∀ N, IsCompact (S N) := fun N =>
    Tendsto.isCompact_insert_range (hxs.comp (tendsto_atTop_atTop_of_monotone
      (fun a b h => by omega) (fun b => ⟨b, by omega⟩)))
  let φ : Y → X → ℝ := fun y z => |f (z, y) - f (x, y)|
  have hφc : Continuous ↿φ := by
    show Continuous (fun p : Y × X => |f (p.2, p.1) - f (x, p.1)|)
    fun_prop
  have hφb : ∀ y z, φ y z ≤ 2 * ‖f‖ := by
    intro y z
    have := f.dist_le_two_norm (z, y) (x, y)
    rwa [Real.dist_eq] at this
  have hφ0 : ∀ y z, 0 ≤ φ y z := fun y z => abs_nonneg _
  let hN : ℕ → Y → ℝ := fun N y => sSup (φ y '' S N)
  have hNc : ∀ N, Continuous (hN N) := fun N => (hS N).continuous_sSup hφc
  have hNne : ∀ N, (S N).Nonempty := fun N => ⟨x, Set.mem_insert _ _⟩
  have hNbdd : ∀ N y, BddAbove (φ y '' S N) := fun N y =>
    ⟨2 * ‖f‖, by rintro _ ⟨z, -, rfl⟩; exact hφb y z⟩
  have hNle : ∀ N y, hN N y ≤ 2 * ‖f‖ := fun N y =>
    csSup_le ((hNne N).image _) (by rintro _ ⟨z, -, rfl⟩; exact hφb y z)
  have hNge : ∀ N y z, z ∈ S N → φ y z ≤ hN N y := fun N y z hz =>
    le_csSup (hNbdd N y) ⟨z, hz, rfl⟩
  have hN0 : ∀ N y, 0 ≤ hN N y := fun N y => le_trans (hφ0 y x) (hNge N y x (Set.mem_insert _ _))
  let H : ℕ → BoundedContinuousFunction Y ℝ := fun N => BoundedContinuousFunction.ofNormedAddCommGroup (hN N) (hNc N)
    (2 * ‖f‖) (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hN0 N y)]; exact hNle N y)
  have hH : ∀ N y, H N y = hN N y := fun N y => rfl
  -- pointwise convergence of hN to 0
  have hNlim : ∀ y, Tendsto (fun N => hN N y) atTop (𝓝 0) := by
    intro y
    have hc : Tendsto (fun n => f (xs n, y)) atTop (𝓝 (f (x, y))) :=
      ((f.continuous.comp (Continuous.prodMk_left y)).tendsto x).comp hxs
    rw [Metric.tendsto_atTop] at hc ⊢
    intro ε hε
    obtain ⟨N0, hN0'⟩ := hc (ε / 2) (by linarith)
    refine ⟨N0, fun N hNN => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hN0 N y)]
    have : hN N y ≤ ε / 2 := by
      apply csSup_le ((hNne N).image _)
      rintro _ ⟨z, hz, rfl⟩
      rcases hz with rfl | ⟨m, rfl⟩
      · simp [φ]; linarith
      · have := hN0' (N + m) (by omega)
        rw [Real.dist_eq] at this
        exact this.le
    linarith
  -- integral of hN against q x tends to 0
  have hint : Tendsto (fun N => ∫ y, hN N y ∂(q x : Measure Y)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (q x : Measure Y)) (fun _ => 2 * ‖f‖)
      (fun N => (hNc N).aestronglyMeasurable) (integrable_const _)
      (fun N => Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hN0 N y)]; exact hNle N y))
      (Filter.Eventually.of_forall hNlim)
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hNε⟩ := (Metric.tendsto_atTop.mp hint) (ε / 3) (by linarith)
  have hNε' := hNε N le_rfl
  rw [Real.dist_eq, sub_zero] at hNε'
  obtain ⟨M1, hM1⟩ := (Metric.tendsto_atTop.mp (hqs (H N))) (ε / 3) (by linarith)
  obtain ⟨M2, hM2⟩ := (Metric.tendsto_atTop.mp (hqs (sl x))) (ε / 3) (by linarith)
  refine ⟨max N (max M1 M2), fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have h1 := hM1 m (by omega)
  have h2 := hM2 m (by omega)
  simp only [hH, hsl] at h1 h2
  rw [Real.dist_eq] at h1 h2 ⊢
  -- bound the slice difference
  have hdiff : |∫ y, f (xs m, y) ∂(q (xs m) : Measure Y) - ∫ y, f (x, y) ∂(q (xs m) : Measure Y)|
      ≤ ∫ y, hN N y ∂(q (xs m) : Measure Y) := by
    have hsub := integral_sub ((sl (xs m)).integrable (q (xs m) : Measure Y)) ((sl x).integrable (q (xs m) : Measure Y))
    simp only [hsl] at hsub
    rw [← hsub]
    refine le_trans (abs_integral_le_integral_abs) (integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y => abs_nonneg _)) ((H N).integrable _)
      (Filter.Eventually.of_forall (fun y => ?_)))
    have hm' : xs m ∈ S N := Set.mem_insert_of_mem _ ⟨m - N, by show xs (N + (m - N)) = xs m; congr 1; omega⟩
    exact hNge N y (xs m) hm'
  have h3 := abs_lt.mp h1
  have h4 := abs_lt.mp h2
  have h5 := abs_le.mp hdiff
  have h6 := abs_lt.mp hNε'
  show |∫ y, f (xs m, y) ∂(q (xs m) : Measure Y) - ∫ y, f (x, y) ∂(q x : Measure Y)| < ε
  rw [abs_lt]
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

end BertsekasShreve.SemicontSelection

open BertsekasShreve.SemicontSelection
open MeasureTheory TopologicalSpace BertsekasShreve.SemicontSelection

theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : BoundedContinuousFunction (X × Y) ℝ) :
    Continuous (fun x => ∫ y, f (x, y) ∂(q x : Measure Y)) := by
  exact p730_core q hq f
