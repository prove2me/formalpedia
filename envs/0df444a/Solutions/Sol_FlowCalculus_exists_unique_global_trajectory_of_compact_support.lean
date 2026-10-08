-- Prove2me | solution 1 for FlowCalculus.exists_unique_global_trajectory_of_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:38:35.404462+00:00
-- url     : https://prove2.me/submissions/f57000e1-eb1e-4abe-bfc7-1730881d3570

import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith

open Set
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (t₀ : ℝ) (x : V) :
    ∃! γ : ℝ → V, γ t₀ = x ∧ ∀ t, HasDerivAt γ (X t (γ t)) t := by
  classical
  have bounded_on_time_intervals (a b : ℝ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ y, ‖X t y‖ ≤ B := by
    obtain ⟨K, hK, hz⟩ := hsupp
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hX.continuous.norm.continuousOn
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro t ht y
    by_cases hy : y ∈ K
    · exact (hB (mem_image_of_mem (fun p : ℝ × V => ‖X p.1 p.2‖)
        (show (t, y) ∈ Icc a b ×ˢ K from ⟨ht, hy⟩))).trans (le_max_right _ _)
    · simp only [hz t y hy, norm_zero]
      exact le_max_left _ _
  have hex : ∀ r : ℝ, ∃ γ : ℝ → V, γ t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - r) (t₀ + r), HasDerivAt γ (X t (γ t)) t := by
    intro r
    by_cases hr : 0 < r
    · obtain ⟨B, hB, hb⟩ := bounded_on_time_intervals (t₀-r) (t₀+r)
      obtain ⟨L, hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp (t₀-r) (t₀+r)
      let tI : Icc (t₀-r) (t₀+r) := ⟨t₀, by constructor <;> linarith⟩
      let R : ℝ≥0 := ⟨B*r+1, by positivity⟩
      have hpl : IsPicardLindelof X tI x R 0 ⟨B, hB⟩ L :=
        { lipschitzOnWith := fun t ht => (hL t ht).lipschitzOnWith
          continuousOn := fun y _ =>
            (hX.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
          norm_le := fun t ht y _ => hb t ht y
          mul_max_le := by
            change B * max (t₀+r-t₀) (t₀-(t₀-r)) ≤ (B*r+1)-0
            simp only [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero]
            linarith }
      obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
      refine ⟨γ, hγ0, ?_⟩
      intro t ht
      exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · refine ⟨fun _ => x, rfl, ?_⟩
      intro t ht
      exfalso
      linarith [ht.1, ht.2]
  choose γ hγ0 hγ using hex
  let ψ : ℝ → V := fun t => γ (|t-t₀|+1) t
  have heq : ∀ R > (0 : ℝ), EqOn ψ (γ R) (Ioo (t₀-R) (t₀+R)) := by
    intro R hR t ht
    let Q := |t-t₀|+1
    have hQ : 0 < Q := by dsimp [Q]; positivity
    let S := min Q R
    have hS : 0 < S := lt_min hQ hR
    have hsQ : S ≤ Q := min_le_left _ _
    have hsR : S ≤ R := min_le_right _ _
    have hts : t ∈ Ioo (t₀-S) (t₀+S) := by
      have htr : |t-t₀| < R := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htq : |t-t₀| < Q := by dsimp [Q]; linarith
      have hh : |t-t₀| < S := lt_min htq htr
      constructor <;> linarith [(abs_lt.mp hh).1, (abs_lt.mp hh).2]
    obtain ⟨L, hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp (t₀-S) (t₀+S)
    have hun := ODE_solution_unique_of_mem_Ioo
      (s := fun _ => Set.univ)
      (fun s hs => (hL s (Ioo_subset_Icc_self hs)).lipschitzOnWith)
      (show t₀ ∈ Ioo (t₀-S) (t₀+S) from ⟨by linarith, by linarith⟩)
      (f := γ Q) (g := γ R)
      (fun s hs => ⟨hγ Q s ⟨by linarith [hs.1], by linarith [hs.2]⟩, trivial⟩)
      (fun s hs => ⟨hγ R s ⟨by linarith [hs.1], by linarith [hs.2]⟩, trivial⟩)
      (by rw [hγ0 Q, hγ0 R])
    exact hun hts
  refine ⟨ψ, ⟨hγ0 _, ?_⟩, ?_⟩
  ·
    intro t
    let R := |t-t₀|+1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (t₀-R) (t₀+R) := by
      have hh : |t-t₀| < R := by dsimp [R]; linarith
      constructor <;> linarith [(abs_lt.mp hh).1, (abs_lt.mp hh).2]
    have hev : ψ =ᶠ[𝓝 t] γ R := Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) (heq R hR)
    rw [heq R hR ht]
    exact (hγ R t ht).congr_of_eventuallyEq hev
  
  · rintro η ⟨hη0, hη⟩
    funext t
    let R := |t-t₀|+1
    have ht : t ∈ Ioo (t₀-R) (t₀+R) := by
      have hh : |t-t₀| < R := by dsimp [R]; linarith
      constructor <;> linarith [(abs_lt.mp hh).1, (abs_lt.mp hh).2]
    obtain ⟨L, hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp (t₀-R) (t₀+R)
    have heq0 : η t₀ = γ R t₀ := hη0.trans (hγ0 R).symm
    have hh := ODE_solution_unique_of_mem_Ioo
      (s := fun _ => Set.univ)
      (fun s hs => (hL s (Ioo_subset_Icc_self hs)).lipschitzOnWith)
      (show t₀ ∈ Ioo (t₀-R) (t₀+R) from ⟨by dsimp [R]; linarith [abs_nonneg (t-t₀)], by dsimp [R]; linarith [abs_nonneg (t-t₀)]⟩)
      (f := η) (g := γ R)
      (fun s _ => ⟨hη s, trivial⟩)
      (fun s hs => ⟨hγ R s hs, trivial⟩) heq0
    exact hh ht
