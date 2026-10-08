-- Prove2me | solution 1 for FlowCalculus.exists_continuous_bijective_complete_flow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:51:09.774105+00:00
-- url     : https://prove2.me/submissions/af68227f-e3f4-46cd-9612-c6b30c31d25b

import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Mathlib.Tactic.Linarith

open Set Function Metric
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (X : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0) :
    ∃ ψ : ℝ → V → V, Continuous (fun p : ℝ × V => ψ p.1 p.2) ∧ (∀ y, ContDiff ℝ ∞ (fun t => ψ t y)) ∧ (∀ y, ψ 0 y = y) ∧ (∀ t, Function.Bijective (ψ t)) ∧
      ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by
  classical
  choose γ hγ huniq using
    (fun t₀ y => FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp t₀ y)
  let ψ : ℝ → V → V := fun t y => γ 0 y t
  have hcont : Continuous (fun p : ℝ × V => ψ p.1 p.2) := by
    rw [continuous_iff_continuousAt]
    intro p
    let R := |p.1|+1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : p.1 ∈ Ioo (-R) R := by
      have hh : |p.1| < R := by dsimp [R]; linarith
      exact abs_lt.mp hh
    obtain ⟨L, hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp (-R) R
    have hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (-R) R, ∀ y, ‖X t y‖ ≤ B := by
      obtain ⟨K, hK, hz⟩ := hsupp
      obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hX.continuous.norm.continuousOn
      refine ⟨max 0 B, le_max_left _ _, ?_⟩
      intro t ht y
      by_cases hy : y ∈ K
      · exact (hB (mem_image_of_mem (fun q : ℝ × V => ‖X q.1 q.2‖)
          (show (t, y) ∈ Icc (-R) R ×ˢ K from ⟨ht, hy⟩))).trans (le_max_right _ _)
      · simp only [hz t y hy, norm_zero]
        exact le_max_left _ _
    obtain ⟨B, hB, hb⟩ := hbound
    let tI : Icc (-R) R := ⟨0, by constructor <;> linarith⟩
    let a : ℝ≥0 := ⟨B*R+1, by positivity⟩
    have hpl : IsPicardLindelof X tI p.2 a 1 ⟨B, hB⟩ L :=
      { lipschitzOnWith := fun t ht => (hL t ht).lipschitzOnWith
        continuousOn := fun y _ =>
          (hX.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
        norm_le := fun t ht y _ => hb t ht y
        mul_max_le := by
          change B * max (R-0) (0-(-R)) ≤ (B*R+1)-1
          simp }
    obtain ⟨α, hα, hαc⟩ := hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    have haeq : ∀ z ∈ closedBall p.2 1,
        EqOn (γ 0 z) (fun t => α (z,t)) (Ioo (-R) R) := by
      intro z hz
      exact ODE_solution_unique_of_mem_Ioo
        (s := fun _ => Set.univ)
        (fun t ht => (hL t (Ioo_subset_Icc_self ht)).lipschitzOnWith)
        (show (0 : ℝ) ∈ Ioo (-R) R from ⟨by linarith, hR⟩)
        (fun t _ => ⟨(hγ 0 z).2 t, trivial⟩)
        (fun t ht => ⟨((hα z hz).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2), trivial⟩)
        ((hγ 0 z).1.trans (hα z hz).1.symm)
    have hbase : ContinuousAt α (p.2,p.1) :=
      hαc.continuousAt (prod_mem_nhds (closedBall_mem_nhds p.2 (ε := 1) (by norm_num))
        (Icc_mem_nhds ht.1 ht.2))
    have hc : ContinuousAt (fun q : ℝ × V => α (q.2,q.1)) p :=
      hbase.comp (f := fun q : ℝ × V => (q.2,q.1))
        (show ContinuousAt (fun q : ℝ × V => (q.2,q.1)) p from
        continuousAt_snd.prodMk continuousAt_fst)
    apply hc.congr_of_eventuallyEq
    filter_upwards [prod_mem_nhds (Ioo_mem_nhds ht.1 ht.2)
      (closedBall_mem_nhds p.2 (ε := 1) (by norm_num))] with q hq
    exact haeq q.2 hq.2 hq.1
  have htime : ∀ y, ContDiff ℝ ∞ (fun t => ψ t y) := by
    intro y
    rw [contDiff_iff_contDiffAt]
    intro t
    have hh : ContDiffOn ℝ ∞ (fun s => ψ s y) (Icc (t-1) (t+1)) :=
      ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := (⊤ : ℕ∞))
        (f := X) (u := Set.univ) hX.contDiffOn
        (fun s _ => ((hγ 0 y).2 s).hasDerivWithinAt) (mapsTo_univ _ _)
    exact hh.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  refine ⟨ψ, hcont, htime, fun y => (hγ 0 y).1, ?_, fun t y => (hγ 0 y).2 t⟩
  intro t
  constructor
  · intro y z heq
    have hy : γ 0 y = γ t (ψ t y) := huniq t (ψ t y) (γ 0 y) ⟨rfl, (hγ 0 y).2⟩
    have hz : γ 0 z = γ t (ψ t y) := huniq t (ψ t y) (γ 0 z) ⟨heq.symm, (hγ 0 z).2⟩
    have hh := congrArg (fun f : ℝ → V => f 0) (hy.trans hz.symm)
    simpa only [(hγ 0 y).1, (hγ 0 z).1] using hh
  · intro z
    let y := γ t z 0
    have hh : γ t z = γ 0 y := huniq 0 y (γ t z) ⟨rfl, (hγ t z).2⟩
    refine ⟨y, ?_⟩
    exact (congrArg (fun f : ℝ → V => f t) hh).symm.trans (hγ t z).1
