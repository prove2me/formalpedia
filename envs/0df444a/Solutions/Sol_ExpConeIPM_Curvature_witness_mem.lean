-- Prove2me | solution 1 for ExpConeIPM.Curvature.witness_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:01:15.056542+00:00
-- url     : https://prove2.me/submissions/982d2879-ff0b-4357-997c-e8f6830616f6

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

set_option autoImplicit false
open scoped InnerProductSpace
open ExpConeIPM.Curvature Filter Topology

theorem solution :
    !₂[1, Real.exp (-2), 0] ∈ interior Kexp ∧
      !₂[(1 : ℝ), 0, 0] ∈ Kexp ∧ !₂[(1 : ℝ), 0, 0] ∉ interior Kexp := by
  set S : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | x 0 ≥ x 1 * Real.exp (x 2 / x 1) ∧ x 1 > 0} with hS
  have hKS : Kexp = closure S := rfl
  have c0 : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => x 0) := by fun_prop
  have c1 : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => x 1) := by fun_prop
  have c2 : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => x 2) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · -- interior
    set O : Set (EuclideanSpace ℝ (Fin 3)) := {x | 0 < x 1} with hO
    have hOopen : IsOpen O := isOpen_lt continuous_const c1
    have hcont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => x 0 - x 1 * Real.exp (x 2 / x 1)) O := by
      intro x hx
      have hx1 : x 1 ≠ 0 := ne_of_gt hx
      apply ContinuousAt.continuousWithinAt
      have : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 3) => x 2 / x 1) x :=
        ContinuousAt.div c2.continuousAt c1.continuousAt hx1
      exact c0.continuousAt.sub (c1.continuousAt.mul (Real.continuous_exp.continuousAt.comp this))
    have hT : IsOpen (O ∩ (fun x : EuclideanSpace ℝ (Fin 3) => x 0 - x 1 * Real.exp (x 2 / x 1)) ⁻¹' (Set.Ioi 0)) :=
      hcont.isOpen_inter_preimage hOopen isOpen_Ioi
    have hTS : (O ∩ (fun x : EuclideanSpace ℝ (Fin 3) => x 0 - x 1 * Real.exp (x 2 / x 1)) ⁻¹' (Set.Ioi 0)) ⊆ S := by
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, hO, Set.mem_setOf_eq] at hx
      exact ⟨by linarith [hx.2], hx.1⟩
    have hmem : (!₂[1, Real.exp (-2), 0] : EuclideanSpace ℝ (Fin 3)) ∈
        (O ∩ (fun x : EuclideanSpace ℝ (Fin 3) => x 0 - x 1 * Real.exp (x 2 / x 1)) ⁻¹' (Set.Ioi 0)) := by
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, hO, Set.mem_setOf_eq]
      simp
      exact Real.exp_pos _
    exact interior_mono (subset_closure) ((interior_maximal hTS hT) hmem)
  · -- (1,0,0) in the closure
    have hlim : Tendsto (fun ε : ℝ => (!₂[(1 : ℝ), 0, 0] : EuclideanSpace ℝ (Fin 3)) +
        ε • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) (𝓝[>] 0) (𝓝 !₂[(1 : ℝ), 0, 0]) := by
      have : Continuous (fun ε : ℝ => (!₂[(1 : ℝ), 0, 0] : EuclideanSpace ℝ (Fin 3)) +
          ε • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by fun_prop
      have h := this.tendsto 0
      simp only [zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    show _ ≥ _ ∧ _ > _
    simp
    constructor
    · linarith [hε.2]
    · exact hε.1
  · -- (1,0,0) not in the interior
    intro hint
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨r, hr, hball⟩ := hint
    have hnonneg : ∀ x ∈ Kexp, 0 ≤ x 1 := by
      intro x hx
      have : Kexp ⊆ {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x 1} := by
        refine closure_minimal ?_ (isClosed_le continuous_const c1)
        intro y hy; exact le_of_lt hy.2
      exact this hx
    set q : EuclideanSpace ℝ (Fin 3) := (!₂[(1 : ℝ), 0, 0] : EuclideanSpace ℝ (Fin 3)) +
      (-(r / 2)) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) with hq
    have hqball : q ∈ Metric.ball (!₂[(1 : ℝ), 0, 0] : EuclideanSpace ℝ (Fin 3)) r := by
      rw [Metric.mem_ball, dist_eq_norm, hq]
      simp [norm_smul, abs_of_pos hr]
      linarith
    have := hnonneg q (hball hqball)
    simp [hq] at this
    linarith
