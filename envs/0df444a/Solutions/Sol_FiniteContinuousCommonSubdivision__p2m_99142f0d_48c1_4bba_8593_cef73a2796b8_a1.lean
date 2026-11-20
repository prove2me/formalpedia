-- Prove2me | solution 1 for FiniteContinuousCommonSubdivision__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:07:52.956174+00:00
-- url     : https://prove2.me/submissions/c2432fb3-6499-45ee-839e-f4ecb3812c62

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

theorem solution
    {ι : Type} [DecidableEq ι] (f : ι → ℝ → ℝ) (N : Finset ι)
    (hf : ∀ i ∈ N, ContinuousOn (f i) (Set.Icc (0 : ℝ) 1))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : ℕ → ℝ),
      0 < m ∧ t 0 = 0 ∧ t m = 1 ∧
      (∀ k ≤ m, t k ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ k < m, t k ≤ t (k + 1)) ∧
      ∀ k < m, ∀ i ∈ N, |f i (t (k + 1)) - f i (t k)| ≤ δ := by
  -- a common modulus of uniform continuity
  have key : ∀ M : Finset ι, M ⊆ N → ∃ η > (0:ℝ), ∀ i ∈ M, ∀ x ∈ Set.Icc (0:ℝ) 1,
      ∀ y ∈ Set.Icc (0:ℝ) 1, dist x y < η → dist (f i x) (f i y) < δ := by
    intro M
    induction M using Finset.induction_on with
    | empty => intro _; exact ⟨1, one_pos, by simp⟩
    | insert a M ha ih =>
      intro hsub
      obtain ⟨η₁, hη₁, h₁⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have huc : UniformContinuousOn (f a) (Set.Icc (0:ℝ) 1) :=
        IsCompact.uniformContinuousOn_of_continuous isCompact_Icc (hf a (hsub (Finset.mem_insert_self a M)))
      rw [Metric.uniformContinuousOn_iff] at huc
      obtain ⟨η₂, hη₂, h₂⟩ := huc δ hδ
      refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
      intro i hi x hx y hy hxy
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h₂ x hx y hy (lt_of_lt_of_le hxy (min_le_right _ _))
      · exact h₁ i hi x hx y hy (lt_of_lt_of_le hxy (min_le_left _ _))
  obtain ⟨η, hη, hU⟩ := key N subset_rfl
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / η)
  have hm0 : 0 < m := by
    have : (0:ℝ) < m := lt_trans (by positivity) hm
    exact_mod_cast this
  have hmR : (0:ℝ) < m := by exact_mod_cast hm0
  refine ⟨m, fun k => (k:ℝ) / m, hm0, by simp, by field_simp, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hmR]; exact_mod_cast hk
  · intro k _
    apply div_le_div_of_nonneg_right _ hmR.le
    push_cast; linarith
  · intro k hk i hi
    have hk1 : (k:ℝ) + 1 ≤ m := by exact_mod_cast hk
    have hmem1 : ((k+1:ℕ):ℝ) / m ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hmR]; push_cast; exact hk1⟩
    have hmem0 : (k:ℝ) / m ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hmR]; linarith⟩
    have hd : dist (((k+1:ℕ):ℝ) / m) ((k:ℝ) / m) < η := by
      rw [Real.dist_eq]
      have : ((k+1:ℕ):ℝ) / m - (k:ℝ) / m = 1 / m := by push_cast; ring
      rw [this, abs_of_pos (by positivity)]
      rw [div_lt_iff₀ hmR]
      rw [div_lt_iff₀ hη] at hm
      linarith
    have := hU i hi _ hmem1 _ hmem0 hd
    rw [Real.dist_eq] at this
    exact this.le
