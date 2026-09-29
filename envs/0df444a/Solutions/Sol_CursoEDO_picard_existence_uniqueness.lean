-- Prove2me | solution 1 for CursoEDO.picard_existence_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T14:19:43.512066+00:00
-- url     : https://prove2.me/submissions/7ea0ed29-33d0-45e7-8fd1-14f642a1fc38

import Mathlib
import Definitions.Def_CursoEDO_Defs

open CursoEDO Metric Set Function

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (t₀ : ℝ) (x₀ : E) (a b M α : ℝ) (c : ℝ) (f : ℝ → E → E)
    (U : Set (ℝ × E))
    (ha : 0 < a) (hb : 0 < b)
    (hU : U = Set.Icc (t₀ - a) (t₀ + a) ×ˢ Metric.closedBall x₀ b)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) U)
    (hM : IsLUB {r : ℝ | ∃ p ∈ U, r = ‖f p.1 p.2‖} M) (hM0 : 0 < M)
    (hlip : LipschitzInSecondVar U (fun p : ℝ × E => f p.1 p.2) c)
    (hα : α = min a (b / M)) :
    ∃ φ : ℝ → E, IsCauchySolutionOn f U t₀ x₀ (Set.Icc (t₀ - α) (t₀ + α)) φ ∧
      ∀ ψ : ℝ → E, IsCauchySolutionOn f U t₀ x₀ (Set.Icc (t₀ - α) (t₀ + α)) ψ →
        Set.EqOn φ ψ (Set.Icc (t₀ - α) (t₀ + α)) := by
  obtain ⟨hc, hlip2⟩ := hlip
  obtain ⟨bn, hbn⟩ : ∃ bn : NNReal, (bn : ℝ) = b := ⟨b.toNNReal, Real.coe_toNNReal b hb.le⟩
  obtain ⟨Mn, hMn⟩ : ∃ Mn : NNReal, (Mn : ℝ) = M := ⟨M.toNNReal, Real.coe_toNNReal M hM0.le⟩
  obtain ⟨cn, hcn⟩ : ∃ cn : NNReal, (cn : ℝ) = c := ⟨c.toNNReal, Real.coe_toNNReal c hc.le⟩
  have hα0 : 0 < α := by rw [hα]; exact lt_min ha (div_pos hb hM0)
  have hαa : α ≤ a := by rw [hα]; exact min_le_left _ _
  have hαb : M * α ≤ b := by
    have hle : α ≤ b / M := by rw [hα]; exact min_le_right _ _
    calc M * α ≤ M * (b / M) := by nlinarith
      _ = b := by field_simp
  have ht₀I : t₀ ∈ Set.Icc (t₀ - α) (t₀ + α) := by constructor <;> linarith
  have hsub : Set.Icc (t₀ - α) (t₀ + α) ⊆ Set.Icc (t₀ - a) (t₀ + a) := by
    apply Set.Icc_subset_Icc <;> linarith
  have memU : ∀ t ∈ Set.Icc (t₀ - α) (t₀ + α), ∀ x ∈ Metric.closedBall x₀ b, (t, x) ∈ U := by
    intro t ht x hx
    rw [hU]
    exact ⟨hsub ht, hx⟩
  -- the data of the Picard-Lindelöf structure
  set T₀ : Set.Icc (t₀ - α) (t₀ + α) := ⟨t₀, ht₀I⟩ with hT₀
  have hPL : IsPicardLindelof f T₀ x₀ bn 0 Mn cn := by
    constructor
    · intro t ht
      rw [hbn]
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [dist_eq_norm, dist_eq_norm, hcn]
      exact hlip2 t x y (memU t ht x hx) (memU t ht y hy)
    · intro x hx
      rw [hbn] at hx
      have hmap : Set.MapsTo (fun t : ℝ => (t, x)) (Set.Icc (t₀ - α) (t₀ + α)) U :=
        fun t ht => memU t ht x hx
      exact hcont.comp (Continuous.continuousOn (by fun_prop)) hmap
    · intro t ht x hx
      rw [hbn] at hx
      rw [hMn]
      exact hM.1 ⟨(t, x), memU t ht x hx, rfl⟩
    · have hmax : max (t₀ + α - (T₀ : ℝ)) ((T₀ : ℝ) - (t₀ - α)) = α := by
        simp [hT₀]
      rw [hmax, hMn, hbn]
      simp only [NNReal.coe_zero, sub_zero]
      linarith
  -- existence
  obtain ⟨A, hA⟩ := ODE.FunSpace.exists_isFixedPt_next hPL (mem_closedBall_self le_rfl)
  have hφball : ∀ t : ℝ, A.compProj t ∈ Metric.closedBall x₀ b := by
    intro t
    have := A.compProj_mem_closedBall (a := bn) hPL.mul_max_le (t := t)
    rwa [hbn] at this
  have hφ₀ : A.compProj t₀ = x₀ := by
    have h1 : A.compProj (T₀ : ℝ) = A.toFun T₀ := ODE.FunSpace.compProj_val
    have h2 : A.toFun T₀ = x₀ := A.apply_of_zero
    simpa [hT₀] using h1.trans h2
  have hφderiv : ∀ t ∈ Set.Icc (t₀ - α) (t₀ + α),
      HasDerivWithinAt A.compProj (f t (A.compProj t)) (Set.Icc (t₀ - α) (t₀ + α)) t := by
    intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc T₀.2 hPL.continuousOn_uncurry
      A.continuous_compProj.continuousOn
      (fun _ _ => A.compProj_mem_closedBall hPL.mul_max_le) x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hA]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  refine ⟨A.compProj,
    ⟨ht₀I, hφ₀, fun t ht => memU t ht _ (hφball t), hφderiv⟩, ?_⟩
  -- uniqueness
  intro ψ hψ
  obtain ⟨-, hψ₀, hψgraph, hψderiv⟩ := hψ
  have hballψ : ∀ t ∈ Set.Icc (t₀ - α) (t₀ + α), ψ t ∈ Metric.closedBall x₀ b := by
    intro t ht
    have hmem := hψgraph t ht
    rw [hU] at hmem
    exact hmem.2
  have hlipK : ∀ t ∈ Set.Ioo (t₀ - α) (t₀ + α),
      LipschitzOnWith cn (f t) (Metric.closedBall x₀ b) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm, hcn]
    exact hlip2 t x y (memU t (Set.Ioo_subset_Icc_self ht) x hx)
      (memU t (Set.Ioo_subset_Icc_self ht) y hy)
  have ht₀Ioo : t₀ ∈ Set.Ioo (t₀ - α) (t₀ + α) := by constructor <;> linarith
  refine ODE_solution_unique_of_mem_Icc (K := cn) (s := fun _ => Metric.closedBall x₀ b)
    hlipK ht₀Ioo (HasDerivWithinAt.continuousOn hφderiv) ?_ ?_
    (HasDerivWithinAt.continuousOn hψderiv) ?_ ?_ ?_
  · intro t ht
    exact (hφderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · intro t _
    exact hφball t
  · intro t ht
    exact (hψderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · intro t ht
    exact hballψ t (Set.Ioo_subset_Icc_self ht)
  · rw [hφ₀, hψ₀]
