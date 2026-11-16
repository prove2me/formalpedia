-- Prove2me | solution 1 for DetTerminalEmbedding1373.Real.Supplement.claim_7_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:52:07.611667+00:00
-- url     : https://prove2.me/submissions/a0787f3d-e85e-4085-90ac-dc9ee1ec7e25

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_chd

open DetTerminalEmbedding1373.Real DetTerminalEmbedding1373.Real.Supplement

theorem solution {d m : ℕ} {J : Type} [Finite J] (y yhat : J → E d) (θ : ℝ)
    (A : E d →ₗ[ℝ] E m) (hθ : 0 ≤ θ) (hy : ∀ j, ‖y j - yhat j‖ ≤ θ) :
    chd A (Set.range y) ≤ chd A (Set.range yhat) +
      (‖LinearMap.toContinuousLinearMap A‖ + 1) * θ := by
  classical
  set K := ‖LinearMap.toContinuousLinearMap A‖
  have hK : 0 ≤ K := norm_nonneg _
  have hAle : ∀ v : E d, ‖A v‖ ≤ K * ‖v‖ := fun v =>
    (LinearMap.toContinuousLinearMap A).le_opNorm v
  have hchd0 : 0 ≤ chd A (Set.range yhat) := by
    unfold chd; exact Real.iSup_nonneg (fun _ => abs_nonneg _)
  -- boundedness of the function on the hull of `yhat`
  have hbdd : BddAbove (Set.range fun z : convexHull ℝ (Set.range yhat) =>
      |‖A z‖ - ‖(z : E d)‖|) := by
    have hfin : (Set.range yhat).Finite := Set.finite_range _
    have hcpt := hfin.isCompact_convexHull (𝕜 := ℝ)
    have hcont : Continuous fun v : E d => |‖A v‖ - ‖v‖| := by
      have := LinearMap.continuous_of_finiteDimensional A
      fun_prop
    obtain ⟨M, hM⟩ := (hcpt.image hcont).bddAbove
    refine ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hM ⟨z, z.2, rfl⟩
  unfold chd
  apply Real.iSup_le _ (by have := mul_nonneg (by linarith : 0 ≤ K + 1) hθ; unfold chd at hchd0; linarith)
  rintro ⟨z, hz⟩
  rw [convexHull_range_eq_exists_affineCombination] at hz
  obtain ⟨s, w, hw0, hw1, rfl⟩ := hz
  set zh : E d := s.affineCombination ℝ yhat w
  have hzh : zh ∈ convexHull ℝ (Set.range yhat) := by
    rw [convexHull_range_eq_exists_affineCombination]; exact ⟨s, w, hw0, hw1, rfl⟩
  have hz1 : s.affineCombination ℝ y w = ∑ i ∈ s, w i • y i :=
    Finset.affineCombination_eq_linear_combination s y w hw1
  have hz2 : zh = ∑ i ∈ s, w i • yhat i :=
    Finset.affineCombination_eq_linear_combination s yhat w hw1
  have hdiff : ‖s.affineCombination ℝ y w - zh‖ ≤ θ := by
    rw [hz1, hz2, ← Finset.sum_sub_distrib]
    calc ‖∑ i ∈ s, (w i • y i - w i • yhat i)‖ ≤ ∑ i ∈ s, ‖w i • y i - w i • yhat i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ s, w i * θ := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hw0 i hi)]
          exact mul_le_mul_of_nonneg_left (hy i) (hw0 i hi)
      _ = θ := by rw [← Finset.sum_mul, hw1, one_mul]
  have hle : |‖A zh‖ - ‖zh‖| ≤ ⨆ z : convexHull ℝ (Set.range yhat), |‖A z‖ - ‖(z : E d)‖| :=
    le_ciSup (f := fun z : convexHull ℝ (Set.range yhat) => |‖A z‖ - ‖(z : E d)‖|) hbdd ⟨zh, hzh⟩
  set z := s.affineCombination ℝ y w
  have h1 : |‖A z‖ - ‖A zh‖| ≤ K * θ := by
    calc |‖A z‖ - ‖A zh‖| ≤ ‖A z - A zh‖ := abs_norm_sub_norm_le _ _
      _ = ‖A (z - zh)‖ := by rw [map_sub]
      _ ≤ K * ‖z - zh‖ := hAle _
      _ ≤ K * θ := mul_le_mul_of_nonneg_left hdiff hK
  have h2 : |‖z‖ - ‖zh‖| ≤ θ := (abs_norm_sub_norm_le _ _).trans hdiff
  show |‖A z‖ - ‖z‖| ≤ _
  have : |‖A z‖ - ‖z‖| ≤ |‖A zh‖ - ‖zh‖| + K * θ + θ := by
    have := abs_sub_le (‖A z‖ - ‖z‖) (‖A zh‖ - ‖zh‖) 0
    rw [abs_sub_comm] at h1
    calc |‖A z‖ - ‖z‖| ≤ |‖A zh‖ - ‖zh‖| + |(‖A z‖ - ‖A zh‖) - (‖z‖ - ‖zh‖)| := by
          have e : ‖A z‖ - ‖z‖ = (‖A zh‖ - ‖zh‖) + ((‖A z‖ - ‖A zh‖) - (‖z‖ - ‖zh‖)) := by ring
          rw [e]; exact abs_add_le _ _
      _ ≤ |‖A zh‖ - ‖zh‖| + (|‖A z‖ - ‖A zh‖| + |‖z‖ - ‖zh‖|) := by
          gcongr; exact abs_sub _ _
      _ ≤ |‖A zh‖ - ‖zh‖| + K * θ + θ := by
          rw [abs_sub_comm] at h1; linarith
  nlinarith
