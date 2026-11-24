-- Prove2me | solution 1 for EisTube.gf_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:47:22.184174+00:00
-- url     : https://prove2.me/submissions/eb6aeaa0-99ae-4875-88b9-189c318afa77

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_reV_cz
import Theorems.Thm_EisTube_imV_cz
import Theorems.Thm_EisTube_norm_exp_sq_cz
import Theorems.Thm_EisTube_polyGaussBdd
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_polyGaussBdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
open EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]
variable {P : Type*} [TopologicalSpace P]
namespace EisTube
theorem _root_.solution {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {K : Set (ι → ℝ)} (hK : K ⊆ Ω) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ (y : ι → ℝ) p,
      ‖gf F (cz x y) p‖ ≤ C * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by
  obtain ⟨C, N, hC⟩ := hbd K hK hKc
  obtain ⟨M, hM⟩ := polyGaussBdd ι (1 / 2) (by norm_num) N
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  obtain ⟨S, hS⟩ : BddAbove ((fun x : ι → ℝ => ∑ i, x i ^ 2) '' K) :=
    hKc.bddAbove_image (by fun_prop)
  refine ⟨|C| * Real.exp S * M, by positivity, fun x hx y p => ?_⟩
  have hxS : ∑ i, x i ^ 2 ≤ S := hS ⟨x, hx, rfl⟩
  have hF := hC (cz x y) (by rw [reV_cz]; exact hx) p
  rw [imV_cz] at hF
  have hF' : ‖F (cz x y) p‖ ≤ |C| * h p * (1 + ‖y‖) ^ N :=
    hF.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (h0 p)) (by positivity))
  have e1 : Real.exp (-∑ i, y i ^ 2) =
      Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hB := hM y
  have hA : 0 ≤ |C| * h p := mul_nonneg (abs_nonneg _) (h0 p)
  rw [gf, norm_mul, norm_exp_sq_cz, e1]
  calc ‖F (cz x y) p‖ * (Real.exp (∑ i, x i ^ 2) *
          (Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2)))
      ≤ (|C| * h p * (1 + ‖y‖) ^ N) * (Real.exp (∑ i, x i ^ 2) *
          (Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2))) :=
        mul_le_mul_of_nonneg_right hF' (by positivity)
    _ = (|C| * h p) * Real.exp (∑ i, x i ^ 2) *
          ((1 + ‖y‖) ^ N * Real.exp (-(1 / 2 * ∑ i, y i ^ 2))) *
          Real.exp (-(∑ i, y i ^ 2) / 2) := by ring
    _ ≤ (|C| * h p) * Real.exp S * M * Real.exp (-(∑ i, y i ^ 2) / 2) := by
        gcongr
    _ = |C| * Real.exp S * M * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by ring
end EisTube
