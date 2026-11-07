-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:37:32.660891+00:00
-- url     : https://prove2.me/submissions/8d81a61d-3f42-4e38-9096-61a22d24814a

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_asymptotic_eigenvector
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem emb_inv_cylEnd (s t : ℝ) : (cylEnd s t)⁻¹ = cylInf s t := by
  unfold cylEnd cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.exp_neg, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg,
    neg_mul, neg_neg]

/-- A finite-energy plane with a nondegenerate positive puncture at `∞` over a Reeb orbit `P` (not
assumed nondegenerate) converges to the trivial cylinder over `P` exponentially fast in `C^∞`. -/
theorem exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (P : ReebOrbit H) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b := by
  obtain ⟨hũ, -⟩ := isFiniteEnergyCurve_comp_inv H hH J hJ u hu
  have hA : endA H (fun z => u z⁻¹) cylEnd = endA H u cylInf := by
    funext p; simp only [endA, emb_inv_cylEnd]
  have hW : endW H (fun z => u z⁻¹) cylEnd = endW H u cylInf := by
    funext p; simp only [endW, emb_inv_cylEnd]
  have hnd : IsNondegenerateEnd H (fun z => u z⁻¹) cylEnd P 1 := by
    unfold IsNondegenerateEnd at huP ⊢
    rwa [hA, hW]
  obtain ⟨b, hb, hexp⟩ := (asymptotic_eigenvector H hH J hJ _ hũ P 1 (Or.inl rfl) hnd).1
  refine ⟨b, hb, ?_⟩
  unfold HasExpAsymptoticsEnd at hexp ⊢
  rwa [hA, hW] at hexp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (P : ReebOrbit H) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b :=
  exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd_aux H hH J hJ u hu P huP
