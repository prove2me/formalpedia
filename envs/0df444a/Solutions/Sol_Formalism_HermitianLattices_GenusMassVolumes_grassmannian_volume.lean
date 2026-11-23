-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.grassmannian_volume
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:59.019609+00:00
-- url     : https://prove2.me/submissions/c8fda9c6-a794-4b37-8767-f06caaf4fc5e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HolderExponentialMoments
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
private lemma prod_range_factorial_pos (n : ℕ) : 0 < ∏ i ∈ range n, (i.factorial : ℝ) :=
  prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : GrassmannianVolume := by
  intro p q
  have hF : ∀ n, 0 < ∏ i ∈ range n, (i.factorial : ℝ) := prod_range_factorial_pos
  have hPpos : ∀ n, 0 < ∏ i ∈ range n, Real.pi ^ (i + 1) :=
    fun n => prod_pos fun i _ => pow_pos Real.pi_pos _
  have hA : ∀ n, ∏ i ∈ range n, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) =
      2 ^ n * (∏ i ∈ range n, Real.pi ^ (i + 1)) / ∏ i ∈ range n, (i.factorial : ℝ) := by
    intro n
    rw [prod_div_distrib, prod_mul_distrib, prod_const, card_range]
  have hP : ∏ i ∈ range (p + q), Real.pi ^ (i + 1) =
      (∏ i ∈ range p, Real.pi ^ (i + 1)) * (∏ i ∈ range q, Real.pi ^ (i + 1)) *
        Real.pi ^ (p * q) := by
    rw [prod_range_add]
    have e : ∀ j ∈ range q, Real.pi ^ (p + j + 1) = Real.pi ^ p * Real.pi ^ (j + 1) := by
      intro j _
      rw [← pow_add]
      congr 1
    rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range, ← pow_mul]
    ring
  have hFF : (∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ) ≤
      ∏ i ∈ range (p + q), (i.factorial : ℝ) := by
    rw [prod_range_add]
    apply mul_le_mul_of_nonneg_left _ (hF p).le
    apply prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    exact_mod_cast Nat.factorial_le (by omega)
  have h1 := (hF p).ne'
  have h2 := (hF q).ne'
  have h3 := (hF (p + q)).ne'
  have h4 := (hPpos p).ne'
  have h5 := (hPpos q).ne'
  refine ⟨?_, ?_⟩
  · rw [hA, hA, hA, hP, pow_add]
    field_simp
  · rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (hF _)).2 hFF)
end Formalism.HermitianLattices.GenusMassVolumes
