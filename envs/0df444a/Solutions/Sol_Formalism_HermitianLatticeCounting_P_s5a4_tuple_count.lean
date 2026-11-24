-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_tuple_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:23.106263+00:00
-- url     : https://prove2.me/submissions/1b1e17db-89ce-4eef-a876-bd5d5376821f

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (n : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    (((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)).filter
      (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤ X * (1 + Real.log X) ^ n := by
  classical
  set P := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊) with hP
  have hpos : ∀ t ∈ P, ∀ i, 0 < t i := by
    intro t ht i
    have := (Fintype.mem_piFinset.mp ht) i
    exact (Finset.mem_Icc.mp this).1
  have h1 : ((P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤
      ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    calc ∑ t ∈ P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X), ((1 : ℕ) : ℝ)
        ≤ ∑ t ∈ P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X), X * ∏ i, ((t i : ℝ))⁻¹ := by
          apply Finset.sum_le_sum
          intro t ht
          obtain ⟨htP, hle⟩ := Finset.mem_filter.mp ht
          have hp : (0 : ℝ) < ∏ i, (t i : ℝ) :=
            Finset.prod_pos (fun i _ => by exact_mod_cast hpos t htP i)
          rw [Finset.prod_inv_distrib, Nat.cast_one, ← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
          push_cast at hle; exact hle
      _ ≤ ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro t _ _
          have : (0 : ℝ) ≤ ∏ i, ((t i : ℝ))⁻¹ := Finset.prod_nonneg (fun i _ => by positivity)
          nlinarith
  have h2 : ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ = X * (∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹) ^ n := by
    have := Finset.prod_univ_sum (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)
      (fun (_ : Fin n) (j : ℕ) => ((j : ℝ))⁻¹)
    rw [← Finset.mul_sum, hP, ← this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ ≤ 1 + Real.log X := by
    have := harmonic_floor_le_one_add_log X hX
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have h4 : 0 ≤ ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ := Finset.sum_nonneg (fun j _ => by positivity)
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
