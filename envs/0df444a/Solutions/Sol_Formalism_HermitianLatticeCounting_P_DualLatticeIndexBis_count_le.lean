-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.count_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.290675+00:00
-- url     : https://prove2.me/submissions/a454a28b-081f-4c26-87f6-2ad9671b74ae

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_SLP_P_CountO_ncard_biUnion_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution (E : Type) [Field E] [NumberField E] (N k y : ℕ) (hN : 1 ≤ N)
    (hOm : Formalism.SLP.OmegaPow)
    (h : ∀ n, 1 ≤ n → {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.Finite ∧
      {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤ N ^ (Nat.primeFactorsList n).length * n ^ k) :
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + ((k : ℝ) + Real.logb 2 N)) := by
  classical
  have hset : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y} =
      ⋃ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
    ext I; simp
  obtain ⟨hfin, hcard⟩ := Formalism.SLP.P.CountO.ncard_biUnion_le (Finset.Icc 1 y)
    (fun n => {I : Ideal (𝓞 E) | Ideal.absNorm I = n})
    (fun n hn => (h n (Finset.mem_Icc.mp hn).1).1)
  rw [hset]
  refine ⟨hfin, ?_⟩
  have hlog : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one]
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.ncard_empty, Nat.cast_zero]
    exact Real.rpow_nonneg le_rfl _
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  calc (((⋃ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n}).ncard : ℕ) : ℝ)
      ≤ ((∑ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ∑ n ∈ Finset.Icc 1 y, (({I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ _n ∈ Finset.Icc 1 y, (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
        have h3 := (h n h1).2
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hny : (n : ℝ) ≤ y := by exact_mod_cast h2
        calc (({I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ)
            ≤ ((N ^ (Nat.primeFactorsList n).length * n ^ k : ℕ) : ℝ) := by exact_mod_cast h3
          _ = (N : ℝ) ^ (Nat.primeFactorsList n).length * (n : ℝ) ^ k := by push_cast; ring
          _ ≤ (n : ℝ) ^ Real.logb 2 N * (n : ℝ) ^ k := by
              gcongr; exact hOm N n hN h1
          _ ≤ (y : ℝ) ^ Real.logb 2 N * (y : ℝ) ^ k := by
              gcongr
          _ = (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by
              rw [Real.rpow_add hy', Real.rpow_natCast]; ring
    _ = (y : ℝ) * (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by simp
    _ = (y : ℝ) ^ (1 + ((k : ℝ) + Real.logb 2 N)) := by
        rw [Real.rpow_add hy' 1, Real.rpow_one]
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
