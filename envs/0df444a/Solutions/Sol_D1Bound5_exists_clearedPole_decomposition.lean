-- Prove2me | solution 1 for D1Bound5.exists_clearedPole_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:47.512713+00:00
-- url     : https://prove2.me/submissions/3d94efae-ecc7-4a33-a838-007d8407a875

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Definitions.Def_D1Bound5_BennettPartialFractions_Definitions
import Definitions.Def_D1Bound5_BennettResidueCoefficient_Definitions
import Theorems.Thm_D1Bound5_bennettPoleDenominator_degree
import Theorems.Thm_D1Bound5_bennettPoleDenominator_monic
import Theorems.Thm_D1Bound5_clearedPoleSum_degree_lt_total

section
open Finset Polynomial

namespace D1Bound5

/-!
This module proves existence of the exact cleared partial-fraction decomposition
used by the residue-sum argument. The decomposition is a conclusion, not an
assumption. Identifying its coefficients with the manuscript's explicit finite
binomial sums remains a separate obligation.
-/

section CommRing

variable {R ι : Type*} [CommRing R] [Nontrivial R]
variable [Fintype ι] [DecidableEq ι]













end CommRing

section Field

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 2000000 in
/-- Exact partial-fraction existence at distinct nodes with arbitrary positive
multiplicities. No partial-fraction identity is assumed in this theorem. -/
theorem _root_.solution (a : ι → F) (ha : Function.Injective a)
    (e : ι → ℕ) (f : F[X]) (hdeg : f.degree < (∑ i, (e i + 1) : ℕ)) :
    ∃ c : (i : ι) → Fin (e i + 1) → F,
      f = ∑ i, ∑ j : Fin (e i + 1), C (c i j) * clearedPoleNumerator a e i j := by
  classical
  obtain ⟨q, r, hr, hf⟩ :=
    Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow
      (s := (Finset.univ : Finset ι)) f
      (g := fun i ↦ X - C (a i))
      (fun i _ ↦ Polynomial.monic_X_sub_C (a i))
      (fun i _ j _ hij ↦ Polynomial.pairwise_coprime_X_sub_C ha hij)
      (fun i ↦ e i + 1)
  have hconst (i : ι) (j : Fin (e i + 1)) : r i j = C ((r i j).coeff 0) := by
    by_cases hzero : r i j = 0
    · simp [hzero]
    apply Polynomial.eq_C_of_natDegree_le_zero
    have hd : (r i j).degree < (1 : ℕ) := by
      simpa using hr i (Finset.mem_univ i) j
    have hn := (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hd
    omega
  let c : (i : ι) → Fin (e i + 1) → F := fun i j ↦ (r i j).coeff 0
  have heq : f = q * bennettPoleDenominator a e +
      ∑ i, ∑ j : Fin (e i + 1), C (c i j) * clearedPoleNumerator a e i j := by
    rw [hf]
    apply congrArg (fun z : F[X] ↦ q * bennettPoleDenominator a e + z)
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hconst i j]
    simp only [c, clearedPoleNumerator, mul_assoc]
  let rem : F[X] := ∑ i, ∑ j : Fin (e i + 1),
    C (c i j) * clearedPoleNumerator a e i j
  have hrem : rem.degree < (bennettPoleDenominator a e).degree := by
    rw [bennettPoleDenominator_degree]
    exact clearedPoleSum_degree_lt_total a e c
  have hdiv : f /ₘ bennettPoleDenominator a e = q :=
    (Polynomial.div_modByMonic_unique q rem (bennettPoleDenominator_monic a e)
      ⟨by simpa only [rem, mul_comm, add_comm] using heq.symm, hrem⟩).1
  have hdivzero : f /ₘ bennettPoleDenominator a e = 0 := by
    apply (Polynomial.divByMonic_eq_zero_iff (bennettPoleDenominator_monic a e)).mpr
    rwa [bennettPoleDenominator_degree]
  have hq : q = 0 := hdiv.symm.trans hdivzero
  exact ⟨c, by simpa only [hq, zero_mul, zero_add] using heq⟩



end Field

end D1Bound5
end
