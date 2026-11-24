-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodMaxMulMaxInvLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:15.066801+00:00
-- url     : https://prove2.me/submissions/91f58679-82f9-4776-a73d-f94f9bac1ff7

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prodMaxInvLeSq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_prod_max_le_pow_mul_thresholdSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem finset_prod_max_one_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    0 ≤ ∏ v ∈ s, max 1 (y v) :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PiProd := by
  intro ι l _ E D H₂ hH hD hprod
  rw [Finset.prod_comm]
  have h1 : ∀ i ∈ E, ∏ v, (max 1 (D i v) * max 1 (1 / D i v)) ≤ (∏ v, max 1 (D i v)) ^ 2 := by
    intro i hi
    rw [Finset.prod_mul_distrib, sq]
    exact mul_le_mul_of_nonneg_left (prodMaxInvLeSq ι (D i) Finset.univ (hD i hi) (hprod i hi)).2
      (finset_prod_max_one_nonneg _ _)
  have hH0 : 0 ≤ H₂ := by linarith
  calc ∏ i ∈ E, ∏ v, (max 1 (D i v) * max 1 (1 / D i v))
        ≤ ∏ i ∈ E, (∏ v, max 1 (D i v)) ^ 2 :=
        Finset.prod_le_prod (fun i _ => Finset.prod_nonneg (fun v _ => mul_nonneg
          (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _)))) h1
    _ = (∏ i ∈ E, ∏ v, max 1 (D i v)) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 2 :=
        pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _ => finset_prod_max_one_nonneg _ _))
          (prod_prod_max_le_pow_mul_thresholdSize E D H₂ hH hD) 2
    _ = H₂ ^ (2 * Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ ^ 2 := by ring
end Formalism.HermitianLatticeCounting.P
