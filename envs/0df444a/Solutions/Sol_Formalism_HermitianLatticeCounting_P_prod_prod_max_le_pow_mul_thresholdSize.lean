-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_prod_max_le_pow_mul_thresholdSize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.0178+00:00
-- url     : https://prove2.me/submissions/983ef9c7-f54c-468c-aa1f-6422e2ce159c

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prodMaxLeProdMaxDiv
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_thresholdSize_eq_prod_comm
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
theorem _root_.solution {ι l : Type} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) (hH : 1 ≤ H₂)
    (hD : ∀ i ∈ E, ∀ v, 0 < D i v) :
    ∏ i ∈ E, ∏ v, max 1 (D i v) ≤ H₂ ^ (Fintype.card ι * E.card) * size E D H₂ := by
  have h1 : ∀ i ∈ E, ∏ v, max 1 (D i v) ≤ H₂ ^ Fintype.card ι * ∏ v, max 1 (D i v / H₂) :=
    fun i hi => prodMaxLeProdMaxDiv ι (D i) H₂ hH (fun v => (hD i hi v).le)
  calc ∏ i ∈ E, ∏ v, max 1 (D i v)
        ≤ ∏ i ∈ E, (H₂ ^ Fintype.card ι * ∏ v, max 1 (D i v / H₂)) :=
        Finset.prod_le_prod (fun i _ => finset_prod_max_one_nonneg _ _) h1
    _ = H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, thresholdSize_eq_prod_comm]
end Formalism.HermitianLatticeCounting.P
