-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.finset_prod_le_prod_of_subset_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:47.376247+00:00
-- url     : https://prove2.me/submissions/ba855652-ca8a-47bb-a922-6b60dec24cef

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
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
private theorem one_le_finset_prod_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := by
  calc (1:ℝ) = ∏ v ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ v ∈ s, y v := Finset.prod_le_prod (fun _ _ => zero_le_one) h
private theorem finset_prod_real_mono_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := by
  classical
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ v ∈ t \ s, y v :=
    one_le_finset_prod_of_forall_one_le _ _ (fun v hv => h v (Finset.mem_sdiff.mp hv).1)
  have h2 : 0 ≤ ∏ v ∈ s, y v :=
    Finset.prod_nonneg (fun v hv => zero_le_one.trans (h v (hst hv)))
  exact le_mul_of_one_le_left h2 h1
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := finset_prod_real_mono_of_subset_of_one_le s t hst y h
end Formalism.HermitianLatticeCounting.P
