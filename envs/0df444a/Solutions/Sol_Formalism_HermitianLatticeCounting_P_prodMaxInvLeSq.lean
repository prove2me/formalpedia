-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:44.674444+00:00
-- url     : https://prove2.me/submissions/9a0fa414-1072-441e-9a38-3c7a1f52b60b

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
private theorem finset_prod_max_one_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    0 ≤ ∏ v ∈ s, max 1 (y v) :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
private theorem max_self_inv_le_max_one_mul_max_one_inv {x : ℝ} (hx : 0 < x) :
    max x (1 / x) ≤ max 1 x * max 1 (1 / x) := by
  have h0 : 0 ≤ max 1 (1 / x) := zero_le_one.trans (le_max_left _ _)
  apply max_le
  · calc x ≤ max 1 x := le_max_right _ _
      _ = max 1 x * 1 := (mul_one _).symm
      _ ≤ max 1 x * max 1 (1 / x) := mul_le_mul_of_nonneg_left (le_max_left _ _)
          (zero_le_one.trans (le_max_left _ _))
  · exact (le_max_right 1 (1 / x)).trans (le_mul_of_one_le_left h0 (le_max_left _ _))
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LemmaP := by
  intro ι _ x Sg hx hprod
  have hA : ∏ v, max 1 (1 / x v) ≤ ∏ v, max 1 (x v) := by
    have e : ∏ v, max 1 (x v) = (∏ v, x v) * ∏ v, max 1 (1 / x v) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v _
      rw [mul_max_of_nonneg _ _ (hx v).le, mul_one, mul_one_div_cancel (hx v).ne']
      exact max_comm _ _
    rw [e]
    exact le_mul_of_one_le_left (finset_prod_max_one_nonneg _ _) hprod
  have hB : ∏ v ∈ Sg, max 1 (1 / x v) ≤ ∏ v, max 1 (1 / x v) :=
    finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => le_max_left _ _)
  refine ⟨?_, hB.trans hA⟩
  calc ∏ v ∈ Sg, max (x v) (1 / x v) ≤ ∏ v ∈ Sg, (max 1 (x v) * max 1 (1 / x v)) :=
        Finset.prod_le_prod (fun v _ => (hx v).le.trans (le_max_left _ _))
          (fun v _ => max_self_inv_le_max_one_mul_max_one_inv (hx v))
    _ = (∏ v ∈ Sg, max 1 (x v)) * ∏ v ∈ Sg, max 1 (1 / x v) := Finset.prod_mul_distrib
    _ ≤ (∏ v, max 1 (x v)) * ∏ v, max 1 (x v) :=
        mul_le_mul (finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => le_max_left _ _))
          (hB.trans hA) (finset_prod_max_one_nonneg _ _) (finset_prod_max_one_nonneg _ _)
    _ = (∏ v, max 1 (x v)) ^ 2 := (sq _).symm
end Formalism.HermitianLatticeCounting.P
