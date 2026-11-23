-- Prove2me | solution 1 for Formalism.L2.DIV.coeff_mul_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:37.359012+00:00
-- url     : https://prove2.me/submissions/0af0832c-5e3a-448e-9401-2f2e3526b67d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section Sub
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
end Sub
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
section Basic
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
private theorem coeff_sum_lemma {K G ι : Type} [Field K] (s : Finset ι) (f : ι → MonoidAlgebra K G)
    (u : G) : (∑ i ∈ s, f i).coeff u = ∑ i ∈ s, (f i).coeff u := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]
private theorem eq_sum_single_lemma {K G : Type} [Field K] [Fintype G] (a : MonoidAlgebra K G) :
    a = ∑ t : G, MonoidAlgebra.single t (a.coeff t) := by
  classical
  ext u
  rw [coeff_sum_lemma, Finset.sum_eq_single u]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro t _ ht
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg ht]
  · intro h
    exact absurd (Finset.mem_univ u) h
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
section Chars
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Chars
section Conj
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Conj
section Assemble
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
end Assemble
section Schur
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Schur
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
end Formalism.L2.DIV.Test
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution (a b : MonoidAlgebra K G) (u : G) :
    (a * b).coeff u = ∑ s : G, a.coeff s * b.coeff (s⁻¹ * u) := by
  classical
  conv_lhs => rw [eq_sum_single_lemma a, eq_sum_single_lemma b]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [coeff_sum_lemma]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_sum_lemma, Finset.sum_eq_single (s⁻¹ * u)]
  · rw [MonoidAlgebra.single_mul_single, mul_inv_cancel_left, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
  · intro t _ ht
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    intro h
    apply ht
    rw [← h, inv_mul_cancel_left]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.L2.DIV
