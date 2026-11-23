-- Prove2me | solution 1 for Formalism.L2.DIV.coeff_chiIdem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:40.345645+00:00
-- url     : https://prove2.me/submissions/eaa5e74d-fda2-411c-ad17-987ff3d6dcf0

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
private theorem coeff_chiIdem_lemma {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (χ : G → K) (t : G) :
    (chiIdem χ).coeff t = χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  classical
  unfold chiIdem
  rw [coeff_sum_lemma, Finset.sum_eq_single t]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro u _ hu
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hu]
  · intro h
    exact absurd (Finset.mem_univ _) h
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
theorem _root_.solution (χ : G → K) (t : G) :
    (chiIdem χ).coeff t = χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  exact coeff_chiIdem_lemma χ t
end Formalism.L2.DIV
