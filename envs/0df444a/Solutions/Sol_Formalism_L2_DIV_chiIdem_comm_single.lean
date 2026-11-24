-- Prove2me | solution 1 for Formalism.L2.DIV.chiIdem_comm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:30.590774+00:00
-- url     : https://prove2.me/submissions/8f91cde5-d341-415d-ac5c-da1811c7b812

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_coeff_mul_fin
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
theorem _root_.solution {χ : G → K} (h : ∀ s t : G, χ (s * t * s⁻¹) = χ t) (s : G) (x : K) :
    MonoidAlgebra.single s x * chiIdem χ = chiIdem χ * MonoidAlgebra.single s x := by
  classical
  ext u
  rw [coeff_mul_fin, coeff_mul_fin, Finset.sum_eq_single s, Finset.sum_eq_single (u * s⁻¹)]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same, show (u * s⁻¹)⁻¹ * u = s by group,
      Finsupp.single_eq_same, coeff_chiIdem_lemma, coeff_chiIdem_lemma, show (s⁻¹ * u)⁻¹ = u⁻¹ * s by group,
      show (u * s⁻¹)⁻¹ = s * u⁻¹ by group]
    have hc : χ (u⁻¹ * s) = χ (s * u⁻¹) := by
      rw [← h s (u⁻¹ * s)]
      congr 1
      group
    rw [hc]
    ring
  · intro v _ hv
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg, mul_zero]
    intro e
    apply hv
    rw [e]
    group
  · intro hn
    exact absurd (Finset.mem_univ _) hn
  · intro v _ hv
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hv), zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end Formalism.L2.DIV
