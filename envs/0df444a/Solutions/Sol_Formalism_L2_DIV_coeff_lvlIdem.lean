-- Prove2me | solution 1 for Formalism.L2.DIV.coeff_lvlIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:27.283719+00:00
-- url     : https://prove2.me/submissions/f32e7d2f-ea8d-4c61-9e16-341993d23607

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
theorem _root_.solution (P : Subgroup G) (ψ : P →* Kˣ) (t : G) :
    (∃ h : P, (h : G) = t ∧ (lvlIdem P ψ).coeff t = (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) ∨
      (lvlIdem P ψ).coeff t = 0 := by
  classical
  unfold lvlIdem
  rw [coeff_sum_lemma]
  by_cases ht : t ∈ P
  · left
    refine ⟨⟨t, ht⟩, rfl, ?_⟩
    rw [Finset.sum_eq_single ⟨t, ht⟩]
    · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    · intro k _ hk
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
      intro h
      exact hk (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · right
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    intro h
    exact ht (h ▸ k.2)
end Formalism.L2.DIV
