-- Prove2me | solution 1 for Formalism.L2.DIV.idemOf_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:39.937796+00:00
-- url     : https://prove2.me/submissions/5600e044-4452-4c7d-a0ac-b85d286e90a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_isIntegral
import Theorems.Thm_Formalism_L2_DIV_coeff_idemOf
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
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
private theorem int_iff_lemma {K : Type} [Field K] [NumberField K] (x : K) :
    (∃ b : 𝓞 K, (b : K) = x) ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨b, rfl⟩
    first
    | exact NumberField.RingOfIntegers.isIntegral_coe b
    | exact b.2
    | exact (mem_integralClosure_iff ℤ K).mp b.2
  · intro h
    first
    | exact ⟨⟨x, h⟩, rfl⟩
    | exact ⟨⟨x, (mem_integralClosure_iff ℤ K).mpr h⟩, rfl⟩
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (t : G) :
    ∃ b : 𝓞 K, (b : K) = (Fintype.card G : K) * (idemOf X).coeff t := by
  have hn : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [int_iff_lemma, coeff_idemOf, Finset.mul_sum]
  have key : ∀ χ ∈ X, IsIntegral ℤ ((Fintype.card G : K) * (χ 1 / (Fintype.card G : K) * χ t⁻¹)) := by
    intro χ hχ
    have e : (Fintype.card G : K) * (χ 1 / (Fintype.card G : K) * χ t⁻¹) = χ 1 * χ t⁻¹ := by
      field_simp
    rw [e]
    exact ((hX χ hχ).isIntegral 1).mul ((hX χ hχ).isIntegral t⁻¹)
  first
  | exact IsIntegral.sum _ key
  | exact IsIntegral.sum key
  | exact (integralClosure ℤ K).sum_mem key
end Formalism.L2.DIV
