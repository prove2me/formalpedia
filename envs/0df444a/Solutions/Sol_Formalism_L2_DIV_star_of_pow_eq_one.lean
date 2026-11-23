-- Prove2me | solution 1 for Formalism.L2.DIV.star_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:29.431791+00:00
-- url     : https://prove2.me/submissions/01a93030-eb5a-4345-b269-f5fee5f4b4c7

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
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem conj_eq_inv_lemma {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) :
    starRingEnd ℂ z = z⁻¹ := by
  have hnorm : ‖z‖ = 1 := by
    first
    | exact norm_eq_one_of_pow_eq_one h hn
    | exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hz : starRingEnd ℂ z * z = 1 := by
    first
    | (rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp)
    | (rw [mul_comm, Complex.mul_conj, hnorm]; simp)
    | (rw [Complex.conj_mul', hnorm]; simp)
  exact eq_inv_of_mul_eq_one_left hz
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution {v0 : InfinitePlace K} (hv : IsConjAt v0) {u : K} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : star u = u⁻¹ := by
  apply v0.embedding.injective
  rw [hv u, map_inv₀]
  exact conj_eq_inv_lemma hn (by rw [← map_pow, hu, map_one])
end Formalism.L2.DIV
