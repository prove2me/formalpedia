-- Prove2me | solution 1 for Formalism.HC.Der.Rd.minpoly_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:20.297026+00:00
-- url     : https://prove2.me/submissions/0976632a-686b-4010-9037-8aada3ea55b0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Theorems.Thm_Formalism_HC_Der_Rd_adjoin_top
import Theorems.Thm_Formalism_HC_Der_Rd_gal_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
namespace Formalism.HC.Der.Rd
theorem _root_.solution : (minpoly E ζ).map (algebraMap E L) = Lagrange.nodal Finset.univ fun σ : L ≃ₐ[E] L => σ ζ := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hint_r : IsIntegral E ζ := .of_finite E ζ
  have htop : E⟮ζ⟯ = ⊤ := by
    rw [eq_top_iff]; intro x _
    have hx : x ∈ Algebra.adjoin E ({ζ} : Set L) := by
      rw [adjoin_top hζ E]; exact Algebra.mem_top
    first
    | exact IntermediateField.algebra_adjoin_le_adjoin E ({ζ} : Set L) hx
    | exact IntermediateField.algebra_adjoin_le_adjoin (F := E) (S := ({ζ} : Set L)) hx
  have hcard : Fintype.card (L ≃ₐ[E] L) = Module.finrank E L := by
    rw [← IsGalois.card_aut_eq_finrank E L, Nat.card_eq_fintype_card]
  have hinj := gal_inj hζ E
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic
  · exact (minpoly.monic hint_r).map _
  · unfold Lagrange.nodal
    refine Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C hinj).set_pairwise _)
      fun σ _ => ?_
    rw [Polynomial.dvd_iff_isRoot, IsRoot.def, eval_map, ← aeval_def]
    have := Polynomial.aeval_algHom_apply (σ : L →ₐ[E] L) ζ (minpoly E ζ)
    rw [minpoly.aeval, _root_.map_zero] at this
    exact this
  · refine le_of_eq ?_
    rw [natDegree_map, ← IntermediateField.adjoin.finrank hint_r, htop, IntermediateField.finrank_top',
      Lagrange.natDegree_nodal, Finset.card_univ, hcard]
end Formalism.HC.Der.Rd
