-- Prove2me | solution 1 for Formalism.HC.Der.Rd.absNorm_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:09.78614+00:00
-- url     : https://prove2.me/submissions/fcdc7d91-868e-4a8d-a1a7-09e338698522

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Theorems.Thm_Formalism_HC_Der_Rd_adjoin_top
import Theorems.Thm_Formalism_HC_Der_Rd_minpoly_map

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
open Classical
namespace Formalism.HC.Der.Rd
theorem _root_.solution : ((Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L)) : ℕ) : ℝ) =
    ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hζL : algebraMap (𝓞 L) L hζ.toInteger = ζ := hζ.coe_toInteger
  have hadjZ : Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 L)) = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  generalize hζ.toInteger = z at hζL hadjZ
  have hadj : Algebra.adjoin (𝓞 E) ({z} : Set (𝓞 L)) = ⊤ := by
    refine eq_top_iff.2 fun x hxt => ?_
    clear hxt
    have hx : x ∈ Algebra.adjoin ℤ ({z} : Set (𝓞 L)) := by rw [hadjZ]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 E) (𝓞 L)]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hK : Algebra.adjoin E {algebraMap (𝓞 L) L z} = ⊤ := by
    rw [hζL]; exact adjoin_top hζ E
  have hD := conductor_mul_differentIdeal (𝓞 E) E L z hK
  have hc : conductor (𝓞 E) z = ⊤ := by
    first
    | exact conductor_eq_top_of_adjoin_eq_top hadj
    | exact conductor_eq_top_of_adjoin_eq_top _ hadj
    | exact conductor_eq_top_of_adjoin_eq_top (𝓞 E) hadj
  rw [hc, Ideal.top_mul] at hD
  have hint_r : IsIntegral (𝓞 E) ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hminE : minpoly E ζ = (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) E) := by
    rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 L) L) z, hζL]
    first
    | exact minpoly.isIntegrallyClosed_eq_field_fractions' E hint_r
    | exact minpoly.isIntegrallyClosed_eq_field_fractions' (K := E) hint_r
  have hmapL : (minpoly (𝓞 E) z).map (algebraMap (𝓞 E) L) =
      Lagrange.nodal Finset.univ (fun σ : L ≃ₐ[E] L => σ ζ) := by
    rw [← minpoly_map hζ E, hminE, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hy : algebraMap (𝓞 L) L (aeval z (derivative (minpoly (𝓞 E) z))) =
      ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ) := by
    rw [← aeval_algebraMap_apply, hζL, aeval_def, eval₂_eq_eval_map, ← derivative_map, hmapL]
    have h1 := Lagrange.eval_nodal_derivative_eval_node_eq (s := (Finset.univ : Finset (L ≃ₐ[E] L)))
      (v := fun σ : L ≃ₐ[E] L => σ ζ) (Finset.mem_univ 1)
    rw [Lagrange.eval_nodal] at h1
    exact h1
  have hnormR : ((Algebra.norm ℤ (aeval z (derivative (minpoly (𝓞 E) z))) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[E] L)).erase 1, (ζ - σ ζ)) : ℚ) : ℝ) := by
    rw [← hy, ← Algebra.coe_norm_int]; norm_cast
  rw [hD, Ideal.absNorm_span_singleton]
  simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [hnormR, map_prod, Rat.cast_prod,
    Finset.abs_prod]
end Formalism.HC.Der.Rd
