-- Prove2me | solution 1 for Formalism.HC.Der.Rd.log_rd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:33.132851+00:00
-- url     : https://prove2.me/submissions/0bfd5a5a-22ba-400a-9650-43e14cbf029a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Theorems.Thm_Formalism_HC_Der_Rd_gal_inj
import Theorems.Thm_Formalism_HC_Der_Rd_log_discr_sub
import Theorems.Thm_Formalism_HC_Der_Rd_log_norm_weight

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
theorem _root_.solution (U : Subgroup (ZMod N)ˣ)
    (hU : ∀ (σ : L ≃ₐ[ℚ] L) (u : (ZMod N)ˣ), σ ζ = ζ ^ (u : ZMod N).val →
      ((∀ x : E, σ (algebraMap E L x) = algebraMap E L x) ↔ u ∈ U)) :
    Real.log |(discr E : ℝ)| / Module.finrank ℚ E =
      ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have hφ : Module.finrank ℚ L = N.totient :=
    IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (NeZero.pos N))
  have hcard : Fintype.card (L ≃ₐ[ℚ] L) = Fintype.card (ZMod N)ˣ := by
    rw [ZMod.card_units_eq_totient, ← hφ, ← IsGalois.card_aut_eq_finrank ℚ L, Nat.card_eq_fintype_card]
  have hinj : Function.Injective (hζ.autToPow ℚ) := by
    intro a b h
    apply gal_inj hζ ℚ
    show a ζ = b ζ
    rw [← hζ.autToPow_spec ℚ a, ← hζ.autToPow_spec ℚ b, h]
  have hbij : Function.Bijective (hζ.autToPow ℚ) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩
  have hsum : ∑ σ ∈ (Finset.univ : Finset (L ≃ₐ[ℚ] L)).filter
        (fun σ => ¬ ∀ x : E, σ (algebraMap E L x) = algebraMap E L x),
        Real.log |((Algebra.norm ℚ (ζ - σ ζ) : ℚ) : ℝ)| =
      (N.totient : ℝ) * ∑ u ∈ (Finset.univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_equiv (Equiv.ofBijective _ hbij) ?_ ?_
    · intro σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.ofBijective_apply]
      rw [hU σ _ (hζ.autToPow_spec ℚ σ).symm]
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have hu : hζ.autToPow ℚ σ ∉ U := by rwa [← hU σ _ (hζ.autToPow_spec ℚ σ).symm]
      have hu1 : ((hζ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N) ≠ 1 := by
        intro h; apply hu; rw [Units.val_eq_one.1 h]; exact U.one_mem
      simp only [Equiv.ofBijective_apply]
      rw [← hζ.autToPow_spec ℚ σ, log_norm_weight hζ _ hu1]
  have key := log_discr_sub hζ E
  rw [hsum] at key
  have hEQ : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hLE : (0 : ℝ) < Module.finrank E L := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ E : ℝ) * Module.finrank E L = N.totient := by
    rw [← Nat.cast_mul, Module.finrank_mul_finrank ℚ E L, hφ]
  rw [div_eq_iff hEQ.ne']
  apply mul_left_cancel₀ hLE.ne'
  rw [key, ← htow]; ring
end Formalism.HC.Der.Rd
