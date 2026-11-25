-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.double_coset_decomposition_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:13.736373+00:00
-- url     : https://prove2.me/submissions/2f650afd-76ed-4204-bdfc-ee66b76d1b53

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_down_up_composition_formula
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mem_image_line
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmP_eq_nmV
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmV_eq_image
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_opU_eq_opD
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_up_down_composition_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.OneDimInversion
open Finset Formalism.LogVandermondeBounds.product_first_zeroth_parts
section T1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {R : Type} [CommRing R]
private lemma ext_fin_one_function {x y : Fin 1 → F} (h : x 0 = y 0) : x = y := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact h
private lemma nonzero_single_coordinate {f : Fin 1 → F} (hf : f ≠ 0) : f 0 ≠ 0 := by
  intro h
  apply hf
  exact ext_fin_one_function (by simpa using h)
private lemma filt1 (f : Fin 1 → F) (hf : f ≠ 0) :
    univ.filter (fun x : Fin 1 → F => pair f x = 1) = {fun _ => (f 0)⁻¹} := by
  have h0 := nonzero_single_coordinate hf
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton, pair, Fin.sum_univ_one]
  constructor
  · intro h
    exact ext_fin_one_function (eq_inv_of_mul_eq_one_right h)
  · intro h
    rw [h]
    exact mul_inv_cancel₀ h0
private lemma inversion_operator_one_dim (ψ : (Fin 1 → F) → R) (f : Fin 1 → F) (hf : f ≠ 0) :
    opU ψ f = ψ (fun _ => (f 0)⁻¹) := by
  unfold opU
  rw [filt1 f hf, sum_singleton]
private lemma inversion_operator_involutive (ψ : (Fin 1 → F) → R) (x : Fin 1 → F) (hx : x ≠ 0) :
    opU (opU ψ) x = ψ x := by
  have h0 := nonzero_single_coordinate hx
  have hne : (fun _ : Fin 1 => (x 0)⁻¹) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp only [Pi.zero_apply] at this
    exact h0 (inv_eq_zero.1 this)
  rw [inversion_operator_one_dim _ x hx, inversion_operator_one_dim _ _ hne]
  congr 1
  exact ext_fin_one_function (by simp)
private lemma nm1 (ψ : (Fin 1 → F) → R) (x : Fin 1 → F) (hx : x ≠ 0) :
    nmV ψ x = trV ψ := by
  have h0 := nonzero_single_coordinate hx
  rw [nmV_eq_image ψ hx]
  unfold trV
  congr 1
  ext y
  rw [mem_image_line hx, mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro hy
    refine ⟨hy, y 0 / x 0, ext_fin_one_function ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
end T1
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
section Orb
end Orb
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
theorem _root_.solution : TraceOperatorIdentityAllRanks := by
  intro F _ _ _ r R _ hr
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨fun ψ x hx => ?_, fun φ f hf => ?_⟩
    · rw [← opU_eq_opD (opU ψ), inversion_operator_involutive ψ x hx, nm1 ψ x hx]
      simp
    · have htr : trP φ = trV φ := rfl
      rw [← opU_eq_opD φ, inversion_operator_involutive φ f hf, nmP_eq_nmV, nm1 φ f hf, htr]
      simp
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hr2 : 2 ≤ k + 1 + 1 := by omega
    have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : k + 1 + 1 - 2 = k := by omega
    refine ⟨fun ψ x hx => ?_, fun φ f hf => ?_⟩
    · rw [down_up_composition_formula F (k + 1 + 1) R hr2 ψ x hx, e1, e2]
      ring
    · rw [up_down_composition_formula F (k + 1 + 1) R hr2 φ f hf, e1, e2]
      ring
end Formalism.HermitianLattices.RamifiedLatticeOperators
