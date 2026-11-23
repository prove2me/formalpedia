-- Prove2me | solution 1 for DedekindZeta.Theta.dual_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:11.762961+00:00
-- url     : https://prove2.me/submissions/f7182cb4-988c-43e5-b52e-adbf4d84f64d

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_P2M_DedekindZeta_Theta_inner_eEmb__eq_traceForm_conjMixed_b285258bd3d8
import Theorems.Thm_DedekindZeta_Theta_forall_inner_int_iff_gens
import Theorems.Thm_P2M_DedekindZeta_Theta_traceForm_int_iff_eEmb__mem_dualLattice_db62551e6e8f

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (y : minkowskiSpace K) :
    (∀ x ∈ idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        (inner ℝ y x : ℝ) = k) ↔
      conjMink K y ∈ idealLattice K (dualIdeal K 𝔞) := by
  -- Write `y = eEmbℝ ξ` with `ξ = eEmbℝ⁻¹ y`.
  set ξ := (eEmbℝ K).symm y with hξ
  have hy : y = eEmbℝ K ξ := by rw [hξ, ContinuousLinearEquiv.apply_symm_apply]
  -- The conjugate `conjMink y` is `eEmbℝ (conjMixed ξ)`.
  have hconj : conjMink K y = eEmbℝ K (conjMixed K ξ) := by
    rw [conjMink_apply, ← hξ]
  -- Reduce the lattice quantifier to generators, then identify with the dual lattice.
  rw [forall_inner_int_iff_gens, hconj,
    ← traceForm_int_iff_eEmbℝ_mem_dualLattice K 𝔞 hne]
  -- Bridge each generator condition: `⟪y, eEmb a⟫ = T(conjMixed ξ, a)`.
  refine forall_congr' fun a => ?_
  rw [FractionalIdeal.mem_coe]
  refine imp_congr_right fun _ => ?_
  rw [hy, inner_eEmbℝ_eq_traceForm_conjMixed]
end DedekindZeta.Theta
