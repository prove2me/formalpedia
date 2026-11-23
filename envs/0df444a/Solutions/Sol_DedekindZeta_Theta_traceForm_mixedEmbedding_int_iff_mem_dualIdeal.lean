-- Prove2me | solution 1 for DedekindZeta.Theta.traceForm_mixedEmbedding_int_iff_mem_dualIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:24.111835+00:00
-- url     : https://prove2.me/submissions/a04323e2-845f-4759-9ae8-f71838b625a2

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_dualIdeal_eq_dual
import Theorems.Thm_DedekindZeta_Theta_traceForm_mixedEmbedding

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (b : K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        traceForm K (mixedEmbedding K b) a = (k : ℝ)) ↔
      b ∈ (dualIdeal K 𝔞 : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.mem_coe, ← dualIdeal_eq_dual K 𝔞,
    FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hne)]
  refine forall₂_congr fun a ha => ?_
  rw [traceForm_mixedEmbedding, Algebra.traceForm_apply, RingHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply FaithfulSMul.algebraMap_injective ℚ ℝ
    rw [hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp
end DedekindZeta.Theta
