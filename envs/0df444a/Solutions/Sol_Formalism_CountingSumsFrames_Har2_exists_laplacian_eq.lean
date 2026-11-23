-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.exists_laplacian_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:37.994703+00:00
-- url     : https://prove2.me/submissions/19a6b22b-ac5f-4ee1-98dd-a34e782038b4

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_pow_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h_pow_har
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_decomp_exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero {A B : ℕ} {f : PolXY K k} :
    f ∈ HarAB K k A B ↔ f ∈ PolAB K k A B ∧ ctrF K k f = 0 := Iff.rfl
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {g : PolXY K k} (hg : g ∈ PolAB K k A B) :
    ∃ f ∈ PolAB K k (A + 1) (B + 1), ctrF K k f = g := by
  obtain ⟨w, hw, hgw⟩ := decomp_exists hk A B g hg
  have h1 := min_le_left A B
  have h2 := min_le_right A B
  refine ⟨∑ j ∈ range (min A B + 1),
    ((((j + 1) * (A - j + (B - j) + k + j) : ℕ) : K)⁻¹) • (hXY K k ^ (j + 1) * w j), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    have hj' := Finset.mem_range.1 hj
    have := h_pow_mul_mem (j + 1) (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 (hw j)).1
    rwa [show A - j + (j + 1) = A + 1 by omega, show B - j + (j + 1) = B + 1 by omega] at this
  · rw [map_sum, hgw]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, ctr_h_pow_har j (hw j), smul_smul, inv_mul_cancel₀, one_smul]
    exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero j) (by omega))
end Formalism.CountingSumsFrames.Har2
