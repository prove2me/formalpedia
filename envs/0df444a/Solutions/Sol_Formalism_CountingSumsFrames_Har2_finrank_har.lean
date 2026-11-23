-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.finrank_har
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:05.702489+00:00
-- url     : https://prove2.me/submissions/919cd52e-af23-494e-a744-49de15357405

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_exists_laplacian_eq
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_finite_polAB
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
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution [CharZero K] (k' A B : ℕ) :
    Module.finrank K (HarAB K (k' + 1) (A + 1) (B + 1)) + Module.finrank K (PolAB K (k' + 1) A B) =
      Module.finrank K (PolAB K (k' + 1) (A + 1) (B + 1)) := by
  have hk1 : (1 : ℕ) ≤ k' + 1 := by omega
  haveI := finite_polAB (K := K) k' (A + 1) (B + 1)
  have hmaps : ∀ x ∈ PolAB K (k' + 1) (A + 1) (B + 1), ctrF K (k' + 1) x ∈ PolAB K (k' + 1) A B :=
    fun x hx => by simpa using ctrF_mem hx
  let φ := (ctrF K (k' + 1)).restrict hmaps
  have hsurj : LinearMap.range φ = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ?_
    obtain ⟨f, hf, hfy⟩ := exists_laplacian_eq hk1 y.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  have hker : (LinearMap.ker φ).map (PolAB K (k' + 1) (A + 1) (B + 1)).subtype =
      HarAB K (k' + 1) (A + 1) (B + 1) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.2 ⟨y.2, congrArg Subtype.val hy⟩
    · intro hx
      obtain ⟨h1, h2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hx
      exact ⟨⟨x, h1⟩, Subtype.ext h2, rfl⟩
  have := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, ← Submodule.finrank_map_subtype_eq, hker] at this
  omega
end Formalism.CountingSumsFrames.Har2
