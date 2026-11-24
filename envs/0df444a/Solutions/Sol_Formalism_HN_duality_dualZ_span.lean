-- Prove2me | solution 1 for Formalism.HN.duality_dualZ_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:24.851926+00:00
-- url     : https://prove2.me/submissions/467f68cf-e509-4d85-898d-b273ff2839a6

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_mem_dualZ
import Theorems.Thm_Formalism_HN_duality_expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section Dual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem exists_int_inner_of_mem_span_int (v : ι → E) (y : E)
    (hy : ∀ k, ∃ n : ℤ, (n : ℝ) = inner ℝ (v k) y) {x : E} (hx : x ∈ span ℤ (Set.range v)) :
    ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hy k
  | zero => exact ⟨0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [inner_add_left, ← ha, ← hb, Int.cast_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * b, ?_⟩
    have hsm : a • x = (a : ℝ) • x := by
      exact (Int.cast_smul_eq_zsmul (R := ℝ) a x).symm
    rw [hsm, real_inner_smul_left, ← hb, Int.cast_mul]
variable [FiniteDimensional ℝ E]
end Dual
universe u
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HN
theorem _root_.solution (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) :
    dualZ (span ℤ (Set.range v)) = span ℤ (Set.range w) := by
  have hspan : span ℝ ((span ℤ (Set.range v) : Submodule ℤ E) : Set E) = span ℝ (Set.range v) := by
    exact Submodule.span_span_of_tower ℤ ℝ (Set.range v)
  apply le_antisymm
  · intro y hy
    rw [duality_mem_dualZ, hspan] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [duality_expand v w hw hvw hy1]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨n, hn⟩ := hy2 (v k) (Submodule.subset_span (Set.mem_range_self k))
    have hsm : inner ℝ (v k) y • w k = n • w k := by
      rw [← hn]
      exact Int.cast_smul_eq_zsmul (R := ℝ) n (w k)
    rw [hsm]
    exact Submodule.smul_mem _ n (Submodule.subset_span (Set.mem_range_self k))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, duality_mem_dualZ, hspan]
    refine ⟨hw i, fun x hx => exists_int_inner_of_mem_span_int v (w i) (fun k => ?_) hx⟩
    refine ⟨if k = i then 1 else 0, ?_⟩
    rw [hvw]
    split_ifs <;> simp
end Formalism.HN
