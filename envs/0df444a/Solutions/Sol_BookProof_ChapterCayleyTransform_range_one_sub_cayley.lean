-- Prove2me | solution 1 for BookProof.ChapterCayleyTransform.range_one_sub_cayley
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:05:13.898591+00:00
-- url     : https://prove2.me/submissions/f0888d5c-4a4c-4833-ac8a-ddd60ea2adae

-- Generated from ChapterCayleyTransform.lean — solution of BookProof.ChapterCayleyTransform.range_one_sub_cayley
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Theorems.Thm_BookProof_ChapterCayleyTransform_sub_cayley_shift
open BookProof.ChapterCayleyTransform



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution :
    Set.range (fun y : H => y - cayley T y) = (T.domain : Set H) := by

  ext v
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x : T.domain, T.shift (-1) x = y :=
      ⟨T.res (-1) y, T.shift_res (by norm_num) y⟩
    change T.shift (-1) x - cayley T (T.shift (-1) x) ∈ (T.domain : Set H)
    rw [sub_cayley_shift]
    exact T.domain.smul_mem _ x.2
  · intro hv
    refine ⟨T.shift (-1) ((2 * Complex.I : ℂ)⁻¹ • (⟨v, hv⟩ : T.domain)), ?_⟩
    have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
    change T.shift (-1) ((2 * Complex.I : ℂ)⁻¹ • (⟨v, hv⟩ : T.domain))
        - cayley T (T.shift (-1) ((2 * Complex.I : ℂ)⁻¹ • (⟨v, hv⟩ : T.domain))) = v
    rw [sub_cayley_shift, Submodule.coe_smul, smul_smul, mul_inv_cancel₀ h2, one_smul]
