-- Prove2me | solution 1 for ConvexOptimization.fenchel_biconjugate_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-15T14:40:43.254739+00:00
-- url     : https://prove2.me/submissions/d1513f50-a786-4b95-9ba1-94c8b3d326f8

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_fenchelBiconjugate

open Set
open scoped RealInnerProductSpace ENNReal
open ConvexOptimization

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    fenchelBiconjugate f x = (f x : EReal) := by
  let E := EuclideanSpace ℝ (Fin n)
  apply le_antisymm
  · unfold fenchelBiconjugate
    refine iSup_le fun y ↦ ?_
    have hterm : ((⟪x, y⟫ - f x : ℝ) : EReal) ≤ fenchelConjugate f y := by
      unfold fenchelConjugate
      exact le_iSup (fun z : E ↦ ((⟪z, y⟫ - f z : ℝ) : EReal)) x
    calc
      (((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y)
          ≤ ((⟪x, y⟫ : ℝ) : EReal) -
              ((⟪x, y⟫ - f x : ℝ) : EReal) := EReal.sub_le_sub le_rfl hterm
      _ = (f x : EReal) := by
        rw [← EReal.coe_sub]
        congr 1
        ring
  · by_contra! hlt
    obtain ⟨a, hBa, hafx⟩ := EReal.exists_between_coe_real hlt
    have hcont : ContinuousOn f Set.univ := hf.continuousOn isOpen_univ
    obtain ⟨l, c, hl, hlx⟩ := hf.exists_affine_le_of_lt (𝕜 := ℝ)
      (mem_univ x) (by exact_mod_cast hafx) isClosed_univ hcont.lowerSemicontinuousOn
    let y : E := (InnerProductSpace.toDual ℝ E).symm l
    have hly (z : E) : ⟪z, y⟫ = l z := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hminor (z : E) : l z + c ≤ f z := by
      simpa using hl ⟨z, mem_univ z⟩
    have hconj : fenchelConjugate f y ≤ ((-c : ℝ) : EReal) := by
      unfold fenchelConjugate
      refine iSup_le fun z ↦ ?_
      rw [EReal.coe_le_coe_iff, hly]
      linarith [hminor z]
    have hax : l x + c = a := by simpa using hlx
    have haTerm : (a : EReal) ≤
        (((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y) := by
      calc
        (a : EReal) = ((l x + c : ℝ) : EReal) := by rw [hax]
        _ = (((⟪x, y⟫ : ℝ) : EReal) - ((-c : ℝ) : EReal)) := by
          rw [← EReal.coe_sub, hly]
          congr 1
          ring
        _ ≤ (((⟪x, y⟫ : ℝ) : EReal) - fenchelConjugate f y) :=
          EReal.sub_le_sub le_rfl hconj
    have haB : (a : EReal) ≤ fenchelBiconjugate f x := by
      unfold fenchelBiconjugate
      exact haTerm.trans (le_iSup (fun z : E ↦
        (((⟪x, z⟫ : ℝ) : EReal) - fenchelConjugate f z)) y)
    exact (not_lt_of_ge haB) hBa
