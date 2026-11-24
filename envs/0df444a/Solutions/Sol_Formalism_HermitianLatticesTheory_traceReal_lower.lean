-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.traceReal_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:39.297797+00:00
-- url     : https://prove2.me/submissions/e45d627b-8766-4921-93e0-1d57f58aaf0a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Theorems.Thm_Formalism_HermitianLatticesTheory_isAddTorsionFree_ringOfIntegers_submodule
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_coercive_rat
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_expand
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_ratpos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
variable [Module (NumberField.RingOfIntegers K) V]
  [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ L, x ≠ 0 → l ≤ ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
  classical
  have := isAddTorsionFree_ringOfIntegers_submodule L
  have : Module.Finite ℤ L := Module.Finite.trans (NumberField.RingOfIntegers K) L
  let b := Module.Free.chooseBasis ℤ L
  let e : Module.Free.ChooseBasisIndex ℤ L → V := fun i => ((b i : L) : V)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ L) (Module.Free.ChooseBasisIndex ℤ L) ℚ :=
    fun i j => Algebra.trace ℚ K (h (e i) (e j))
  have hcoe : ∀ c : Module.Free.ChooseBasisIndex ℤ L → ℤ,
      (((∑ i, c i • b i : L)) : V) = ∑ i, c i • e i := by
    intro c; simp [e]
  have hqc : ∀ c : Module.Free.ChooseBasisIndex ℤ L → ℤ,
      Algebra.trace ℚ K (h (∑ i, c i • e i) (∑ i, c i • e i)) =
        (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c
    rw [thetaSummable_expand]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, G]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hZ : ∀ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, c ≠ 0 →
      0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c hc
    rw [← hqc]
    apply hpos
    rw [← hcoe]
    intro h0
    apply hc
    have h1 : (∑ i, c i • b i : L) = 0 := Subtype.ext h0
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c h1 i
  obtain ⟨l, hl, hcoer⟩ := thetaSummable_coercive_rat G (thetaSummable_ratpos G hZ)
  refine ⟨l, hl, fun x hx hx0 => ?_⟩
  set c := b.equivFun ⟨x, hx⟩ with hcdef
  have hxc : x = ∑ i, c i • e i := by
    rw [← hcoe, hcdef, b.sum_equivFun]
  have hc0 : c ≠ 0 := by
    intro hc
    apply hx0
    rw [hxc, hc]
    simp
  have hco := hcoer (fun i => (c i : ℚ))
  rw [← hqc, ← hxc] at hco
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hc0 (funext hh)
  have h2 : 0 < (c i) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
  have h3 : (1 : ℤ) ≤ (c i) ^ 2 := by linarith [Int.add_one_le_iff.mpr h2]
  have h4 : (1 : ℝ) ≤ (((c i : ℤ) : ℚ) : ℝ) ^ 2 := by exact_mod_cast h3
  have h5 : (1 : ℝ) ≤ ∑ j, (((c j : ℤ) : ℚ) : ℝ) ^ 2 :=
    h4.trans (Finset.single_le_sum (f := fun j => (((c j : ℤ) : ℚ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  nlinarith
end Formalism.HermitianLatticesTheory
