-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:21.714423+00:00
-- url     : https://prove2.me/submissions/cf623c6e-b104-45b4-aa34-51e2989badf5

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_dint

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
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (ι : V →+ EuclideanSpace ℝ (Fin n))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (d : ℕ) (hd : 0 < d) (M : Submodule (NumberField.RingOfIntegers K) V)
    (hdM : ∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K))
    (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) : 1 / (d : ℝ) ≤ ‖ι x‖ := by
  obtain ⟨z, hz⟩ := classSetAssembly_dint h d x x (hdM x hx x hx)
  have hp := hpos x hx0
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hz0 : (0 : ℤ) < z := by
    have : (0 : ℚ) < z := by rw [← hz]; exact mul_pos hdQ hp
    exact_mod_cast this
  have hz1 : (1 : ℝ) ≤ z := by
    have : (1 : ℤ) ≤ z := by omega
    exact_mod_cast this
  have hn : ‖ι x‖ ^ 2 = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, hι]
  have hzR : (d : ℝ) * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = (z : ℝ) := by
    exact_mod_cast hz
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN := norm_nonneg (ι x)
  have key : 1 ≤ (‖ι x‖ * d) ^ 2 := by
    have e : (‖ι x‖ * d) ^ 2 = (z : ℝ) * d := by
      rw [mul_pow, hn, ← hzR]; ring
    rw [e]
    nlinarith
  have hNd : 0 ≤ ‖ι x‖ * d := mul_nonneg hN hdR.le
  rw [div_le_iff₀ hdR]
  nlinarith
end Formalism.HermitianLatticesTheory
