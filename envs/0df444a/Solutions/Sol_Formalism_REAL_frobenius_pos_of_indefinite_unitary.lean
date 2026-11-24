-- Prove2me | solution 1 for Formalism.REAL.frobenius_pos_of_indefinite_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:58:59.027561+00:00
-- url     : https://prove2.me/submissions/21e23498-cb9a-4d71-af14-2bdc40d51c57

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_frobenius_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    [Nonempty (Fin n)] : 0 < hs g := by
  by_contra hle
  push_neg at hle
  have h0 : hs g = 0 := le_antisymm hle (frobenius_nonneg g)
  have hg0 : g = 0 := by
    unfold hs at h0
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h0 i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j (Finset.mem_univ _)
    simpa using h2
  unfold inUJ at hg
  rw [hg0] at hg
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  have := congrFun (congrFun hg i) i
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply, Jm,
    Matrix.diagonal_apply_eq] at this
  split_ifs at this <;> norm_num at this
end Formalism.REAL
