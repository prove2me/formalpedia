-- Prove2me | solution 1 for Formalism.REAL.isCompact_frobenius_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:59:58.501339+00:00
-- url     : https://prove2.me/submissions/172ad40f-d3f0-43ee-8054-ec4e399630bf

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_contDiff_frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
section F4ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end F4ALinfty
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma Jm_mul_Jm_self {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private lemma Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : Jm ε * gᴴ * Jm ε * g = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Jm_mul_Jm_self]
end Formalism.REAL
end
end

set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (r : ℝ) : IsCompact {g : UJ ε | hsG g ≤ r} := by
  haveI : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _
  have hhs : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := contDiff_frobenius.continuous
  have hSc : IsCompact {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g ∧ hs g ≤ r} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · show IsClosed ({g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε} ∩ {g | hs g ≤ r})
      have hcJ : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * Jm ε * g) :=
        (continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id
      exact (isClosed_eq hcJ continuous_const).inter (isClosed_le hhs continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨Real.sqrt r, fun g hg => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Matrix.norm_le_iff (Real.sqrt_nonneg r)).2 fun i j => ?_
      have h1 : ‖g i j‖ ^ 2 ≤ hs g := by
        unfold hs
        calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
              Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity)
                (Finset.mem_univ j)
          _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
              Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
                (Finset.mem_univ i)
      calc ‖g i j‖ = Real.sqrt (‖g i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt r := Real.sqrt_le_sqrt (h1.trans hg.2)
  haveI := isCompact_iff_compactSpace.mp hSc
  let ψ : {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g ∧ hs g ≤ r} → UJ ε := fun p =>
    ⟨⟨p.1, Jm ε * (p.1)ᴴ * Jm ε, mul_eq_one_comm.mp (Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ p.2.1), Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ p.2.1⟩, p.2.1⟩
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul continuous_const
  have key : {g : UJ ε | hsG g ≤ r} = Set.range ψ := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨toM g, show inUJ ε (toM g) ∧ hs (toM g) ≤ r from ⟨g.2, hg⟩⟩, Subtype.ext (Units.ext rfl)⟩
    · rintro ⟨p, rfl⟩
      exact p.2.2
  rw [key]
  exact isCompact_range hψ
end Formalism.REAL
