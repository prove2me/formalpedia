-- Prove2me | solution 1 for Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:07.282594+00:00
-- url     : https://prove2.me/submissions/7a7b939c-8ebe-43a8-9275-7ebea6551cd4

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Theorems.Thm_Formalism_F_covolEqGram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.RankSupermodularCovolume
theorem _root_.solution (N N' : Submodule ℤ E) [DiscreteTopology N'] (hle : N ≤ N')
    (hrk : rk N = rk N') :
    covol N = (N.toAddSubgroup.relIndex N'.toAddSubgroup : ℝ) * covol N' := by
  classical
  haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (N' : Set E)) ‹_› hle
  let K : Submodule ℤ N' := N.comap N'.subtype
  let eK : K ≃ₗ[ℤ] N := Submodule.comapSubtypeEquivOfLe hle
  have hK : Module.finrank ℤ K = Module.finrank ℤ N' := by
    rw [eK.finrank_eq]; exact hrk
  let b : Basis (Fin (Module.finrank ℤ N')) ℤ N' := Module.finBasis ℤ N'
  let bK : Basis (Fin (Module.finrank ℤ N')) ℤ K := Module.finBasisOfFinrankEq ℤ K hK
  let A : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℤ :=
    Matrix.of fun i j => b.repr (bK j : N') i
  let Ar : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℝ :=
    Matrix.of fun i j => ((b.repr (bK j : N') i : ℤ) : ℝ)
  have hidx : N.toAddSubgroup.relIndex N'.toAddSubgroup = (b.det (Subtype.val ∘ bK)).natAbs := by
    rw [Submodule.natAbs_det_basis_change b K bK]
    rfl
  let v : Fin (Module.finrank ℤ N') → E := fun i => (b i : E)
  let w : Fin (Module.finrank ℤ N') → E := fun i => ((bK i : N') : E)
  have hw : ∀ j, w j = ∑ i, Ar i j • v i := by
    intro j
    have h := b.sum_repr ((bK j : N'))
    have h2 := congrArg (fun x : N' => (x : E)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    show ((bK j : N') : E) = _
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Ar, v, Int.cast_smul_eq_zsmul]
  have hgram : Matrix.gram ℝ w = Ar.transpose * (Matrix.gram ℝ v * Ar) := by
    ext i j
    simp only [Matrix.gram_apply, hw, Matrix.mul_apply, Matrix.transpose_apply,
      inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hA : Ar.det = (A.det : ℝ) := by
    have := ((Int.castRingHom ℝ).map_det A).symm
    simpa [Ar, A, RingHom.mapMatrix_apply, Matrix.map] using this
  have hdet : (Matrix.gram ℝ w).det = (A.det : ℝ) ^ 2 * (Matrix.gram ℝ v).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hA]
    ring
  have hcw : (fun i => ((bK.map eK) i : E)) = w := by
    funext i
    rfl
  have hbd : b.det (Subtype.val ∘ bK) = A.det := by
    rw [Basis.det_apply]
    rfl
  rw [covolEqGram E N (Fin (Module.finrank ℤ N')) (bK.map eK), covolEqGram E N' _ b, hcw, hdet,
    hidx, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, hbd]
  simp [Nat.cast_natAbs, Int.cast_abs]
  exact Or.inl rfl
end Formalism.RankSupermodularCovolume
