-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.projective_lines_geometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:51.400132+00:00
-- url     : https://prove2.me/submissions/8a50e065-4f6b-4c2b-9d78-66e74e8609e9

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
variable (p : ℕ) [Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution (v : InfinitePlace K) :
    LatGeom (κ₁ := Empty) (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
      (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
      (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) (lineMap K p)
      (fun i => htMap (Pi.basisFun K (ZMod p)) (fun _ => 1) (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1)
        (lineMap K p i)) v (fun _ => 1) 1 (lineMat p) 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨by simp, by simp, by simp, by simp, standard_lattice_fg K _, standard_lattice_span_eq_top K _,
    fun _ => standard_lattice_fg K _, fun _ => standard_lattice_span_eq_top K _, ?_, ?_, fun _ _ => le_rfl, le_rfl,
    one_pos, by simp, ?_⟩
  · simp only [ZMod.card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_pos Fintype.card_pos hp
  · intro i
    unfold stdLat
    rw [Submodule.map_span_le]
    rintro _ ⟨t, rfl⟩
    rw [LinearMap.coe_restrictScalars]
    unfold lineMap
    rw [Matrix.toLin_self]
    refine Submodule.sum_mem _ fun q _ => ?_
    by_cases hq : q = linePt p i t
    · simp only [Matrix.of_apply, hq, if_true, one_smul]
      exact Submodule.subset_span ⟨_, rfl⟩
    · simp only [Matrix.of_apply, hq, if_false, zero_smul]
      exact Submodule.zero_mem _
  · intro i k j
    simp only [lineMap, LinearMap.toMatrix_toLin, inv_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.map_apply, Matrix.of_apply, lineMat, Sum.inl.injEq]
    split_ifs <;> simp
end Formalism.LFunctionChainParameters.ProjectiveLineModels
