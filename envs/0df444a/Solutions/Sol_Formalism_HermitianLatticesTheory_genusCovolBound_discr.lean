-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovolBound_discr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:17.536003+00:00
-- url     : https://prove2.me/submissions/2c999241-3516-4ac7-8740-4abec1e01ef1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (a : K)
    (ha : ∀ r : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (a * algebraMap (𝓞 K) K r) = z) :
    ((NumberField.discr K : ℤ) : K) * a ∈ (1 : Submodule (𝓞 K) K) := by
  classical
  have htr : ∀ r : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (𝓞 K) K r) = z := by
    intro r
    have hi : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (𝓞 K) K r)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨z, by rw [← hz]; simp⟩
  have hint : ∀ i j, ∃ z : ℤ, Algebra.trace ℚ K
      (NumberField.integralBasis K i * NumberField.integralBasis K j) = z := by
    intro i j
    simpa [NumberField.integralBasis_apply, map_mul] using
      htr (RingOfIntegers.basis K i * RingOfIntegers.basis K j)
  choose T hT using hint
  have hm : ∀ i, ∃ z : ℤ, Algebra.trace ℚ K (a * NumberField.integralBasis K i) = z := by
    intro i
    simpa [NumberField.integralBasis_apply] using ha (RingOfIntegers.basis K i)
  choose m hm' using hm

  let Tq : Matrix _ _ ℚ := (Int.castRingHom ℚ).mapMatrix (Matrix.of T)
  have hTq : Matrix.mulVec Tq ((NumberField.integralBasis K).repr a) = fun i => (m i : ℚ) := by
    funext i
    have hs : Algebra.trace ℚ K (a * NumberField.integralBasis K i) =
        ∑ j, (NumberField.integralBasis K).repr a j *
          Algebra.trace ℚ K (NumberField.integralBasis K i * NumberField.integralBasis K j) := by
      conv_lhs => rw [← (NumberField.integralBasis K).sum_repr a]
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul,
        mul_comm (NumberField.integralBasis K j)]
    rw [← hm' i, hs]
    simp only [Matrix.mulVec, dotProduct, Tq, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, eq_intCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hT i j, mul_comm]
  have hdet : ((NumberField.discr K : ℤ) : ℚ) = Tq.det := by
    rw [NumberField.coe_discr, Algebra.discr_def]
    congr 1
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Tq, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.of_apply, eq_intCast, hT]
  have hn : ∀ i, ((NumberField.discr K : ℤ) : ℚ) * (NumberField.integralBasis K).repr a i =
      (Matrix.mulVec (Matrix.of T).adjugate m i : ℤ) := by
    intro i
    have h2 : Matrix.mulVec Tq.adjugate (Matrix.mulVec Tq ((NumberField.integralBasis K).repr a)) =
        Matrix.mulVec Tq.adjugate (fun i => (m i : ℚ)) := by rw [hTq]
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h2
    have h3 := congrFun h2 i
    rw [Pi.smul_apply, smul_eq_mul, ← hdet] at h3
    rw [h3, show Tq.adjugate = (Int.castRingHom ℚ).mapMatrix (Matrix.of T).adjugate from
      (RingHom.map_adjugate _ _).symm]
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
    push_cast
    rfl
  rw [Submodule.mem_one]
  refine ⟨∑ i, Matrix.mulVec (Matrix.of T).adjugate m i • RingOfIntegers.basis K i, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← (NumberField.integralBasis K).sum_repr a, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul, ← NumberField.integralBasis_apply, Rat.smul_def]
  have := congrArg (fun q : ℚ => (q : K)) (hn i)
  push_cast at this
  rw [← this]
  ring
end Formalism.HermitianLatticesTheory
