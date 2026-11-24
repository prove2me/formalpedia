-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.col_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:14.999826+00:00
-- url     : https://prove2.me/submissions/df3c8f33-a407-47e2-85f3-59e90a33529d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_act_pathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_map_pathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {L : Type} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (g : (Matrix (Fin n) (Fin n) L)ˣ) (N : ℕ) (J : Finset (Fin n)) :
    actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N J) =
      ∑ I' : Finset (Fin n),
        pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N I' *
          C (minorF (if 1 ≤ c then (↑g : Matrix (Fin n) (Fin n) L)
            else (↑g⁻¹ : Matrix (Fin n) (Fin n) L).transpose) I' J) := by
  have h1 := A1hw.map_pathWord
    ((actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) :
      MvPolynomial (ℕ × Fin n) L →ₐ[L] MvPolynomial (ℕ × Fin n) L) :
      MvPolynomial (ℕ × Fin n) L →+* MvPolynomial (ℕ × Fin n) L)
    isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N J
  rw [RingHom.coe_coe] at h1
  rw [h1]
  have hX : ∀ i, (fun a => actAll isVec (↑g : Matrix (Fin n) (Fin n) L)
      (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (X (i, a) : MvPolynomial (ℕ × Fin n) L)) =
      if isVec i then Matrix.vecMul (fun b => (X (i, b) : MvPolynomial (ℕ × Fin n) L))
          ((↑g : Matrix (Fin n) (Fin n) L).map C)
        else Matrix.vecMul (fun b => (X (i, b) : MvPolynomial (ℕ × Fin n) L))
          ((↑g⁻¹ : Matrix (Fin n) (Fin n) L).map C).transpose := by
    intro i
    funext a
    unfold actAll
    rw [aeval_X]
    split_ifs <;> rfl
  let G : (Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L))ˣ :=
    Units.map ((C : L →+* MvPolynomial (ℕ × Fin n) L).mapMatrix (m := Fin n)).toMonoidHom g
  have hG : (↑G : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L)) =
      (↑g : Matrix (Fin n) (Fin n) L).map C := rfl
  have hGi : (↑G⁻¹ : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L)) =
      (↑g⁻¹ : Matrix (Fin n) (Fin n) L).map C := rfl
  by_cases hc : 1 ≤ c
  · have := A1hw.act_pathWord actFormWedge actFormContract isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L))
      (fun i a => actAll isVec (↑g : Matrix (Fin n) (Fin n) L)
        (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (X (i, a) : MvPolynomial (ℕ × Fin n) L)) G
      (fun i hi => by
        have hv : isVec i = true := by simpa [hc] using hi
        rw [hX i, if_pos hv, hG])
      (fun i hi => by
        have hv : ¬ isVec i = true := by simpa [hc] using hi
        rw [hX i, if_neg hv, hGi]) N
    rw [this]
    unfold actF
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [if_pos hc, hG, minorMap]
  · have := A1hw.act_pathWord actFormWedge actFormContract isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L))
      (fun i a => actAll isVec (↑g : Matrix (Fin n) (Fin n) L)
        (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (X (i, a) : MvPolynomial (ℕ × Fin n) L)) (invT G)
      (fun i hi => by
        have hv : ¬ isVec i = true := by simpa [hc] using hi
        rw [hX i, if_neg hv]
        rfl)
      (fun i hi => by
        have hv : isVec i = true := by simpa [hc] using hi
        rw [hX i, if_pos hv]
        show _ = Matrix.vecMul _ ((↑G : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L)).transpose).transpose
        rw [Matrix.transpose_transpose, hG]) N
    rw [this]
    unfold actF
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [if_neg hc, minorMap]
    rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
