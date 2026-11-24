-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.EHc_HL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:48.664389+00:00
-- url     : https://prove2.me/submissions/7dcbf149-dc14-4a26-bd1b-ce2d2d42edff

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem inLie_conj_of_mem_GV' {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) :
    inLie k r (y⁻¹ * X * y) := by
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have h1 : Hpk k r * y⁻¹ = yᴴ * Hpk k r := by
    calc Hpk k r * y⁻¹ = yᴴ * Hpk k r * y * y⁻¹ := by rw [hy']
      _ = yᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 : (y⁻¹)ᴴ * Hpk k r = Hpk k r * y := by
    calc (y⁻¹)ᴴ * Hpk k r = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * y := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * y := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at hX ⊢
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h2]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    simp only [← Matrix.mul_assoc]
    rw [h1]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.JFxE
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {y : Mat k r} (hy : y ∈ GV k r) : HL (EHc (E := E) k r y) := by
  intro a b f f₂ h g hg
  rw [EHc_eq, EHc_eq]
  beta_reduce
  rw [Dx_congr (x := (false, y⁻¹ * Xa k r a b * y)) (inLie_conj_of_mem_GV' hy (Xa_lie a b)) h g hg,
    Dx_congr (x := (false, y⁻¹ * Xb k r a b * y)) (inLie_conj_of_mem_GV' hy (Xb_lie a b)) h g hg]
end Formalism.FourierDecayAlt.P.JFxE
