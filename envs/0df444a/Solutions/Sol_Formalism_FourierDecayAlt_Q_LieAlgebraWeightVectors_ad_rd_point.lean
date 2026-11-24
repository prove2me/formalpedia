-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_rd_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:11.365862+00:00
-- url     : https://prove2.me/submissions/290554c5-f01e-4d62-b6d7-3f7b247a9801

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_curve_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_exp_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_hasDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
private theorem mul_mem_uh {n : Type*} [Fintype n] [DecidableEq n] {H a b : Matrix n n ℂ}
    (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hgi : g⁻¹ * g = 1) (hgi' : g * g⁻¹ = 1) (hgU : IsUnit g)
    (hginv : g⁻¹ ∈ UH (Hpk k r)) {X : Mx k r} (hX : inLieLev k r (Fin.last r) X)
    (hXz : X *ᵥ (g⁻¹ *ᵥ z) = 0) (v : Wq) :
    RdV X F g v = dRep π (g * X * g⁻¹) (F g v) := by
  have hYv : ∀ w, (g * X * g⁻¹) *ᵥ w = g *ᵥ (X *ᵥ (g⁻¹ *ᵥ w)) := fun w => by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hexp : ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) =
      NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g := by
    intro t
    have e1 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1]
    first
      | rw [Matrix.exp_conj g _ hgU]
      | rw [Matrix.exp_conj ℂ g _ hgU]
      | rw [Matrix.exp_conj ℝ g _ hgU]
    rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have hginvfix : ∀ w, g *ᵥ w = w → g⁻¹ *ᵥ w = w := by
    intro w hw
    conv_lhs => rw [← hw]
    rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
  have hmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) ∈ UWset k r z := by
    intro t
    have hE : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) = g * NormedSpace.exp ((t : ℂ) • X) * g⁻¹ := by
      rw [hexp t, Matrix.mul_assoc (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) g g⁻¹, hgi', Matrix.mul_one]
    refine ⟨?_, fun a => ?_, ?_⟩
    · rw [hE]
      exact mul_mem_uh (curve_lev hg.1 hX t).1 hginv
    · obtain ⟨h1, h2⟩ := hg.1.2 a a.isLt
      obtain ⟨x1, x2⟩ := hX.2 a a.isLt
      refine ⟨exp_fix ?_ t, exp_fix ?_ t⟩
      · rw [hYv, hginvfix _ h1, x1, Matrix.mulVec_zero]
      · rw [hYv, hginvfix _ h2, x2, Matrix.mulVec_zero]
    · exact exp_fix (by rw [hYv, hXz, Matrix.mulVec_zero]) t
  have heq : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) =
      (π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))).comp (F g) := by
    intro t
    rw [hexp t]
    exact hF.2 g hg _ (hmem t)
  have hd := rd_hasDeriv hF.1 hg hX
  have hd' := ((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply] at hd'
  have hfun : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (F g v)) =
      fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)) v := by
    funext t
    rw [heq t]
    rfl
  rw [dRep, hfun]
  exact hd'.deriv.symm
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
