-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.left_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:02.082307+00:00
-- url     : https://prove2.me/submissions/50f17924-1da7-433a-af89-99cb9499eb93

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_RZ
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_lie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_RZ_point
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_foldr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D) (hπ'1 : π' 1 = 1)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (w : ℂ) (v : Wq) :
    capR k r Bs w J g v = capRep k r π (fun a => g *ᵥ Bs a) w (J g v) := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1.1
  have hLI : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hpk_sq']
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hLI
  have hgi : g⁻¹ * g = 1 := by rw [hinv, hLI]
  have hgi' : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hLI)
  have hgU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse hLI)
  have hginv : g⁻¹ ∈ UH (Hpk k r) := by
    show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
    calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
      _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hgi']; simp
  have h1W : (1 : Mx k r) ∈ UWset k r z' := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [UH]
  have hJ' : J ∈ AdK k r z π D := by
    refine ⟨hJ.1, fun x hx h hh => ?_⟩
    have e := hJ.2.2.2 x hx h hh 1 h1W
    rw [mul_one, hπ'1] at e
    simpa [ContinuousLinearMap.one_def] using e
  unfold capR capRep qmF
  simp only [Finset.sum_apply, ContinuousLinearMap.sum_apply, Pi.smul_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  refine (ad_foldr (AdK k r z π D) (fun F => F g v) _ _ _ ?_ ?_ J hJ').2
  · intro j x hx
    have hl := (ad_unitB_lie (z := z) (g := g) hBs (id (σ j)) (id j)).1
    refine adK_add ?_ (adK_RZ hD.1 hl.1 hl.2 hx)
    split_ifs
    · exact adK_smul hx _
    · exact adK_zero
  · intro j x hx
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    rw [ad_RZ_point hx hg hgi hgi' hgU hginv hBs _ _ v]
    split_ifs <;> simp
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
