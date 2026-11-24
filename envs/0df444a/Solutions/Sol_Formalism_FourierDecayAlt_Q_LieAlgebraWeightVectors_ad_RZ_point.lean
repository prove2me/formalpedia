-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_RZ_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:35:19.757619+00:00
-- url     : https://prove2.me/submissions/a2e88650-9bda-4734-b479-53d44907078d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_rd_point
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_lie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_hpart_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ad_unitB_conj


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
theorem _root_.solution {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hgi : g⁻¹ * g = 1) (hgi' : g * g⁻¹ = 1) (hgU : IsUnit g)
    (hginv : g⁻¹ ∈ UH (Hpk k r)) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (a b : Fin m) (v : Wq) :
    RZ (Hpk k r) (unitB (Hpk k r) Bs a b) F g v =
      EcRep (Hpk k r) π (unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b) (F g v) := by
  have hH : (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r := hginv
  have hgH : gᴴ * Hpk k r * g = Hpk k r := by
    calc gᴴ * Hpk k r * g = gᴴ * ((g⁻¹)ᴴ * Hpk k r * g⁻¹) * g := by rw [hH]
      _ = (g⁻¹ * g)ᴴ * Hpk k r * (g⁻¹ * g) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hgi]; simp
  obtain ⟨⟨h1, h2⟩, hk1, hk2⟩ := ad_unitB_lie (z := z) (g := g) hBs a b
  simp only [RZ, EcRep]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ad_rd_point hF hg hgi hgi' hgU hginv h1 hk1 v, ad_rd_point hF hg hgi hgi' hgU hginv h2 hk2 v,
    ad_unitB_conj hgH hgi', (ad_hpart_conj hgH hgi' _).1, (ad_hpart_conj hgH hgi' _).2]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
