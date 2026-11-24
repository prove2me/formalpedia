-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:46.000784+00:00
-- url     : https://prove2.me/submissions/b365d02c-226e-4b7d-abba-f4d6e12bf033

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_swap4
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_sf
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_levM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_cell_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_os_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_os_cell
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_thetaF_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
attribute [local instance] sfHeis
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (hN : ClosedN) (μN' μb' : Measure (Mt k r')) (hμN' : IsHaarOn (Nset k r') μN') [SigmaFinite μb']
    (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) (c : ℂ) (B : Mat k r') :
    ∫⁻ X : HPar k r' × HPar k r', ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
        f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * B * Matrix.of q.2 * Matrix.of q.1.2) X.2)
          ∂((μN'.prod μN').prod μb') =
      ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
        f ((Matrix.of p.1.1)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of p.2 * Matrix.of p.1.2)
          ∂(((((volume : Measure (HPar k r')).prod μN').map (thetaF k r')).prod
            (((volume : Measure (HPar k r')).prod μN').map (thetaF k r'))).prod (μb'.map (levM k r'))) := by
  have : SigmaFinite μN' := sf hμN'
  have hcell : Measurable fun p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r') =>
      f ((Matrix.of p.1.1)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of p.2 * Matrix.of p.1.2) :=
    hf.comp (cell_meas (N := fun p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r') => p.1.1)
      (T := fun _ => (w0 k r' c * ιLev k 1 r' B : Mat k (1 + r'))) (M := fun p => p.2) (N' := fun p => p.1.2)
      (measurable_fst.comp measurable_fst) measurable_const measurable_snd
      (measurable_snd.comp measurable_fst))
  have hΘ : Measurable (Prod.map (Prod.map (thetaF k r') (thetaF k r')) (levM k r')) :=
    (thetaF_meas.prodMap thetaF_meas).prodMap levM_meas
  let Fs : ((HPar k r' × Mt k r') × (HPar k r' × Mt k r')) × Mt k r' → ℝ≥0∞ := fun s =>
    f ((Matrix.of (thetaF k r' s.1.1))⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of (levM k r' s.2) *
      Matrix.of (thetaF k r' s.1.2))
  have hFs : Measurable Fs := hf.comp (cell_meas
      (N := fun s : ((HPar k r' × Mt k r') × (HPar k r' × Mt k r')) × Mt k r' => thetaF k r' s.1.1)
      (T := fun _ => (w0 k r' c * ιLev k 1 r' B : Mat k (1 + r'))) (M := fun s => levM k r' s.2)
      (N' := fun s => thetaF k r' s.1.2)
      (thetaF_meas.comp (measurable_fst.comp measurable_fst)) measurable_const (levM_meas.comp measurable_snd)
      (thetaF_meas.comp (measurable_snd.comp measurable_fst)))
  have hsw : Measurable fun p : (HPar k r' × HPar k r') × (Mt k r' × Mt k r') =>
      ∫⁻ m, Fs (((p.1.1, p.2.1), (p.1.2, p.2.2)), m) ∂μb' := by
    have h2 : Measurable fun p : (HPar k r' × HPar k r') × (Mt k r' × Mt k r') =>
        (((p.1.1, p.2.1), (p.1.2, p.2.2)) : (HPar k r' × Mt k r') × (HPar k r' × Mt k r')) := by fun_prop
    exact hFs.lintegral_prod_right'.comp h2
  symm
  calc _ = ∫⁻ s, Fs s ∂((((volume : Measure (HPar k r')).prod μN').prod
            ((volume : Measure (HPar k r')).prod μN')).prod μb') := by
        rw [Measure.map_prod_map _ _ thetaF_meas thetaF_meas,
          Measure.map_prod_map _ _ (thetaF_meas.prodMap thetaF_meas) levM_meas]
        exact lintegral_map hcell hΘ
    _ = ∫⁻ u, ∫⁻ m, Fs (u, m) ∂μb' ∂(((volume : Measure (HPar k r')).prod μN').prod
            ((volume : Measure (HPar k r')).prod μN')) := lintegral_prod _ hFs.aemeasurable
    _ = ∫⁻ p : (HPar k r' × HPar k r') × (Mt k r' × Mt k r'), ∫⁻ m, Fs (((p.1.1, p.2.1), (p.1.2, p.2.2)), m) ∂μb'
          ∂(((volume : Measure (HPar k r')).prod (volume : Measure (HPar k r'))).prod (μN'.prod μN')) :=
        swap4 _ _ _ _ (fun u => ∫⁻ m, Fs (u, m) ∂μb') hFs.lintegral_prod_right'
    _ = ∫⁻ X : HPar k r' × HPar k r', ∫⁻ Q : Mt k r' × Mt k r', ∫⁻ m, Fs (((X.1, Q.1), (X.2, Q.2)), m) ∂μb'
          ∂(μN'.prod μN') := lintegral_prod _ hsw.aemeasurable
    _ = _ := by
        refine lintegral_congr fun X => ?_
        have hq : Measurable fun q : (Mt k r' × Mt k r') × Mt k r' =>
            f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * B * Matrix.of q.2 * Matrix.of q.1.2) X.2) :=
          hf.comp (os_meas (X := fun _ => X.1) (C := fun _ => c) (X' := fun _ => X.2) measurable_const measurable_const
            (cell_meas (N := fun q : (Mt k r' × Mt k r') × Mt k r' => q.1.1) (T := fun _ => B) (M := fun q => q.2)
              (N' := fun q => q.1.2) (measurable_fst.comp measurable_fst) measurable_const measurable_snd
              (measurable_snd.comp measurable_fst)) measurable_const)
        refine Eq.trans ?_ (lintegral_prod _ hq.aemeasurable).symm
        refine lintegral_congr_ae ?_
        have hae : ∀ᵐ Q : Mt k r' × Mt k r' ∂(μN'.prod μN'), (Matrix.of Q.1 : Mat k r') ∈ Nset k r' :=
          Measure.quasiMeasurePreserving_fst.ae (haar_ae hμN')
        filter_upwards [hae] with Q hQ
        refine lintegral_congr fun m => ?_
        exact congrArg f
          (os_cell X.1 X.2 c B (Matrix.of Q.1) (Matrix.of Q.2) (Matrix.of m) ((hN k r').unit _ hQ)).symm
end Formalism.FourierDecayAlt.P.LongWeylElement
