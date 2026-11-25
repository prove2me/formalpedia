-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.iter_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:51.388963+00:00
-- url     : https://prove2.me/submissions/3db5d031-6fdb-4fa3-9b3f-3e4e41076ed7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_t_bigcellrec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_uWbRec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lint_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_cWeight_rec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_sf
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mm_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_levM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bcF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_long_weyl_element_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_cell_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_os_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_nuN_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lint_smul3
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_cW_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (hO : OneStepInt) (HU : HaarUnique) (hL : LevHaar) (hCN : ClosedN) (hCb : ClosedWb)
    (hG : HaarGExists) (hNe : HaarNExists) (hWb : HaarWbExists) (hNR : NRecHaar) (hC : HeisConjLevMeas)
    (k r' : ℕ) (ih : IterAt k r') : IterAt k (1 + r') := by
  intro μG μN μb hμG hμN hμb
  obtain ⟨μG₁, hG₁⟩ := hG k r'
  obtain ⟨μN', hN'⟩ := hNe k r'
  obtain ⟨μb', hb'⟩ := hWb k r'
  obtain ⟨C₀, hC₀, h0⟩ := hO k r' μG μG₁ hμG hG₁
  obtain ⟨C₁, hC₁, h1⟩ := ih μG₁ μN' μb' hG₁ hN' hb'
  have hνN : IsHaarOn (Nset k (1 + r')) (((volume : Measure (HPar k r')).prod μN').map (thetaF k r')) := by
    rw [← nuN_eq hC hCN μN' hN']; exact hNR k r' μN' hN'
  obtain ⟨a, ha, hae⟩ := haar_smul HU (hCN k (1 + r')) hμN hνN
  have hνb : IsHaarOn (UWb k (1 + r')) (μb'.map (levM k r')) := by
    rw [uWbRec k r']; exact (hL k r' _ μb' (hCb k r') hb').2
  obtain ⟨b, hb, hbe⟩ := haar_smul HU (hCb k (1 + r')) hμb hνb
  have : SigmaFinite μG₁ := sf hG₁
  have : SigmaFinite μN' := sf hN'
  have : SigmaFinite μb' := sf hb'
  have : SigmaFinite μN := sf hμN
  have : SigmaFinite μb := sf hμb
  refine ⟨C₀ * C₁ * (a * a * b), by positivity, fun f hf => ?_⟩

  let Kμ : Mt k (1 + r') → ℝ≥0∞ := fun T =>
    ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
      f ((Matrix.of p.1.1)⁻¹ * Matrix.of T * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb)
  have hKμ : Measurable Kμ := by
    have : Measurable fun t : Mt k (1 + r') × ((Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r')) =>
        f ((Matrix.of t.2.1.1)⁻¹ * Matrix.of t.1 * Matrix.of t.2.2 * Matrix.of t.2.1.2) :=
      hf.comp (cell_meas (N := fun t : Mt k (1 + r') × ((Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r')) => t.2.1.1)
        (T := fun t => t.1) (M := fun t => t.2.2) (N' := fun t => t.2.1.2)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
    exact this.lintegral_prod_right'
  let TT : ℂ × (Fin r' → ℂ) → Mt k (1 + r') := fun p => mulM (w0F k r' p.1, levM k r' (bcF k r' p.2))
  have hTT : Measurable TT := mm_meas (long_weyl_element_measurable.comp measurable_fst) (levM_meas.comp (bcF_meas.comp measurable_snd))

  have step : ∀ c : ℂ, ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)
        ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁) =
      (C₁ : ℝ≥0∞) * (((a * a * b : ℝ≥0) : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') * Kμ (TT (c, c'))) := by
    intro c
    have m1 : Measurable fun p : (HPar k r' × HPar k r') × Mt k r' => f (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) :=
      hf.comp (os_meas (X := fun p : (HPar k r' × HPar k r') × Mt k r' => p.1.1) (C := fun _ => c) (Gm := fun p => p.2)
        (X' := fun p => p.1.2) (by fun_prop) measurable_const (by fun_prop) (by fun_prop))
    have m3 : Measurable fun t : ((HPar k r' × HPar k r') × (Fin r' → ℂ)) × ((Mt k r' × Mt k r') × Mt k r') =>
        f (oneStep k r' t.1.1.1 c ((Matrix.of t.2.1.1)⁻¹ * bigCell k r' t.1.2 1 * Matrix.of t.2.2 * Matrix.of t.2.1.2)
          t.1.1.2) :=
      hf.comp (os_meas
        (X := fun t : ((HPar k r' × HPar k r') × (Fin r' → ℂ)) × ((Mt k r' × Mt k r') × Mt k r') => t.1.1.1)
        (C := fun _ => c) (X' := fun t => t.1.1.2) (by fun_prop) measurable_const
        (cell_meas (N := fun t : ((HPar k r' × HPar k r') × (Fin r' → ℂ)) × ((Mt k r' × Mt k r') × Mt k r') => t.2.1.1)
          (T := fun t => bcF k r' t.1.2) (M := fun t => t.2.2) (N' := fun t => t.2.1.2)
          (by fun_prop) (bcF_meas.comp (by fun_prop)) (by fun_prop) (by fun_prop)) (by fun_prop))
    calc _ = ∫⁻ X : HPar k r' × HPar k r', ∫⁻ g₁ : Mt k r', f (oneStep k r' X.1 c (Matrix.of g₁) X.2) ∂μG₁ :=
          lintegral_prod _ m1.aemeasurable
      _ = ∫⁻ X : HPar k r' × HPar k r', (C₁ : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') *
            ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
              f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * bigCell k r' c' 1 * Matrix.of q.2 * Matrix.of q.1.2) X.2)
                ∂((μN'.prod μN').prod μb') := by
          refine lintegral_congr fun X => ?_
          exact h1 (fun g₁ => f (oneStep k r' X.1 c (Matrix.of g₁) X.2))
            (hf.comp (os_meas (X := fun _ => X.1) (C := fun _ => c) (Gm := fun g₁ => g₁) (X' := fun _ => X.2)
              measurable_const measurable_const measurable_id measurable_const))
      _ = (C₁ : ℝ≥0∞) * ∫⁻ X : HPar k r' × HPar k r', ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') *
            ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
              f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * bigCell k r' c' 1 * Matrix.of q.2 * Matrix.of q.1.2) X.2)
                ∂((μN'.prod μN').prod μb') := lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (C₁ : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ∫⁻ X : HPar k r' × HPar k r', ENNReal.ofReal (cWeight k r' c') *
            ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
              f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * bigCell k r' c' 1 * Matrix.of q.2 * Matrix.of q.1.2) X.2)
                ∂((μN'.prod μN').prod μb') := by
          congr 1
          refine lintegral_lintegral_swap ?_
          exact (((cW_meas k r').comp measurable_snd).mul m3.lintegral_prod_right').aemeasurable
      _ = (C₁ : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') *
            (((a * a * b : ℝ≥0) : ℝ≥0∞) * Kμ (TT (c, c'))) := by
          congr 1
          refine lintegral_congr fun c' => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          refine (key hCN μN' μb' hN' f hf c (bigCell k r' c' 1)).trans ?_
          rw [hae, hbe]
          exact lint_smul3 μN μb a b _
      _ = _ := by
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
          refine lintegral_congr fun c' => ?_
          exact mul_left_comm _ _ _

  let GG : ℂ × (Fin r' → ℂ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1‖ ^ (2 * (2 * r' + k + 1))) * (ENNReal.ofReal (cWeight k r' p.2) * Kμ (TT p))
  have hGG : Measurable GG :=
    Measurable.mul (by fun_prop) (((cW_meas k r').comp measurable_snd).mul (hKμ.comp hTT))
  have outer : ∫⁻ c : Fin (1 + r') → ℂ, ENNReal.ofReal (cWeight k (1 + r') c) *
        ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
          f ((Matrix.of p.1.1)⁻¹ * bigCell k (1 + r') c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) =
      ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') * Kμ (TT (c, c')) := by
    calc _ = ∫⁻ c : Fin (1 + r') → ℂ, GG (splitC r' c) := by
          refine lintegral_congr fun c => ?_
          show _ = ENNReal.ofReal (‖c (a0 r')‖ ^ (2 * (2 * r' + k + 1))) *
            (ENNReal.ofReal (cWeight k r' fun a => c (Fin.natAdd 1 a)) * Kμ (TT (splitC r' c)))
          rw [cWeight_rec, ENNReal.ofReal_mul (by positivity), mul_assoc, t_bigcellrec k r' c 1]
          rfl
      _ = ∫⁻ p : ℂ × (Fin r' → ℂ), GG p := lint_split r' GG
      _ = ∫⁻ c : ℂ, ∫⁻ c' : Fin r' → ℂ, GG (c, c') := lintegral_prod _ hGG.aemeasurable
      _ = _ := by
          refine lintegral_congr fun c => ?_
          exact lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))))
            (fun c' => ENNReal.ofReal (cWeight k r' c') * Kμ (TT (c, c'))) ENNReal.ofReal_ne_top
  rw [h0 f hf, outer]
  simp only [step]
  have e : ∀ (A : ℝ≥0) (w x : ℝ≥0∞), w * ((C₁ : ℝ≥0∞) * ((A : ℝ≥0∞) * x)) =
      ((C₁ * A : ℝ≥0) : ℝ≥0∞) * (w * x) := by
    intro A w x; rw [ENNReal.coe_mul]; ring
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, mul_assoc C₀ C₁]
end Formalism.FourierDecayAlt.P.LongWeylElement
