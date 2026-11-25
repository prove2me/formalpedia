-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.phi_bound_parts_of_radical_and_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:48.359828+00:00
-- url     : https://prove2.me/submissions/b40e4593-433a-4bbc-9e48-76d1c3d67c4c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_gaXi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_pint
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_meas_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_exch_dLR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_int_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_gaXi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_psiStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_norm_psiStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_ckOn_slice
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_one_le_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_slice_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_fin_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_strictUpper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromRows
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromCols
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_lowW
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_ell
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_subS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_supS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerA
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerB
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.continuous_psi_comp
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_upper

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (hR : RadicalParam) (hZh : ZhSlice) : PointwiseIntegralBoundFromComponents := by
  intro hM hC hS hI k p s ρ σ d hd hs K hK hK0 m mm Q A₁ hQ ha
  set a := a1 (p + s + ρ) A₁ m mm with ha_def
  have hn0 : 0 ≤ 2 * ((p + s + ρ : ℕ) : ℝ) * ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) := by positivity
  have ha0 : 0 < a := lt_of_le_of_lt hn0 ha
  obtain ⟨Cb, hCb0, hbd⟩ := slice_bound hM hR hZh hC hS σ d hd hs hK hK0 m mm Q A₁ hQ ha0
  obtain ⟨C₃, hC₃⟩ := hC k p s ρ σ d hd hs K hK hK0 Q
  have hInt : Integrable (fun ξ : Xi k p s ρ σ => wt ξ ^ (-a)) (muXi k p s ρ σ) := hI k p s ρ σ a hs ha
  set I := ∫ ξ, wt ξ ^ (-a) ∂(muXi k p s ρ σ) with hIdef
  refine ⟨Cb * I, ?_⟩
  intro z z' E _ _ _ F₁ B₁ hStar
  have hB₁ : 0 ≤ B₁ := by
    have := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one
    exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) this
  have hψ : ∀ ξ, ‖psiStar k ρ σ z z' ξ‖ ≤ 1 := fun ξ => (norm_psiStar k ρ σ z z' ξ).le
  have : BorelSpace (XiH p s σ) := Prod.borelSpace
  have : BorelSpace (RC k (p + s) ρ × RC k (p + s) ρ) := Prod.borelSpace
  have : BorelSpace (Xi k p s ρ σ) := Prod.borelSpace
  have : SecondCountableTopology (Xi k p s ρ σ) := inferInstance
  have hψm : AEStronglyMeasurable (fun ξ => psiStar k ρ σ z z' ξ) (muXi k p s ρ σ) :=
    (cont_psiStar k ρ σ z z').aestronglyMeasurable
  have hck : ∀ ξ (Z : G.Mat s), G.detM Z ≠ 0 →
      B.CkOn ((mm : ℕ) : ℕ∞) (B.GV k ρ) (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) :=
    fun ξ Z hZ => ckOn_mono (by omega) (ckOn_slice hM hR σ d hd hStar.1 ξ Z hZ)
  have hcont1 : ContinuousOn F₁ (B.GV k (p + s + ρ)) :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono (by simp) hStar.1)
  have hmeas : ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ,
      AEStronglyMeasurable (fun ξ => F₁ (gaXi k ρ σ d ξ Z γ)) (muXi k p s ρ σ) := by
    intro Z hZ γ hγ
    exact (hcont1.comp_continuous (cont_gaXi hR σ d hd Z hZ γ)
      fun ξ => gaXi_mem hM hR σ d hd ξ Z hZ hγ).aestronglyMeasurable
  have hsm : ∀ ξ (e : E), ‖psiStar k ρ σ z z' ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hwt0 : ∀ ξ : Xi k p s ρ σ, 0 ≤ wt ξ ^ (-a) := fun ξ =>
    Real.rpow_nonneg (le_trans zero_le_one (one_le_wt ξ)) _
  have hTle : ∀ (Z : G.Mat s) (g : B.Mat k ρ), g ∈ B.GV k ρ → (1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a) ≤ 1 :=
    fun Z g hg => mul_le_one₀
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg Z]) (by linarith))
      (Real.rpow_nonneg (le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg) (by linarith))
  have hweak : ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (g : B.Mat k ρ), g ∈ B.GV k ρ →
      Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a)) * wt ξ ^ (-a) ≤ Cb * B₁ * wt ξ ^ (-a) := by
    intro ξ Z g hg
    have h1 := hTle Z g hg
    have h2 : 0 ≤ Cb * B₁ := mul_nonneg hCb0 hB₁
    calc Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a)) * wt ξ ^ (-a)
        ≤ Cb * B₁ * 1 * wt ξ ^ (-a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) (hwt0 ξ)
      _ = Cb * B₁ * wt ξ ^ (-a) := by ring
  have hbγ : ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ∀ u v : List (B.Mat k ρ), (∀ X ∈ u, B.unitLie k ρ X) →
      (∀ X ∈ v, B.unitLie k ρ X) → u.length + v.length ≤ mm → ∀ g ∈ B.GV k ρ, ∀ ξ,
      ‖B.dLR u v (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) g‖ ≤ Cb * B₁ * wt ξ ^ (-a) := by
    intro Z hZ u v hu hv hl g hg ξ
    have h0 := hbd E F₁ B₁ hStar ξ Z hZ g hg u v hu hv hl 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (hweak ξ Z g hg)
  have hβ : Integrable (fun ξ => Cb * B₁ * wt ξ ^ (-a)) (muXi k p s ρ σ) := hInt.const_mul _
  have hexch : ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ∀ u v : List (B.Mat k ρ), (∀ X ∈ u, B.unitLie k ρ X) →
      (∀ X ∈ v, B.unitLie k ρ X) → u.length + v.length ≤ mm → ∀ g ∈ B.GV k ρ,
      B.dLR u v (PhiFun k ρ σ d z z' F₁ Z) g =
        ∫ ξ, psiStar k ρ σ z z' ξ • B.dLR u v (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) g ∂(muXi k p s ρ σ) :=
    fun Z hZ => exch_dLR (μ := muXi k p s ρ σ) (fun ξ => psiStar k ρ σ z z' ξ) hψ hψm
      (fun ξ γ => F₁ (gaXi k ρ σ d ξ Z γ)) mm (fun ξ => hck ξ Z hZ) (fun g hg => hmeas Z hZ g hg) _ hβ (hbγ Z hZ)
  refine ⟨fun Z γ hZ hγ => ?_, fun Z hZ => ?_, fun u v hu hv hl γ hγ => ?_⟩
  · refine hβ.mono' (hψm.smul (hmeas Z hZ γ hγ)) (Eventually.of_forall fun ξ => ?_)
    exact (hsm ξ _).trans (hbγ Z hZ [] [] (by simp) (by simp) (by simp) γ hγ ξ)
  · refine ⟨int_ck (μ := muXi k p s ρ σ) (fun ξ => psiStar k ρ σ z z' ξ) hψ hψm
      (fun ξ γ => F₁ (gaXi k ρ σ d ξ Z γ)) mm (fun ξ => hck ξ Z hZ) (fun g hg => hmeas Z hZ g hg) _ hβ (hbγ Z hZ), ?_⟩
    intro u v hu hv hl g hg
    rw [hexch Z hZ u v hu hv hl g hg]
    have hb' : ∀ ξ, ‖psiStar k ρ σ z z' ξ • B.dLR u v (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) g‖ ≤
        Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a)) * wt ξ ^ (-a) := fun ξ => by
      refine (hsm ξ _).trans ?_
      have h0 := hbd E F₁ B₁ hStar ξ Z hZ g hg u v hu hv hl 0 (by omega)
      rwa [norm_iteratedFDeriv_zero] at h0
    have hnorm := norm_integral_le_of_norm_le (hInt.const_mul (Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a))))
      (Eventually.of_forall hb')
    rw [integral_const_mul] at hnorm
    have hg0 : 0 < B.gN g := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
    have := fin_step (c := Cb * B₁) (T := (1 + ‖Z‖) ^ (-a)) hg0 hnorm
    calc _ ≤ Cb * B₁ * I * (1 + ‖Z‖) ^ (-a) := this
      _ = Cb * I * B₁ * (1 + ‖Z‖) ^ (-a) := by ring
  · have hcD : Continuous (fun Z' : G.Mat s => G.detM Z') := by unfold G.detM; fun_prop
    have hUo : IsOpen {Z : G.Mat s | G.detM Z ≠ 0} := isOpen_ne_fun hcD continuous_const
    have hcda : ∀ ξ (i : ℕ), i ≤ m + 1 → ∀ Z' : G.Mat s, G.detM Z' ≠ 0 →
        ContDiffAt ℝ i (fun Z'' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) Z' :=
      fun ξ i hi Z' hZ' => (hC₃ E F₁ A₁ B₁ hStar ξ u v i hu hv (by omega) Z' γ hZ' hγ).1
    have hcd : ∀ ξ, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun Z' : G.Mat s => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ)
        {Z | G.detM Z ≠ 0} := fun ξ Z' hZ' =>
      ((hcda ξ (m + 1) le_rfl Z' hZ').const_smul (psiStar k ρ σ z z' ξ)).contDiffWithinAt
    have hmZ : ∀ Z' ∈ {Z : G.Mat s | G.detM Z ≠ 0}, AEStronglyMeasurable
        (fun ξ => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) (muXi k p s ρ σ) := by
      intro Z' hZ'
      refine hψm.smul ?_
      simp_rw [dLR_eq]
      exact meas_alt (fun ξ => hck ξ Z' hZ') (fun g hg => hmeas Z' hZ' g hg) _ (allLie_lr hu hv)
        (by rw [length_lr]; exact hl) γ hγ
    have hdf : ∀ ξ (i : ℕ), i ≤ m + 1 → ∀ Z' : G.Mat s, G.detM Z' ≠ 0 →
        ‖iteratedFDeriv ℝ i (fun Z'' : G.Mat s => psiStar k ρ σ z z' ξ •
          B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) Z'‖ ≤
          Cb * B₁ * ((1 + ‖Z'‖) ^ (-a) * B.gN γ ^ (-a)) * wt ξ ^ (-a) := by
      intro ξ i hi Z' hZ'
      have e := iteratedFDeriv_const_smul_apply (a := psiStar k ρ σ z z' ξ) (hcda ξ i hi Z' hZ')
      have e2 : (fun Z'' : G.Mat s => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) =
          psiStar k ρ σ z z' ξ • (fun Z'' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) := rfl
      rw [e2, e, norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)).trans
        (hbd E F₁ B₁ hStar ξ Z' hZ' γ hγ u v hu hv hl i hi)
    obtain ⟨hcont, hbnd⟩ := pint hUo (fun ξ => Cb * B₁ * wt ξ ^ (-a)) hβ (m + 1) E
      (fun ξ Z' => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) hcd hmZ
      (fun i hi Z' hZ' ξ => (hdf ξ i hi Z' hZ').trans (hweak ξ Z' γ hγ))
    have heqU : ∀ Z' ∈ {Z : G.Mat s | G.detM Z ≠ 0}, B.dLR u v (PhiFun k ρ σ d z z' F₁ Z') γ =
        ∫ ξ, psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ ∂(muXi k p s ρ σ) :=
      fun Z' hZ' => hexch Z' hZ' u v hu hv hl γ hγ
    refine ⟨hcont.congr heqU, fun q hq Z hZ => ?_⟩
    have hev : (fun Z' : G.Mat s => B.dLR u v (PhiFun k ρ σ d z z' F₁ Z') γ) =ᶠ[𝓝 Z]
        (fun Z' => ∫ ξ, psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ
          ∂(muXi k p s ρ σ)) := by
      filter_upwards [hUo.mem_nhds hZ] with Z' hZ' using heqU Z' hZ'
    rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds]
    have hn := hbnd q hq Z hZ _ (hInt.const_mul (Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN γ ^ (-a))))
      (fun ξ => hdf ξ q hq Z hZ)
    rw [integral_const_mul] at hn
    have hg0 : 0 < B.gN γ := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hγ)
    have := fin_step (c := Cb * B₁) (T := (1 + ‖Z‖) ^ (-a)) hg0 hn
    calc _ ≤ Cb * B₁ * I * (1 + ‖Z‖) ^ (-a) := this
      _ = Cb * I * B₁ * (1 + ‖Z‖) ^ (-a) := by ring
end Formalism.FourierDecayAlt.P.Ux10
