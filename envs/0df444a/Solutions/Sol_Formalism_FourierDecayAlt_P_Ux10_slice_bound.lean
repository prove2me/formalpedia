-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.slice_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:46.318126+00:00
-- url     : https://prove2.me/submissions/0766bd2e-0fa2-4ddc-b588-af5ce7d2be3e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_DjU_gaXi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_slice_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_one_le_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_dLR_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_one

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) (hC : DerivativeCost) (hS : CoordinateDecay)
    {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (hs : 1 ≤ s)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Set.Ioi 0) (m mm Q : ℕ) (A₁ : ℝ) (hQ : m + 1 + mm ≤ Q)
    (ha : 0 < a1 (p + s + ρ) A₁ m mm) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (p + s + ρ) → E) (B₁ : ℝ),
      Star k (p + s) ρ F₁ A₁ Q B₁ K → ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s), G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ,
      ∀ u v : List (B.Mat k ρ), unitW k ρ u → unitW k ρ v → u.length + v.length ≤ mm → ∀ q ≤ m + 1,
        ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) Z‖ ≤
          Cb * B₁ * ((1 + ‖Z‖) ^ (-a1 (p + s + ρ) A₁ m mm) * B.gN γ ^ (-a1 (p + s + ρ) A₁ m mm)) *
            wt ξ ^ (-a1 (p + s + ρ) A₁ m mm) := by
  set a := a1 (p + s + ρ) A₁ m mm with ha_def
  set R : ℝ := ((p + s + ρ : ℕ) : ℝ) with hRdef
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  set As := A₁ - 5 * R * ((m : ℝ) + 1) - 2 * R * (mm : ℝ) with hAsdef
  have hden : 0 < 8 * (2 * R + 1) := by positivity
  have hAa : As / (8 * (2 * R + 1)) = a := by rw [ha_def]; unfold a1; rfl
  have hAs0 : 0 ≤ As := by
    have : As = a * (8 * (2 * R + 1)) := by rw [← hAa]; field_simp
    rw [this]; positivity
  obtain ⟨C₃, hC₃⟩ := hC k p s ρ σ d hd hs K hK hK0 Q
  obtain ⟨C₂, hC₂⟩ := hS k p s ρ σ d hd hs K hK hK0 As hAs0
  refine ⟨|C₃| * |C₂|, by positivity, ?_⟩
  intro E _ _ F₁ B₁ hStar ξ Z hZ γ hγ u v hu hv hl q hq
  have hB₁ : 0 ≤ B₁ := by
    have := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one
    exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) this
  have hγ1 : 1 ≤ B.gN γ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hγ
  have hw1 : 1 ≤ wt ξ := one_le_wt ξ
  have hZ1 : 1 ≤ 1 + ‖Z‖ := by linarith [norm_nonneg Z]
  by_cases hKZ : ‖(hMat σ d).det * G.detM Z‖ ∈ K
  · obtain ⟨-, hb⟩ := hC₃ E F₁ A₁ B₁ hStar ξ u v q hu hv (by omega) Z γ hZ hγ
    have hg := gaXi_mem hM hR σ d hd ξ Z hZ hγ
    have hg1 : 1 ≤ B.gN (gaXi k ρ σ d ξ Z γ) := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have hDj : ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K := by rw [DjU_gaXi hZh]; exact hKZ
    have hs22 := hC₂ ξ Z γ hγ hDj
    have hexp : -A₁ + 5 * R * (q : ℝ) + 2 * R * ((u.length + v.length : ℕ) : ℝ) ≤ -As := by
      have hq' : (q : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hq
      have hl' : ((u.length + v.length : ℕ) : ℝ) ≤ (mm : ℝ) := by exact_mod_cast hl
      rw [hAsdef]; nlinarith
    calc _ ≤ C₃ * B₁ * B.gN (gaXi k ρ σ d ξ Z γ) ^
            (-A₁ + 5 * R * (q : ℝ) + 2 * R * ((u.length + v.length : ℕ) : ℝ)) := hb
      _ ≤ |C₃| * B₁ * B.gN (gaXi k ρ σ d ξ Z γ) ^ (-As) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hB₁) (Real.rpow_le_rpow_of_exponent_le hg1 hexp)
            (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ ≤ |C₃| * B₁ * (|C₂| * (wt ξ * (1 + ‖Z‖) * B.gN γ) ^ (-a)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hs22.trans ?_
          rw [hAa]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by positivity) _)
      _ = |C₃| * |C₂| * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN γ ^ (-a)) * wt ξ ^ (-a) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
          ring
  · have hO : IsOpen {Z' : G.Mat s | G.detM Z' ≠ 0 ∧ ‖(hMat σ d).det * G.detM Z'‖ ∉ K} := by
      have hc : Continuous (fun Z' : G.Mat s => G.detM Z') := by unfold G.detM; fun_prop
      exact (isOpen_ne_fun hc continuous_const).inter
        (hK.isClosed.isOpen_compl.preimage (continuous_norm.comp (continuous_const.mul hc)))
    have hev : (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) =ᶠ[𝓝 Z]
        fun _ => (0 : E) := by
      filter_upwards [hO.mem_nhds ⟨hZ, hKZ⟩] with Z' hZ'
      exact dLR_vanish (slice_vanish hM hR hZh σ d hd hStar ξ Z' hZ'.1 hZ'.2) u v hu hv γ hγ
    rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity
end Formalism.FourierDecayAlt.P.Ux10
