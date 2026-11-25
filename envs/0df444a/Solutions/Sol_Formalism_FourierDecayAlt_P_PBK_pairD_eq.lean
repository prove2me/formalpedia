-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.pairD_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:44.557545+00:00
-- url     : https://prove2.me/submissions/eb5539f6-3c5e-4066-89cf-10fd2a68dab3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_psi_conj_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integrable_termZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_sum_rootSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_of_mem_rootSet_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_sum_rootSet_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) (x x' ρ : ℂ) (hρ : ρ ≠ 0) :
    pairD s β ε bt bt' x x' ρ = ∑ ζ ∈ G.rootSet s 1, ∫ z, termZ s β bt bt' x x' ρ ζ z := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hζ0 : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 0 := fun ζ hζ h0 => by
    have := norm_of_mem_rootSet_one hs hζ; rw [h0, norm_zero] at this; exact zero_ne_one this

  set Φ : ℂ → ℂ := fun z => ∑ ζ ∈ G.rootSet s 1,
    (conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x')) *
      (((‖ρ‖ ^ s : ℝ) : ℂ) * ⟪bt z, bt' (ζ * ρ * z)⟫_ℂ) with hΦ
  have hjac : ∀ z : ℂ, ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z =
      ∑ ζ ∈ G.rootSet s 1, termZ s β bt bt' x x' ρ ζ z := by
    intro z
    rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hn : ‖ζ * ρ * z‖ = ‖ρ‖ * ‖z‖ := by rw [norm_mul, norm_mul, hζn, one_mul]
    have hj : ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 = ((s : ℝ) * ‖z‖ ^ (s - 1)) ^ 2 := by
      rw [norm_mul, norm_inv, hε, inv_one, one_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hps : conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x') =
        G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) := by
      rw [psi_conj_mul]; congr 1; ring
    have hρs : ‖ρ‖ ^ s = ‖ρ‖ * ‖ρ‖ ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hj, hps]
    simp only [termZ, bz, inner_smul_left, inner_smul_right, Complex.conj_ofReal, smul_eq_mul, hn, hρs, mul_pow,
      Complex.real_smul]
    push_cast
    ring
  have hint : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z) := by
    simp_rw [hjac]
    exact integrable_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)
  obtain ⟨-, hch⟩ := integral_sum_rootSet s hs ε hε0 Φ hint

  have hD : ∀ D : ℂ, D ≠ 0 → ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ =
      ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    intro D hD0
    rw [inner_smul_right, mainD, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzs : z ^ s = ε * D := (mem_rootSet' hs).1 hz
    have hw : ε * D ≠ 0 := mul_ne_zero hε0 hD0
    have hrD : ε * (ρ ^ s * D) = ρ ^ s * (ε * D) := by ring
    rw [mainD, hrD, sum_rootSet_mul hs hw hzs rfl (pow_ne_zero _ hρ), inner_sum, Finset.mul_sum, hΦ]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  have hDae : (fun D => ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ) =ᵐ[volume]
      fun D => ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with D hD0
    exact hD D hD0
  rw [pairD, integral_congr_ae hDae, hch]
  simp_rw [hjac]
  exact integral_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)
end Formalism.FourierDecayAlt.P.PBK
