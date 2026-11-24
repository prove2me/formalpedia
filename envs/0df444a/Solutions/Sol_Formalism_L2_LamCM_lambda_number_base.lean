-- Prove2me | solution 1 for Formalism.L2.LamCM.lambda_number_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:40:05.167707+00:00
-- url     : https://prove2.me/submissions/8e9c229e-0789-4327-b528-911e3542dfc7

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_lambda_endomorphism
import Theorems.Thm_Formalism_L2_LamCM_finrank_pos_real
import Theorems.Thm_Formalism_L2_LamCM_degree_norm_base
import Theorems.Thm_Formalism_L2_LamCM_coeff_cauchy_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : LamNumber0 := by
  intro K _ _ g abelian₂ ℓ de La logOm V _ c G μ n S Rr h hcf hmem hS hRr hev
  obtain ⟨hNg, hNd⟩ := degree_norm_base K g abelian₂ ℓ de La logOm V c μ n h
  have hde := h.2.2.1
  have hℓ := h.2.1
  have hBpos : (0 : ℝ) < Rr ^ (∑ v, μ v) := pow_pos hRr _
  have hlen : ∀ σ, (lineNN de ℓ c μ n).len σ (MvPolynomial.coeff μ G) ≤ S σ * Rr ^ (∑ v, μ v) := by
    intro σ
    have hnv : ∀ v, 0 < (ℓ (c v)).n σ := fun v => (hℓ (c v)).2 σ
    have hdn : 0 < de.n σ ^ n := pow_pos (hde.2 σ) n
    have hC := coeff_cauchy_bound V (MvPolynomial.map σ G) (fun v => 1 / (ℓ (c v)).n σ)
      (S σ * Rr ^ (∑ v, μ v) / de.n σ ^ n) μ
      (fun v => one_div_pos.mpr (hnv v)) (fun z hz => by
        rw [le_div_iff₀ hdn]
        exact hev σ z (fun v => (le_div_iff₀ (hnv v)).mp (hz v)))
    rw [MvPolynomial.coeff_map, le_div_iff₀ hdn] at hC
    have hprod : ∏ v, (1 / (ℓ (c v)).n σ) ^ μ v = (∏ v, (ℓ (c v)).n σ ^ μ v)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp [one_div, inv_pow]
    rw [hprod] at hC
    simp only [MLine.len, lineNN, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow]
    calc ‖σ (MvPolynomial.coeff μ G)‖ * (de.n σ ^ n * (∏ v, (ℓ (c v)).n σ ^ μ v)⁻¹)
        = ‖σ (MvPolynomial.coeff μ G)‖ * (∏ v, (ℓ (c v)).n σ ^ μ v)⁻¹ * de.n σ ^ n := by ring
      _ ≤ S σ * Rr ^ (∑ v, μ v) := hC
  have hE := lambda_endomorphism K (lineNN de ℓ c μ n) (MvPolynomial.coeff μ G) S _ hNg hcf hmem hS hBpos hlen
  have hd := finrank_pos_real K
  have hlogB : Real.log (Rr ^ (∑ v, μ v)) = (∑ v, (μ v : ℝ)) * Real.log Rr := by
    rw [Real.log_pow]; push_cast; ring
  rw [le_div_iff₀ hd]
  have hN2 : (lineNN de ℓ c μ n).deg ≤
      ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) * Module.finrank ℚ K := by
    have := hNd
    simp only [MLine.ndeg] at this
    rwa [div_le_iff₀ hd] at this
  rw [hlogB] at hE
  nlinarith
end Formalism.L2.LamCM
