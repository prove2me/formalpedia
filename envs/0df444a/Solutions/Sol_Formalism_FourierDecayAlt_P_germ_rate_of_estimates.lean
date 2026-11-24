-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.germ_rate_of_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:55.167306+00:00
-- url     : https://prove2.me/submissions/d1c7b21d-ce59-4afd-b55b-d7f54e161086

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_derivBound_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_singleton_subset_detSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_critCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_farCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_critCut_mem_Icc
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_integrable_cut_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_abs_nonstationaryCutoff_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_root_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_root_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_inner_osc
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_norm_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_term
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_block_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_osc_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.GermRateOfSteps := by
  intro hOm hCut _hCrit hSD hRoot hTail hIn hNS hSt hAL hLI _hLC hLarge
  obtain ⟨C₀, C₂, hC₀, hNS⟩ := hNS
  obtain ⟨E₁, hSt⟩ := hSt
  obtain ⟨E₂, hAL⟩ := hAL
  refine ⟨E₁ + E₂ + 3 * (C₀ + 2) + 3, C₂ + 2, ?_⟩
  intro m β hβ Kc hKc h0
  obtain ⟨δ, hδ⟩ := hSD m Kc hKc h0
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hs : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hC₀' : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (((C₀ : ℝ) + 2) * ((m : ℝ) + 2)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 / ((C₀ : ℝ) * ((m : ℝ) + 2)) := by
    rw [hεdef]
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_right _ hs.le
    linarith
  have hε2 : ε ≤ 1 / (2 * ((m : ℝ) + 2)) := by
    rw [hεdef]
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_right _ hs.le
    linarith
  have hε3 : ε ≤ 1 := by
    refine hε2.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have hεinv : ∀ a : ℝ, a / ε = a * (((C₀ : ℝ) + 2) * ((m : ℝ) + 2)) := by
    intro a
    rw [hεdef]
    field_simp
  obtain ⟨c1, hTail⟩ := hTail m β
  obtain ⟨c2, t2, ht2, hNS⟩ := hNS m β hβ Kc hKc h0 δ ε hδ hεpos hε1
  obtain ⟨c3, t3, ht3, hSt⟩ := hSt m β hβ Kc hKc h0 δ ε hδ hεpos hε2
  obtain ⟨c4, t4, ht4, hAL⟩ := hAL m β Kc hKc h0 ε hεpos hε2
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℝ, t₀ = min (min t2 t3) (min t4 1) := ⟨_, rfl⟩
  have ht₀ : 0 < t₀ := by
    rw [ht₀def]; exact lt_min (lt_min ht2 ht3) (lt_min ht4 one_pos)
  obtain ⟨c5, hLarge⟩ := hLarge m β Kc hKc h0 t₀ ht₀
  obtain ⟨R, hR1, hR⟩ := root_bound (m := m) hKc
  refine ⟨|c5| + (|c1| + |c2| + ((m : ℝ) + 2) * (|c3| + R ^ (m + 1) * |c4|)), ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t c ht hD
  have hK : 0 ≤ K := K_nonneg hD hΦ
  have hτ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hKτ : 0 ≤ K * ‖t‖ := mul_nonneg hK hτ.le
  have hR0 : 0 ≤ R ^ (m + 1) := by positivity

  have hA' : (E₁ : ℝ) * ((m : ℝ) + 2) ^ 2 + (E₂ : ℝ) * ((m : ℝ) + 2) ^ 2 +
      3 * ((C₀ : ℝ) + 2) * ((m : ℝ) + 2) ^ 2 + 3 * ((m : ℝ) + 2) ^ 2 ≤ A := by
    refine le_trans (le_of_eq ?_) hA
    push_cast
    ring
  have hE₁ : 0 ≤ (E₁ : ℝ) * ((m : ℝ) + 2) ^ 2 := by positivity
  have hE₂ : 0 ≤ (E₂ : ℝ) * ((m : ℝ) + 2) ^ 2 := by positivity
  have hCC : 0 ≤ 3 * ((C₀ : ℝ) + 2) * ((m : ℝ) + 2) ^ 2 := by positivity
  have hq : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ 3 * ((m : ℝ) + 2) ^ 2 := by nlinarith
  have hA1 : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A := by linarith
  have hA0 : ((m : ℝ) + 1) * ((m : ℝ) + 4) < A := by linarith
  have hAt : ((m : ℝ) + 1) * ((m : ℝ) + 4) + (3 * (m : ℝ) + 4) / ε ≤ A := by
    rw [hεinv]
    have : (3 * (m : ℝ) + 4) * (((C₀ : ℝ) + 2) * ((m : ℝ) + 2)) ≤ 3 * ((C₀ : ℝ) + 2) * ((m : ℝ) + 2) ^ 2 := by
      have h1 : 0 ≤ ((C₀ : ℝ) + 2) * ((m : ℝ) + 2) := by positivity
      nlinarith
    linarith
  have hAs : (E₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A := by linarith
  have hAl : (E₂ : ℝ) * ((m : ℝ) + 2) ^ 2 + 3 * ((m : ℝ) + 2) / ε ≤ A := by
    rw [hεinv]
    have : 3 * ((m : ℝ) + 2) * (((C₀ : ℝ) + 2) * ((m : ℝ) + 2)) = 3 * ((C₀ : ℝ) + 2) * ((m : ℝ) + 2) ^ 2 := by ring
    have h3 : 0 ≤ 3 * ((m : ℝ) + 2) ^ 2 := by positivity
    linarith
  have hk1 : C₂ * (m + 2) ^ 2 ≤ k := by nlinarith
  have hk2 : 2 * (m + 1) + 2 ≤ k := by nlinarith
  have hk3 : 1 ≤ k := by omega
  by_cases hts : t₀ ≤ ‖t‖
  · have h1 := hLarge V Φ A K hA1 (derivBound_mono hΦ (Nat.zero_le k) subset_rfl) t c hts hD
    refine h1.trans ?_
    have h2 : c5 * K * ‖t‖ ≤ |c5| * (K * ‖t‖) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hKτ
    have h3 : 0 ≤ (|c1| + |c2| + ((m : ℝ) + 2) * (|c3| + R ^ (m + 1) * |c4|)) * (K * ‖t‖) := by positivity
    calc _ ≤ |c5| * (K * ‖t‖) := h2
      _ ≤ |c5| * (K * ‖t‖) + (|c1| + |c2| + ((m : ℝ) + 2) * (|c3| + R ^ (m + 1) * |c4|)) * (K * ‖t‖) := by linarith
      _ = _ := by ring
  · have hlt : ‖t‖ < t₀ := not_le.mp hts
    rw [ht₀def] at hlt
    have hl2 : ‖t‖ ≤ t2 := (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
    have hl3 : ‖t‖ ≤ t3 := (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
    have hl4 : ‖t‖ ≤ t4 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    have hl1 : ‖t‖ ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    obtain ⟨i1, i2, iosc, hI⟩ := inner_osc hOm hCut hIn (β := β) h0 hA0 hεpos.le hΦ ht hl1 hD
    obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = c * t ^ (m + 1) := ⟨_, rfl⟩
    rw [← hDdef] at hD iosc hI
    have hDne : D ≠ 0 := fun h => h0 (h ▸ hD)
    have hD'ne : (-1 : ℂ) ^ (m + 3) * D ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hDne
    obtain ⟨hmem, hcard⟩ := hRoot (m + 2) ((-1) ^ (m + 3) * D) (by omega)
    have hcard := hcard hD'ne

    have hO : OmBlock β (m + 1) Φ t c = OmBlock β (m + 1) (cutPhi (‖t‖ ^ (-ε)) Φ) t c +
        OmBlock β (m + 1) (cutPhiC (‖t‖ ^ (-ε)) Φ) t c := by
      unfold OmBlock
      rw [← integral_add i1 i2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => gr_block_split β (m + 1) _ Φ t c p)

    have ifar := integrable_cut_smul iosc (continuous_farCut m δ D) (abs_nonstationaryCutoff_le m δ D)
    have icrit : ∀ z : ℂ, Integrable (fun p : XY m => ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p)
        (muXY β m) := fun z =>
      integrable_cut_smul iosc (continuous_critCut δ z) (B := 1) fun x => by
        rw [abs_of_nonneg (critCut_mem_Icc δ z x).1]; exact (critCut_mem_Icc δ z x).2
    have hsplit : ∫ p : XY m, oscIn β m ε Φ D t p ∂(muXY β m) =
        ∫ p : XY m, ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) +
        ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D),
          ∫ p : XY m, ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) := by
      rw [← integral_finsetSum _ fun z _ => icrit z, ← integral_add ifar (integrable_finsetSum _ fun z _ => icrit z)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => gr_osc_split β m δ ε Φ D t p)
    have hT : ((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) =
        (((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) * ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
      ring
    have hrem : remainder β m (fun _ => 1) Φ t c =
        ((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) (cutPhiC (‖t‖ ^ (-ε)) Φ) t c +
        (((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) •
          ∫ p : XY m, ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) +
        ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D),
          ((((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) •
              ∫ p : XY m, ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) -
            ((m : ℂ) + 2)⁻¹ • ((((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * psi β (((m : ℂ) + 2) * z / t)) •
              OmLong β (m + 1) Φ z)) := by
      have h1 : ((‖t‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • OmBlock β (m + 1) (cutPhi (‖t‖ ^ (-ε)) Φ) t c =
          (((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) •
            ∫ p : XY m, ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) +
          ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), (((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) •
              ∫ p : XY m, ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) := by
        rw [hT, ← smul_smul, hI, hsplit, smul_add, Finset.smul_sum]
      unfold remainder mainTerm
      rw [← hDdef, hO, smul_add, h1, Finset.smul_sum, Finset.sum_sub_distrib]
      abel
    rw [hrem]

    have b1 := hTail V Φ A K ε t c hεpos hε3 hAt ht hl1
      (derivBound_mono hΦ (Nat.zero_le k) (singleton_subset_detSet (m := m) (hDdef ▸ hD)))
    have b2 := hNS V Φ A K k hA1 hk1 hΦ t c ht hl2 (hDdef ▸ hD)
    rw [← hDdef] at b2
    have b2' : ‖(((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) •
          ∫ p : XY m, ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m)‖ ≤ c2 * K * ‖t‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc _ ≤ (‖t‖ ^ (m + 1))⁻¹ * (c2 * K * ‖t‖ ^ (m + 2)) := mul_le_mul_of_nonneg_left b2 (by positivity)
        _ = _ := by field_simp; ring
    have b3 : ∀ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D),
        ‖((((‖t‖ ^ (m + 1))⁻¹ : ℝ) : ℂ) •
              ∫ p : XY m, ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) -
            ((m : ℂ) + 2)⁻¹ • ((((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * psi β (((m : ℂ) + 2) * z / t)) •
              OmLong β (m + 1) Φ z))‖ ≤ (|c3| + R ^ (m + 1) * |c4|) * (K * ‖t‖) := by
      intro z hz
      have hz' : z ^ (m + 2) = (-1) ^ (m + 3) * D := (hmem z).mp hz
      have hzne : z ≠ 0 := root_ne_zero h0 hD hz'
      have hζ : 0 < ‖z‖ := norm_pos_iff.mpr hzne
      have s3 := hSt V Φ A K k hAs hk2 hΦ t c z ht hl3 (hDdef ▸ hD) (hDdef ▸ hz')
      rw [← hDdef] at s3
      have s4 := hAL V Φ A K k hAl hk3 hΦ t D z ht hl4 hD hz'
      have s5 := hLI (m + 1) β z hzne V Φ
      have g := gr_term m _ _ _ _ (psi β (((m : ℂ) + 2) * z / t)) (gr_norm_psi _ _) ‖t‖ ‖z‖ (c3 * K) (c4 * K)
        hτ hζ s3 s4 s5
      refine g.trans ?_
      have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) := pow_le_pow_left₀ hζ.le (hR D hD z hz') _
      have u1 : c3 * K ≤ |c3| * K := mul_le_mul_of_nonneg_right (le_abs_self _) hK
      have u2 : ‖z‖ ^ (m + 1) * (c4 * K) ≤ R ^ (m + 1) * (|c4| * K) := by
        calc _ ≤ ‖z‖ ^ (m + 1) * (|c4| * K) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hK) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hzR (by positivity)
      calc _ ≤ (|c3| * K + R ^ (m + 1) * (|c4| * K)) * ‖t‖ :=
            mul_le_mul_of_nonneg_right (add_le_add u1 u2) hτ.le
        _ = _ := by ring
    have b3' := norm_sum_le_of_le _ b3
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at b3'
    refine (norm_add₃_le).trans ?_
    have v1 : c1 * K * ‖t‖ ≤ |c1| * (K * ‖t‖) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hKτ
    have v2 : c2 * K * ‖t‖ ≤ |c2| * (K * ‖t‖) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hKτ
    have v5 : 0 ≤ |c5| * (K * ‖t‖) := by positivity
    have hc2 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    rw [hc2] at b3'
    calc _ ≤ |c1| * (K * ‖t‖) + |c2| * (K * ‖t‖) +
          ((m : ℝ) + 2) * ((|c3| + R ^ (m + 1) * |c4|) * (K * ‖t‖)) :=
          add_le_add (add_le_add (b1.trans v1) (b2'.trans v2)) b3'
      _ ≤ |c5| * (K * ‖t‖) + (|c1| * (K * ‖t‖) + |c2| * (K * ‖t‖) +
          ((m : ℝ) + 2) * ((|c3| + R ^ (m + 1) * |c4|) * (K * ‖t‖))) := by linarith
      _ = _ := by ring
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
