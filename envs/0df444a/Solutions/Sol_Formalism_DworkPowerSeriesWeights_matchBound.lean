-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.matchBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:45.0078+00:00
-- url     : https://prove2.me/submissions/0c864700-352d-4919-ab44-a18d25565717

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_matchings
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_intOp
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
namespace Formalism.DworkPowerSeriesWeights
private theorem norm_polar_le_one_of_norm_le_one {K : Type u} [NormedField K] [IsUltrametricDist K]
    {ι : Type} [Fintype ι] (c : ι → ι → K) (L L' : ι → K) (hc : ∀ x y, ‖c x y‖ ≤ 1)
    (hL : ∀ x, ‖L x‖ ≤ 1) (hL' : ∀ x, ‖L' x‖ ≤ 1) : ‖polar c L L'‖ ≤ 1 := by
  unfold polar
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun y _ => ?_)
  rw [norm_mul]
  refine mul_le_one₀ (hc x y) (norm_nonneg _) ?_
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)
  · rw [norm_mul]; exact mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)
private theorem norm_coeff_prod_linForm_le_one {K : Type u} [NormedField K] [IsUltrametricDist K]
    {ι : Type} [Fintype ι] {n : ℕ} (L : Fin n → ι → K) (hL : ∀ i x, ‖L i x‖ ≤ 1)
    (s : Finset (Fin n)) : ∀ m, ‖MvPolynomial.coeff m (∏ i ∈ s, linForm (L i))‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Finset.prod_empty, MvPolynomial.coeff_one]
    split_ifs <;> simp
  | @insert a s ha ih =>
    intro m
    rw [Finset.prod_insert ha, MvPolynomial.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun p _ => ?_)
    rw [norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ih p.2)
    unfold linForm
    rw [MvPolynomial.coeff_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', norm_mul]
    refine mul_le_one₀ (hL a x) (norm_nonneg _) ?_
    split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
end

set_option autoImplicit false
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : MatchBound.{u} := by
  unfold MatchBound
  intro K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM
  have hm : Matchings.{u} := matchings
  unfold Matchings at hm
  have hI : IntOp.{u} := intOp
  unfold IntOp at hI
  rw [hm K ι c S sg n L]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _) ?_
  intro σ hσ
  rw [Finset.mem_filter] at hσ
  by_cases hz : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0
  · have hcard := hM σ hσ.2 hz
    rw [norm_mul, norm_prod]
    have hJ := hI K ι sg hsg _
      (norm_coeff_prod_linForm_le_one L hL (Finset.univ.filter (fun i => σ i = i)))
    have hP : ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by
      calc ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖
          ≤ ∏ _i ∈ Finset.univ.filter (fun i => i < σ i), pi ^ (-(1 / 2 : ℝ)) := by
            refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
            rw [norm_mul, norm_neg]
            calc ‖S‖ * ‖polar c (L i) (L (σ i))‖ ≤ ‖S‖ * 1 :=
                  mul_le_mul_of_nonneg_left
                    (norm_polar_le_one_of_norm_le_one c (L i) (L (σ i)) hc (hL i) (hL (σ i))) (norm_nonneg _)
              _ ≤ pi ^ (-(1 / 2 : ℝ)) := by rw [mul_one]; exact hS
        _ = pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by
            rw [Finset.prod_const, Real.rpow_mul hpi0.le, Real.rpow_natCast]
    have hmono : pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) ≤
        pi ^ (-(1 / 2 : ℝ) * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le
      have : ((Finset.univ.filter (fun i => i < σ i)).card : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hcard
      linarith
    refine (mul_le_mul hP hJ (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)).trans ?_
    rw [mul_one]
    exact hmono
  · push_neg at hz
    obtain ⟨i, hi, hpol⟩ := hz
    have h0 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), (-S * polar c (L i) (L (σ i)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (by rw [hpol, mul_zero])
    rw [h0, zero_mul, norm_zero]
    exact Real.rpow_nonneg hpi0.le _
end Formalism.DworkPowerSeriesWeights
