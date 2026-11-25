-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.approx_OO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:34.735703+00:00
-- url     : https://prove2.me/submissions/9c0635a0-dcc8-4cd2-a40c-b0a1ff992392

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integrable_liftedRankOneKernel
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integral_liftedRankOneKernel
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_prod_restrict_four
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Xop_eq_integral
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_ae_mem_four
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_norm_hsC
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_sqrt_hsA_integral_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤)
    (C C' : ℕ → Set G) (hCm : ∀ n, MeasurableSet (C n)) (hC'm : ∀ n, MeasurableSet (C' n))
    (hCmono : Monotone C) (hC'mono : Monotone C') (hCS : S ⊆ ⋃ n, C n) (hC'S : S' ⊆ ⋃ n, C' n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀, ∀ A A' : Set G, MeasurableSet A → A ⊆ S → μS A < ⊤ → MeasurableSet A' → A' ⊆ S' → μS' A' < ⊤ →
      C n₀ ⊆ A → C' n₀ ⊆ A' →
      Real.sqrt (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ)) ≤ ε := by
  set P := (ν.prod μS).prod (ν'.prod μS') with hP
  have hK4 := integrable_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ X : V' →L[ℂ] V, Real.sqrt (hsA X) ≤ c * ‖X‖ :=
    ⟨‖hsC (V := V) (V' := V')‖, norm_nonneg _, fun X => by
      rw [← norm_hsC]
      exact ContinuousLinearMap.le_opNorm _ _⟩
  let Rn : ℕ → Set ((G × G) × (G × G)) := fun n => (Set.univ ×ˢ C n) ×ˢ (Set.univ ×ˢ C' n)
  have hRm : ∀ n, MeasurableSet (Rn n) := fun n =>
    (MeasurableSet.univ.prod (hCm n)).prod (MeasurableSet.univ.prod (hC'm n))
  have hanti : Antitone fun n => (Rn n)ᶜ := fun n m hnm =>
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl (hCmono hnm)) (Set.prod_mono subset_rfl (hC'mono hnm)))
  have hnull : P (⋂ n, (Rn n)ᶜ) = 0 := by
    have hae := ae_mem_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') h0 h0'
    rw [ae_iff] at hae
    refine measure_mono_null (fun p hp => ?_) hae
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hp
    rintro ⟨h1, h2⟩
    obtain ⟨n1, hn1⟩ := Set.mem_iUnion.mp (hCS h1)
    obtain ⟨n2, hn2⟩ := Set.mem_iUnion.mp (hC'S h2)
    exact hp (max n1 n2)
      ⟨⟨trivial, hCmono (le_max_left _ _) hn1⟩, ⟨trivial, hC'mono (le_max_right _ _) hn2⟩⟩
  have hT := tendsto_setIntegral_of_antitone (μ := P) (f := fun q => ‖K4 σ d w W W' γ q‖)
    (fun n => (hRm n).compl) hanti ⟨0, hK4.norm.integrableOn⟩
  rw [setIntegral_measure_zero _ hnull] at hT
  have hT' := hT.const_mul c
  rw [mul_zero] at hT'
  obtain ⟨n₀, hn₀⟩ := (hT'.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun A A' hA hAS hAf hA' hAS' hAf' hCA hC'A => ?_⟩
  have hR : MeasurableSet (((Set.univ : Set G) ×ˢ A) ×ˢ ((Set.univ : Set G) ×ˢ A')) :=
    (MeasurableSet.univ.prod hA).prod (MeasurableSet.univ.prod hA')
  have hX : Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in (Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'), K4 σ d w W W' γ q ∂P := by
    rw [Xop_eq_integral hσ hW hW' hinv hinv' hA hAS hAf hA' hAS' hAf' γ
      (by rw [prod_restrict_four]; exact hK4.restrict), prod_restrict_four]
    rfl
  have hdiff : ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P := by
    rw [← integral_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB, hX, setIntegral_compl hR hK4]
  have hsub : ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ ⊆ (Rn n₀)ᶜ :=
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl hCA) (Set.prod_mono subset_rfl hC'A))
  rw [hdiff]
  calc Real.sqrt (hsA (∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P))
      ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, Real.sqrt (hsA (K4 σ d w W W' γ q)) ∂P :=
        sqrt_hsA_integral_le _ hK4.restrict
    _ ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, c * ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => Real.sqrt_nonneg _)
          (hK4.norm.const_mul c).restrict (Filter.Eventually.of_forall fun q => hc _)
    _ = c * ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_const_mul c _
    _ ≤ c * ∫ q in (Rn n₀)ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hK4.norm.integrableOn
          (Filter.Eventually.of_forall fun q => norm_nonneg _) hsub.eventuallyLE) hc0
    _ ≤ ε := hn₀.le
end Formalism.L2.S.Pv.EnergyAbs
