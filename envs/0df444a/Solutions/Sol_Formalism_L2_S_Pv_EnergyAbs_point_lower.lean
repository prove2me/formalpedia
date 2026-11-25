-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.point_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:12.708221+00:00
-- url     : https://prove2.me/submissions/db354287-bcc1-4d6e-b361-1a4a7c6cd76a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsPoint
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cpiece_compact
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cpiece_mono
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cpiece_cover
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_translate_props
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_approx_OO
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_hsA_Xop_translate
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_liminf_lower
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_quot_map_inv
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_sqrt_hsA_le_add_sub
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_tendsto_ratio_ennreal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem hilbertSchmidtSq_nonneg_aux_lemma (A : V' →L[ℂ] V) : 0 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  exact Finset.sum_nonneg fun i _ => sq_nonneg _
private theorem sq_max_le_hilbertSchmidtSq_lemma_2 (A B : V' →L[ℂ] V) {ε : ℝ}
    (h : Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA (A - B)) ≤ ε) :
    max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Formalism.L2.SG.Pf.EnergyAbs.hsA B := by
  have hB := hilbertSchmidtSq_nonneg_aux_lemma B
  have htri := sqrt_hsA_le_add_sub A B
  have hmax : max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) :=
    max_le (by linarith) (Real.sqrt_nonneg _)
  calc max (Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA A) - ε) 0 ^ 2 ≤ Real.sqrt (Formalism.L2.SG.Pf.EnergyAbs.hsA B) ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 2
    _ = Formalism.L2.SG.Pf.EnergyAbs.hsA B := Real.sq_sqrt hB
end Formalism.L2.S.Pv.EnergyAbs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    {w : HH} {S S' : Set G} {μS μS' ν ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')}
    {W : G → V} {W' : G → V'} [SFinite ν] [SFinite ν'] (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hq : IsQuot μ μS ν) (hq' : IsQuot μ μS' ν')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (Ω Ω' : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hΩ' : ∀ n, MeasurableSet (Ω' n) ∧ Ω' n ⊆ S' ∧ 0 < μS' (Ω' n) ∧ μS' (Ω' n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S → Tendsto (fun n =>
      (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1))
    (hF' : ∀ K : Set G, IsCompact K → K ⊆ S' → Tendsto (fun n =>
      (μS' {t | t ∈ Ω' n ∧ ∀ k ∈ K, k * t ∈ Ω' n}).toReal / (μS' (Ω' n)).toReal) atTop (𝓝 1))
    (hXc : ∀ n, Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g)))
    (γ : G) (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ)) ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ *
        ∫⁻ s, ∫⁻ s', ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹)))
          ∂μS' ∂μS) atTop := by
  have hS₀ := hS
  have hS'₀ := hS'
  obtain ⟨hSc, -, -, hinvS, hσS, -, h0S, -, -, -, hinvmS⟩ := hS₀
  obtain ⟨hSc', -, -, hinvS', hσS', -, h0S', -, -, -, hinvmS'⟩ := hS'₀
  have : SigmaFinite μS := hσS
  have : SigmaFinite μS' := hσS'
  have hm : μ = (ν.prod μS).map φinv := (quot_map_inv hq) hinvmS
  have hm' : μ = (ν'.prod μS').map φinv := (quot_map_inv hq') hinvmS'
  refine liminf_lower hinvmS hinvmS' Ω Ω'
    (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2) (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
    (fun n s s' => ENNReal.ofReal (Formalism.L2.SG.Pf.EnergyAbs.hsA
      (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) (s * γ * s'⁻¹))))
    (fun n => ?_) (Formalism.L2.SG.Pf.EnergyAbs.hsA (∫ x, Formalism.L2.SG.Pf.EnergyAbs.rk1A (W x) (W' (γ⁻¹ * x)) ∂μ))
    (hilbertSchmidtSq_nonneg_aux_lemma _) (fun ε hε => ?_)
  · exact ENNReal.measurable_ofReal.comp ((hXc n).measurable.comp
      ((continuous_fst.mul continuous_const).mul continuous_snd.inv).measurable)
  · obtain ⟨n₀, hn₀⟩ := approx_OO hσ hW hW' hinvS hinvS' h0S h0S' hm hm' γ hB
      (cpiece S) (cpiece S')
      (fun n => (cpiece_compact hSc n).isClosed.measurableSet)
      (fun n => (cpiece_compact hSc' n).isClosed.measurableSet)
      (cpiece_mono S) (cpiece_mono S')
      (cpiece_cover S) (cpiece_cover S') ε hε
    refine ⟨cpiece S n₀, cpiece S' n₀, ?_, ?_, ?_⟩
    · refine tendsto_ratio_ennreal (fun n => (hΩ n).2.2.1) (fun n => (hΩ n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω n ∧ _ from ht).1) ?_
      exact hF _ (cpiece_compact hSc n₀) Set.inter_subset_right
    · refine tendsto_ratio_ennreal (fun n => (hΩ' n).2.2.1) (fun n => (hΩ' n).2.2.2)
        (fun n => measure_mono fun t ht => (show t ∈ Ω' n ∧ _ from ht).1) ?_
      exact hF' _ (cpiece_compact hSc' n₀) Set.inter_subset_right
    · intro n s s' hs hs'
      have hs2 : s⁻¹ ∈ Ω n ∧ ∀ k ∈ cpiece S n₀, k * s⁻¹ ∈ Ω n := hs
      have hs2' : s'⁻¹ ∈ Ω' n ∧ ∀ k ∈ cpiece S' n₀, k * s'⁻¹ ∈ Ω' n := hs'
      have hsS : s ∈ S := by simpa using hinvS _ ((hΩ n).2.1 hs2.1)
      have hsS' : s' ∈ S' := by simpa using hinvS' _ ((hΩ' n).2.1 hs2'.1)
      obtain ⟨hAm, hAS, hAt⟩ := translate_props hS (hΩ n).1 (hΩ n).2.1 (hΩ n).2.2.2 hsS
      obtain ⟨hAm', hAS', hAt'⟩ :=
        translate_props hS' (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS'
      have happrox := hn₀ _ _ hAm hAS hAt hAm' hAS' hAt' (fun k hk => hs2.2 k hk)
        (fun k hk => hs2'.2 k hk)
      rw [hsA_Xop_translate hσ hS hS' hW hW' (hΩ n).1 (hΩ n).2.1
        (hΩ n).2.2.2 (hΩ' n).1 (hΩ' n).2.1 (hΩ' n).2.2.2 hsS hsS' γ]
      exact ENNReal.ofReal_le_ofReal (sq_max_le_hilbertSchmidtSq_lemma_2 _ _ happrox)
end Formalism.L2.S.Pv.EnergyAbs
