-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.folner_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:30.804199+00:00
-- url     : https://prove2.me/submissions/d04e2dae-5be1-4dd0-9296-1728132cabb1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_ratio_le_one
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_ratio_nonneg
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_sumsq_div_eq
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_integrable
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_value
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cnt_measurable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH}
    {S : Set G} {μS ν : Measure G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hσ : IsUnitRep σ) (hSch : IsSchur μ σ d) (hw : ‖w‖ = 1) (hS : IsHaarSub S μS) (hν : SFinite ν)
    (hq : IsQuot μ μS ν) (hW : IsWAbs μ σ d w S τ ν W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤)
    (Ω : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S →
      Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS (Ω n)).toReal)
      atTop (𝓝 (1 / d)) := by
  have : SFinite ν := hν
  have : SigmaFinite μS := hS.2.2.2.2.1
  have hd : 0 < d := hSch.1
  have hWeq := hW.2.2.2.1
  have hτu := hW.2.2.1
  have hWc := hW.2.2.2.2.1
  have hW1 := hW.2.2.2.2.2.2.1
  have hS0 : μS Sᶜ = 0 := hS.2.2.2.2.2.2.1
  have hΦ := Fk_integrable hσ w hS0 hWeq hτu hWc hconv
  have hmeas : ∀ n, Measurable (fun x : G × G × G => rat μS (Ω n) x.2.2) := fun n =>
    (((cnt_measurable (μS := μS) (hΩ n).1).ennreal_toReal).div_const _).comp measurable_snd.snd
  have hr : ∀ n q, 0 ≤ rat μS (Ω n) q ∧ rat μS (Ω n) q ≤ 1 := by
    intro n q
    unfold rat cnt
    exact ⟨ratio_nonneg, ratio_le_one (fun t ht => ht.1) (hΩ n).2.2.2⟩
  have hbound : ∀ n (x : G × G × G), ‖rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2‖ ≤
      ‖Fk σ w W x.1 x.2.1 x.2.2‖ := by
    intro n x
    rw [norm_smul, Real.norm_of_nonneg (hr n x.2.2).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr n x.2.2).2
  have hint_r : ∀ n, Integrable (fun x : G × G × G => rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS)) := fun n =>
    hΦ.mono ((hmeas n).aestronglyMeasurable.smul hΦ.aestronglyMeasurable) (ae_of_all _ (hbound n))
  have hS_ae : ∀ᵐ x ∂(ν.prod (ν.prod μS)), x.2.2 ∈ S := by
    rw [ae_iff]
    have hset : {x : G × G × G | ¬ x.2.2 ∈ S} = Set.univ ×ˢ (Set.univ ×ˢ Sᶜ) := by
      ext x; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hS0, mul_zero, mul_zero]
  have hlim : Tendsto (fun n => ∫ x, rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2
      ∂(ν.prod (ν.prod μS))) atTop (𝓝 (∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖Fk σ w W x.1 x.2.1 x.2.2‖)
      (fun n => (hint_r n).aestronglyMeasurable) hΦ.norm (fun n => ae_of_all _ (hbound n)) ?_
    filter_upwards [hS_ae] with x hx
    have h1 : Tendsto (fun n => rat μS (Ω n) x.2.2) atTop (𝓝 1) := by
      have h0 := hF {x.2.2} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
      simpa [rat, cnt] using h0
    have h2 := h1.smul_const (Fk σ w W x.1 x.2.1 x.2.2)
    rwa [one_smul] at h2
  rw [Fk_value hσ hd hq hW hΦ] at hlim
  have hlim' : Tendsto (fun n => (((∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) /
      (μS (Ω n)).toReal : ℝ) : ℂ)) atTop (𝓝 ((1 / d : ℝ) : ℂ)) :=
    hlim.congr fun n => (sumsq_div_eq hσ hw hS hWeq hτu hWc hW1 (hΩ n).1 (hΩ n).2.1
      (hΩ n).2.2.2 (hint_r n)).symm
  have h3 := (Complex.continuous_re.tendsto _).comp hlim'
  simpa only [Function.comp_def, Complex.ofReal_re] using h3
end Formalism.L2.S.Pv.EnergyAbs
