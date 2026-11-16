-- Prove2me | solution 1 for FairReplay.eq_138
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T22:20:05.31814+00:00
-- url     : https://prove2.me/submissions/5dbe88f7-718f-4d60-bfca-547c39874d5c

import Definitions.Def_FairReplay_armCount
import Mathlib
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditTrajectory
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.MeasureCompProd


namespace CommunityReplay_906eabbf_c33a_4814_8aa9_54b687d247bf
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal

namespace BanditAlgorithm

private def finiteStoppingPart {Ω : Type*} (τ : Ω → ℕ∞) (g : Ω → ℝ) (ω : Ω) : ℝ :=
  if τ ω = ⊤ then 0 else g ω

private lemma measurable_finiteStoppingPart
    {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ) {g : Ω → ℝ}
    (hg : Measurable[hτ.measurableSpace] g) :
    Measurable[⨆ n : ℕ, (hτ.min_const n).measurableSpace]
      (finiteStoppingPart τ g) := by
  intro s hs
  let mInf : MeasurableSpace Ω := ⨆ n : ℕ, (hτ.min_const n).measurableSpace
  have hlevel (n : ℕ) :
      MeasurableSet[mInf] (g ⁻¹' s ∩ {ω | τ ω = (n : ℕ∞)}) := by
    have hstop :
        MeasurableSet[hτ.measurableSpace] (g ⁻¹' s ∩ {ω | τ ω = (n : ℕ∞)}) :=
      (hg hs).inter (hτ.measurableSet_eq_of_countable' n)
    have hfil :
        MeasurableSet[ℱ n] (g ⁻¹' s ∩ {ω | τ ω = (n : ℕ∞)}) :=
      (hτ.measurableSet_inter_eq_iff (g ⁻¹' s) n).mp hstop
    exact (le_iSup (fun n : ℕ ↦ (hτ.min_const n).measurableSpace) n) _
      ((hτ.measurableSet_min_const_iff _).mpr ⟨hstop, hfil⟩)
  have hfinite :
      MeasurableSet[mInf] (⋃ n : ℕ, g ⁻¹' s ∩ {ω | τ ω = (n : ℕ∞)}) :=
    MeasurableSet.iUnion hlevel
  have htop :
      MeasurableSet[mInf] {ω | τ ω = ⊤} := by
    have hfinite_univ :
        MeasurableSet[mInf] (⋃ n : ℕ, ({ω | τ ω = (n : ℕ∞)} : Set Ω)) := by
      exact MeasurableSet.iUnion fun n ↦
        (le_iSup (fun n : ℕ ↦ (hτ.min_const n).measurableSpace) n) _
          ((hτ.measurableSet_min_const_iff _).mpr
            ⟨hτ.measurableSet_eq_of_countable' n,
              hτ.measurableSet_eq_of_countable n⟩)
    convert hfinite_univ.compl using 1
    ext ω
    cases hω : τ ω with
    | top => simp [hω]
    | coe n => simp [hω]
  by_cases hzero : (0 : ℝ) ∈ s
  · have heq :
        finiteStoppingPart τ g ⁻¹' s =
          {ω | τ ω = ⊤} ∪ ⋃ n : ℕ, g ⁻¹' s ∩ {ω | τ ω = (n : ℕ∞)} := by
      ext ω
      cases hω : τ ω with
      | top => simp [finiteStoppingPart, hω, hzero]
      | coe n => simp [finiteStoppingPart, hω]
    rw [heq]
    exact htop.union hfinite
  · have heq :
        finiteStoppingPart τ g ⁻¹' s =
          ⋃ n : ℕ, g ⁻¹' s ∩ {ω | τ ω = (n : ℕ∞)} := by
      ext ω
      cases hω : τ ω with
      | top => simp [finiteStoppingPart, hω, hzero]
      | coe n => simp [finiteStoppingPart, hω]
    rw [heq]
    exact hfinite

private def stoppedTruncationFiltration
    {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ) :
    Filtration ℕ hτ.measurableSpace where
  seq n := (hτ.min_const n).measurableSpace
  mono' i j hij :=
    IsStoppingTime.measurableSpace_mono (hτ.min_const i) (hτ.min_const j) fun ω ↦
      min_le_min_left (τ ω) (WithTop.coe_le_coe.mpr hij)
  le' n :=
    IsStoppingTime.measurableSpace_mono (hτ.min_const n) hτ fun ω ↦ min_le_left _ _

open _root_.CommunityReplay_906eabbf_c33a_4814_8aa9_54b687d247bf.BanditAlgorithm in
theorem _root_.CommunityReplay_906eabbf_c33a_4814_8aa9_54b687d247bf.solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    @klDiv (ℕ → Fin k × ℝ) hτ.measurableSpace
        ((banditTrajMeasure ν π).trim hτ.measurableSpace_le)
        ((banditTrajMeasure ν' π).trim hτ.measurableSpace_le) ≤
      ⨆ n : ℕ,
        @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
          ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
          ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) := by
  let P := banditTrajMeasure ν π
  let Q := banditTrajMeasure ν' π
  let PS : @Measure (ℕ → Fin k × ℝ) hτ.measurableSpace :=
    P.trim hτ.measurableSpace_le
  let QS : @Measure (ℕ → Fin k × ℝ) hτ.measurableSpace :=
    Q.trim hτ.measurableSpace_le
  let N : Set (ℕ → Fin k × ℝ) := {ω | τ ω = ⊤}
  have hNambient : MeasurableSet N := hτ.measurableSet_eq_top
  have hNstop : MeasurableSet[hτ.measurableSpace] N :=
    by
      have hu :
          MeasurableSet[hτ.measurableSpace]
            (⋃ n : ℕ, ({ω | τ ω = (n : ℕ∞)} : Set (ℕ → Fin k × ℝ))) :=
        MeasurableSet.iUnion fun n ↦ hτ.measurableSet_eq_of_countable' n
      convert hu.compl using 1
      ext ω
      cases hω : τ ω with
      | top => simp [N, hω]
      | coe n => simp [N, hω]
  have hPN : P N = 0 := by
    by_contra hPN
    have htopint : (∫⁻ _ω in N, (⊤ : ℝ≥0∞) ∂P) = ⊤ := by
      simp [hPN]
    have hle :
        (∫⁻ _ω in N, (⊤ : ℝ≥0∞) ∂P) ≤
          ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P := by
      rw [← lintegral_indicator hNambient]
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ N
      · have htau : τ ω = ⊤ := by simpa [N] using hω
        simp [hω, htau]
      · simp [hω]
    rw [htopint] at hle
    exact (ne_of_lt hfinite) (top_unique hle)
  have hPSN : PS N = 0 := by
    rw [show PS N = P N by
      exact trim_measurableSet_eq hτ.measurableSpace_le hNstop]
    exact hPN
  by_cases hac : PS ≪ QS
  · let g : (ℕ → Fin k × ℝ) → ℝ := fun ω ↦ (PS.rnDeriv QS ω).toReal
    let g₀ : (ℕ → Fin k × ℝ) → ℝ := finiteStoppingPart τ g
    have hrn_zero : g =ᵐ[QS.restrict N] 0 := by
      have hrn_zero_enn :
          (fun ω ↦ PS.rnDeriv QS ω) =ᵐ[QS.restrict N] 0 := by
        rw [EventuallyEq, ae_restrict_iff' hNstop]
        exact (setLIntegral_eq_zero_iff hNstop (Measure.measurable_rnDeriv PS QS)).mp
          (by rw [Measure.setLIntegral_rnDeriv' hac hNstop, hPSN])
      filter_upwards [hrn_zero_enn] with ω hω
      simp [g, hω]
    have hgg₀ : g =ᵐ[QS] g₀ := by
      rw [EventuallyEq, ae_restrict_iff' hNstop] at hrn_zero
      filter_upwards [hrn_zero] with ω hω
      by_cases htop : τ ω = ⊤
      · simpa [g₀, finiteStoppingPart, htop] using hω htop
      · simp [g₀, finiteStoppingPart, htop]
    let ℱτ := stoppedTruncationFiltration (banditFiltration k) τ hτ
    have hg₀_meas :
        StronglyMeasurable[⨆ n : ℕ, (ℱτ n : MeasurableSpace (ℕ → Fin k × ℝ))] g₀ := by
      apply Measurable.stronglyMeasurable
      exact
        measurable_finiteStoppingPart (banditFiltration k) τ hτ
          (Measure.measurable_rnDeriv PS QS).ennreal_toReal
    have hg₀_int : Integrable g₀ QS :=
      Measure.integrable_toReal_rnDeriv.congr hgg₀
    have hconv :
        ∀ᵐ ω ∂QS, Tendsto (fun n ↦ QS[g₀ | ℱτ n] ω) atTop (nhds (g₀ ω)) :=
      hg₀_int.tendsto_ae_condExp hg₀_meas
    let φ : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (klFun x)
    have hφ_meas (n : ℕ) :
        Measurable[hτ.measurableSpace] (fun ω ↦ φ (QS[g₀ | ℱτ n] ω)) := by
      have hc :
          Measurable[hτ.measurableSpace] (fun ω ↦ QS[g₀ | ℱτ n] ω) :=
        (stronglyMeasurable_condExp (μ := QS) (f := g₀)
          (m := (ℱτ n : MeasurableSpace (ℕ → Fin k × ℝ)))).measurable.mono
            (ℱτ.le n) le_rfl
      exact ENNReal.continuous_ofReal.measurable.comp
        (continuous_klFun.measurable.comp hc)
    have hfatou :
        (∫⁻ ω, φ (g₀ ω) ∂QS) ≤
          liminf (fun n ↦ ∫⁻ ω, φ (QS[g₀ | ℱτ n] ω) ∂QS) atTop := by
      calc
        (∫⁻ ω, φ (g₀ ω) ∂QS) =
            ∫⁻ ω, liminf (fun n ↦ φ (QS[g₀ | ℱτ n] ω)) atTop ∂QS := by
          apply lintegral_congr_ae
          filter_upwards [hconv] with ω hω
          have hkl :
              Tendsto (fun n ↦ klFun (QS[g₀ | ℱτ n] ω)) atTop
                (nhds (klFun (g₀ ω))) :=
            (continuous_klFun.tendsto _).comp hω
          have hof :
              Tendsto (fun n ↦ φ (QS[g₀ | ℱτ n] ω)) atTop
                (nhds (φ (g₀ ω))) :=
            (ENNReal.continuous_ofReal.tendsto _).comp hkl
          exact hof.liminf_eq.symm
        _ ≤ liminf (fun n ↦ ∫⁻ ω, φ (QS[g₀ | ℱτ n] ω) ∂QS) atTop :=
          lintegral_liminf_le hφ_meas
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    have hφgg₀ :
        (fun ω ↦ ENNReal.ofReal (klFun (g ω))) =ᵐ[QS]
          (fun ω ↦ φ (g₀ ω)) := by
      filter_upwards [hgg₀] with ω hω
      simp [φ, hω]
    rw [lintegral_congr_ae hφgg₀]
    have hseq (n : ℕ) :
        (∫⁻ ω, φ (QS[g₀ | ℱτ n] ω) ∂QS) =
          @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
            (P.trim (hτ.min_const n).measurableSpace_le)
            (Q.trim (hτ.min_const n).measurableSpace_le) := by
      let mn : MeasurableSpace (ℕ → Fin k × ℝ) :=
        (hτ.min_const n).measurableSpace
      have hmn : mn ≤ hτ.measurableSpace := ℱτ.le n
      have hacn : PS.trim hmn ≪ QS.trim hmn := hac.trim hmn
      have hrn := toReal_rnDeriv_trim hmn hac
      have hcond :
          QS[g | mn] =ᵐ[QS.trim hmn] QS[g₀ | mn] :=
        condExp_congr_ae_trim hmn hgg₀
      have hmeasn : Measurable[mn] (fun ω ↦ φ (QS[g₀ | mn] ω)) := by
        exact ENNReal.continuous_ofReal.measurable.comp
          (continuous_klFun.measurable.comp
            (stronglyMeasurable_condExp (μ := QS) (f := g₀) (m := mn)).measurable)
      have hnested :
          @klDiv (ℕ → Fin k × ℝ) mn (PS.trim hmn) (QS.trim hmn) =
            ∫⁻ ω, φ (QS[g₀ | mn] ω) ∂QS := by
        rw [klDiv_eq_lintegral_klFun_of_ac hacn]
        calc
          (∫⁻ ω, ENNReal.ofReal
              (klFun (((PS.trim hmn).rnDeriv (QS.trim hmn) ω).toReal))
              ∂QS.trim hmn) =
              ∫⁻ ω, φ (QS[g₀ | mn] ω) ∂QS.trim hmn := by
                apply lintegral_congr_ae
                filter_upwards [hrn, hcond] with ω h₁ h₂
                simp only [φ, g] at h₁ h₂ ⊢
                rw [h₁, h₂]
          _ = ∫⁻ ω, φ (QS[g₀ | mn] ω) ∂QS :=
            lintegral_trim hmn hmeasn
      symm
      simpa [mn, PS, QS, P, Q, trim_trim, ℱτ,
        stoppedTruncationFiltration] using hnested
    exact hfatou.trans <| (liminf_le_of_frequently_le' <|
      Frequently.of_forall fun n ↦ (hseq n).le.trans <| le_iSup
        (fun j : ℕ ↦
          @klDiv (ℕ → Fin k × ℝ) (hτ.min_const j).measurableSpace
            (P.trim (hτ.min_const j).measurableSpace_le)
            (Q.trim (hτ.min_const j).measurableSpace_le)) n)
  · have hex :
        ∃ A : Set (ℕ → Fin k × ℝ),
          MeasurableSet[hτ.measurableSpace] A ∧ QS A = 0 ∧ PS A ≠ 0 := by
      by_contra h
      apply hac
      refine Measure.AbsolutelyContinuous.mk ?_
      intro A hA hQA
      by_contra hPA
      exact h ⟨A, hA, hQA, hPA⟩
    obtain ⟨A, hA, hQA, hPA⟩ := hex
    let An : ℕ → Set (ℕ → Fin k × ℝ) :=
      fun n ↦ A ∩ {ω | τ ω ≤ (n : ℕ∞)}
    have hAn_stop (n : ℕ) :
        MeasurableSet[hτ.measurableSpace] (An n) :=
      hA.inter (hτ.measurableSet_le' n)
    have hAn (n : ℕ) :
        MeasurableSet[(hτ.min_const n).measurableSpace] (An n) :=
      (hτ.measurableSet_inter_le_const_iff A n).mp (hAn_stop n)
    have hexn : ∃ n : ℕ, PS (An n) ≠ 0 := by
      by_contra hn
      push Not at hn
      have hu : PS (⋃ n : ℕ, An n) = 0 := measure_iUnion_null hn
      have hsub : A ⊆ (⋃ n : ℕ, An n) ∪ N := by
        intro ω hωA
        cases hω : τ ω with
        | top =>
            exact Or.inr (by simp [N, hω])
        | coe n =>
            refine Or.inl ?_
            exact Set.mem_iUnion.2 ⟨n, hωA, by simp [hω]⟩
      exact hPA (measure_mono_null hsub (measure_union_null hu hPSN))
    obtain ⟨n, hPSAn⟩ := hexn
    let mn : MeasurableSpace (ℕ → Fin k × ℝ) :=
      (hτ.min_const n).measurableSpace
    have hmn : mn ≤ hτ.measurableSpace :=
      IsStoppingTime.measurableSpace_mono (hτ.min_const n) hτ fun ω ↦ min_le_left _ _
    have hnotacn : ¬ PS.trim hmn ≪ QS.trim hmn := by
      intro hacn
      apply hPSAn
      have hQAn : QS (An n) = 0 := measure_mono_null inter_subset_left hQA
      have htrimQ : (QS.trim hmn) (An n) = 0 := by
        rw [trim_measurableSet_eq hmn (hAn n)]
        exact hQAn
      have htrimP : (PS.trim hmn) (An n) = 0 := hacn htrimQ
      rwa [trim_measurableSet_eq hmn (hAn n)] at htrimP
    have hDtop :
        @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
          (P.trim (hτ.min_const n).measurableSpace_le)
          (Q.trim (hτ.min_const n).measurableSpace_le) = ⊤ := by
      simpa [mn, PS, QS, P, Q, trim_trim] using klDiv_of_not_ac hnotacn
    rw [klDiv_of_not_ac hac]
    have hle := le_iSup
      (fun j : ℕ ↦
        @klDiv (ℕ → Fin k × ℝ) (hτ.min_const j).measurableSpace
          (P.trim (hτ.min_const j).measurableSpace_le)
          (Q.trim (hτ.min_const j).measurableSpace_le)) n
    rwa [hDtop] at hle

end BanditAlgorithm

end
end CommunityReplay_906eabbf_c33a_4814_8aa9_54b687d247bf
noncomputable def BanditAlgorithm.klDiv_stopped_le_iSup_truncations := @CommunityReplay_906eabbf_c33a_4814_8aa9_54b687d247bf.solution

namespace CommunityReplay_793a2041_d387_42ca_9824_bcc8fc5b0403
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# Additivity of the Kullback-Leibler divergence over a measurable partition

`klDiv μ ν = klDiv (μ|_s) (ν|_s) + klDiv (μ|_sᶜ) (ν|_sᶜ)`.

This is the "localisation" step behind L&S Exercise 14.13 (printed p. 197): to compare the
divergences carried by two nested σ-algebras one splits the space along an event of the
smaller σ-algebra and compares the two halves separately.

Mathlib defines `klDiv μ ν = ENNReal.ofReal (∫ llr μ ν ∂μ + ν univ - μ univ)` (the
mass-corrected form), which is exactly what makes the divergence additive over a partition
for *finite*, not merely probability, measures.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α}

namespace InformationTheory

/-- If `μ ≪ ν`, the restriction of `μ` to `s` is the restriction of `ν` weighted by `dμ/dν`. -/
lemma restrict_eq_withDensity_rnDeriv (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    μ.restrict s = (ν.restrict s).withDensity (μ.rnDeriv ν) := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.restrict_restrict hA, Measure.restrict_apply hA,
    Measure.setLIntegral_rnDeriv hμν]

/-- On `s`, the log-likelihood ratio of the restricted measures agrees with the original one. -/
lemma llr_restrict_ae (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    llr (μ.restrict s) (ν.restrict s) =ᵐ[μ.restrict s] llr μ ν := by
  have hrn : (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
    rw [restrict_eq_withDensity_rnDeriv μ ν hμν s]
    exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv μ ν)
  have hac : μ.restrict s ≪ ν.restrict s := hμν.restrict s
  filter_upwards [hac hrn] with x hx
  simp only [llr_def, hx]

/-- The `klDiv` of a restricted pair, written with the original log-likelihood ratio. -/
lemma klDiv_restrict_eq (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (s : Set α) (hint : IntegrableOn (llr μ ν) s μ) :
    klDiv (μ.restrict s) (ν.restrict s) =
      ENNReal.ofReal (∫ x in s, llr μ ν x ∂μ + ν.real s - μ.real s) := by
  have hac : μ.restrict s ≪ ν.restrict s := hμν.restrict s
  have hcongr := llr_restrict_ae μ ν hμν s
  have hint' : Integrable (llr (μ.restrict s) (ν.restrict s)) (μ.restrict s) :=
    hint.congr hcongr.symm
  rw [klDiv_of_ac_of_integrable hac hint', integral_congr_ae hcongr]
  simp [measureReal_def, Measure.restrict_apply_univ]

end InformationTheory

open _root_.CommunityReplay_793a2041_d387_42ca_9824_bcc8fc5b0403.InformationTheory in
theorem solution (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    klDiv μ ν = klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) := by
  classical
  by_cases hμν : μ ≪ ν
  swap
  · -- Not absolutely continuous: both sides are `⊤`.
    rw [klDiv_of_not_ac hμν]
    have hnot : ¬ (μ.restrict s ≪ ν.restrict s ∧ μ.restrict sᶜ ≪ ν.restrict sᶜ) := by
      rintro ⟨h1, h2⟩
      refine hμν (Measure.AbsolutelyContinuous.mk fun A hA hνA ↦ ?_)
      have e1 : μ.restrict s A = 0 := h1 (by
        rw [Measure.restrict_apply hA]
        exact measure_mono_null inter_subset_left hνA)
      have e2 : μ.restrict sᶜ A = 0 := h2 (by
        rw [Measure.restrict_apply hA]
        exact measure_mono_null inter_subset_left hνA)
      rw [Measure.restrict_apply hA] at e1 e2
      have hsplit : μ (A ∩ s) + μ (A \ s) = μ A := measure_inter_add_diff (μ := μ) A hs
      rw [Set.diff_eq, e1, e2, zero_add] at hsplit
      exact hsplit.symm
    rcases not_and_or.mp hnot with h | h
    · rw [klDiv_of_not_ac h]; simp
    · rw [klDiv_of_not_ac h]; simp
  · by_cases hint : Integrable (llr μ ν) μ
    swap
    · -- Not integrable: the left side is `⊤`, and integrability on both halves would
      -- reassemble to integrability on the whole space.
      rw [klDiv_of_not_integrable hint]
      have hnot : klDiv (μ.restrict s) (ν.restrict s) = ⊤ ∨
          klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) = ⊤ := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨h1, h2⟩ := hcon
        have i1 := (klDiv_ne_top_iff.mp h1).2
        have i2 := (klDiv_ne_top_iff.mp h2).2
        have j1 : IntegrableOn (llr μ ν) s μ :=
          i1.congr (llr_restrict_ae μ ν hμν s)
        have j2 : IntegrableOn (llr μ ν) sᶜ μ :=
          i2.congr (llr_restrict_ae μ ν hμν sᶜ)
        have : IntegrableOn (llr μ ν) (s ∪ sᶜ) μ := j1.union j2
        rw [Set.union_compl_self, integrableOn_univ] at this
        exact hint this
      rcases hnot with h | h
      · rw [h]; simp
      · rw [h]; simp
    · -- Main case: split the integral and the masses along `s`.
      have j1 : IntegrableOn (llr μ ν) s μ := hint.integrableOn
      have j2 : IntegrableOn (llr μ ν) sᶜ μ := hint.integrableOn
      have hA : 0 ≤ ∫ x in s, llr μ ν x ∂μ + ν.real s - μ.real s := by
        have := integral_llr_add_sub_measure_univ_nonneg (hμν.restrict s)
          ((j1.congr (llr_restrict_ae μ ν hμν s).symm))
        rwa [integral_congr_ae (llr_restrict_ae μ ν hμν s),
          show (ν.restrict s).real univ = ν.real s by
            simp [measureReal_def, Measure.restrict_apply_univ],
          show (μ.restrict s).real univ = μ.real s by
            simp [measureReal_def, Measure.restrict_apply_univ]] at this
      have hB : 0 ≤ ∫ x in sᶜ, llr μ ν x ∂μ + ν.real sᶜ - μ.real sᶜ := by
        have := integral_llr_add_sub_measure_univ_nonneg (hμν.restrict sᶜ)
          ((j2.congr (llr_restrict_ae μ ν hμν sᶜ).symm))
        rwa [integral_congr_ae (llr_restrict_ae μ ν hμν sᶜ),
          show (ν.restrict sᶜ).real univ = ν.real sᶜ by
            simp [measureReal_def, Measure.restrict_apply_univ],
          show (μ.restrict sᶜ).real univ = μ.real sᶜ by
            simp [measureReal_def, Measure.restrict_apply_univ]] at this
      rw [klDiv_of_ac_of_integrable hμν hint,
        klDiv_restrict_eq μ ν hμν s j1, klDiv_restrict_eq μ ν hμν sᶜ j2,
        ← ENNReal.ofReal_add hA hB]
      congr 1
      have hsplit : ∫ x in s, llr μ ν x ∂μ + ∫ x in sᶜ, llr μ ν x ∂μ = ∫ x, llr μ ν x ∂μ :=
        integral_add_compl hs hint
      have hν : ν.real s + ν.real sᶜ = ν.real univ :=
        measureReal_add_measureReal_compl (μ := ν) hs
      have hμ : μ.real s + μ.real sᶜ = μ.real univ :=
        measureReal_add_measureReal_compl (μ := μ) hs
      linarith [hsplit, hν, hμ]

end
end CommunityReplay_793a2041_d387_42ca_9824_bcc8fc5b0403
noncomputable def InformationTheory.klDiv_restrict_add_klDiv_restrict_compl := @CommunityReplay_793a2041_d387_42ca_9824_bcc8fc5b0403.solution

namespace CommunityReplay_d6955138_4196_47db_93bd_29222b212e60
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# A σ-algebra that adds no information on a full-measure set does not change the divergence

If `m₁ ≤ m₂`, all the mass of `μ` and `ν` sits on `S`, and every `m₂`-set meets `S` in an
`m₁`-set (the two σ-algebras have the same trace on `S`), then
`klDiv_{m₂} μ ν ≤ klDiv_{m₁} (μ.trim) (ν.trim)`.

Together with the data-processing inequality this is an equality; only `≤` is recorded here,
since that is the direction that is not already available.

This is the half of L&S Exercise 14.13 (printed p. 197) that says the stopped σ-algebras
`F_{τ∧(n+1)}` and `F_{τ∧n}` carry the same information on the event `{τ ≤ n}`, where the
learner has already stopped and no further observation is made.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

variable {α : Type*}

theorem solution {m₁ m₂ : MeasurableSpace α} (h : m₁ ≤ m₂)
    (μ ν : @Measure α m₂) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set α} (hμS : μ Sᶜ = 0) (hνS : ν Sᶜ = 0)
    (htrace : ∀ A, MeasurableSet[m₂] A → MeasurableSet[m₁] (A ∩ S)) :
    @klDiv α m₂ μ ν ≤ @klDiv α m₁ (μ.trim h) (ν.trim h) := by
  classical
  by_cases hac : (μ.trim h) ≪ (ν.trim h)
  swap
  · rw [klDiv_of_not_ac hac]; exact le_top
  by_cases hint : Integrable (llr (μ.trim h) (ν.trim h)) (μ.trim h)
  swap
  · rw [klDiv_of_not_integrable hint]; exact le_top
  -- `S` itself is measurable, being `univ ∩ S`.
  have hS₁ : MeasurableSet[m₁] S := by simpa using htrace univ MeasurableSet.univ
  have hS₂ : MeasurableSet[m₂] S := h _ hS₁
  -- `g` is the `m₁`-density; we show it is also the `m₂`-density.
  set g : α → ℝ≥0∞ := (μ.trim h).rnDeriv (ν.trim h) with hg
  have hg_meas : Measurable[m₁] g := Measure.measurable_rnDeriv _ _
  have hg_meas₂ : Measurable[m₂] g := hg_meas.mono h le_rfl
  have hdiff : ∀ (ρ : @Measure α m₂) (A : Set α), ρ Sᶜ = 0 → ρ (A \ S) = 0 := fun ρ A hρ ↦
    measure_mono_null (fun x hx hxS ↦ hx.2 hxS) hρ
  have hμ_eq : ∀ A, MeasurableSet[m₂] A → μ A = μ (A ∩ S) := by
    intro A hA
    rw [← measure_inter_add_diff A hS₂, hdiff μ A hμS, add_zero]
  have hν_eq : ∀ A, MeasurableSet[m₂] A → ν A = ν (A ∩ S) := by
    intro A hA
    rw [← measure_inter_add_diff A hS₂, hdiff ν A hνS, add_zero]
  -- the key step: `g` is a density for `μ` with respect to `ν` on all of `m₂`
  have key : μ = ν.withDensity g := by
    ext A hA
    have hAS : MeasurableSet[m₁] (A ∩ S) := htrace A hA
    have hAS₂ : MeasurableSet[m₂] (A ∩ S) := h _ hAS
    have hsets : (A ∩ S : Set α) =ᵐ[ν] A := by
      rw [ae_eq_set]
      constructor
      · exact measure_mono_null (fun x hx ↦ absurd hx.1.1 hx.2) hνS
      · exact measure_mono_null (fun x hx hxS ↦ hx.2 ⟨hx.1, hxS⟩) hνS
    calc μ A = μ (A ∩ S) := hμ_eq A hA
      _ = (μ.trim h) (A ∩ S) := (trim_measurableSet_eq h hAS).symm
      _ = ∫⁻ x in A ∩ S, g x ∂(ν.trim h) := (Measure.setLIntegral_rnDeriv hac _).symm
      _ = ∫⁻ x, (A ∩ S).indicator g x ∂(ν.trim h) := by rw [lintegral_indicator hAS]
      _ = ∫⁻ x, (A ∩ S).indicator g x ∂ν := lintegral_trim h (hg_meas.indicator hAS)
      _ = ∫⁻ x in A ∩ S, g x ∂ν := by rw [lintegral_indicator hAS₂]
      _ = ∫⁻ x in A, g x ∂ν := setLIntegral_congr hsets
      _ = (ν.withDensity g) A := (withDensity_apply g hA).symm
  -- transfer absolute continuity, the log-likelihood ratio and integrability across the trim
  have hac₂ : μ ≪ ν := by rw [key]; exact withDensity_absolutelyContinuous ν g
  have hrn : μ.rnDeriv ν =ᵐ[ν] g := by
    rw [key]; exact Measure.rnDeriv_withDensity ν hg_meas₂
  have hllr : llr μ ν =ᵐ[μ] fun x ↦ Real.log (g x).toReal := by
    filter_upwards [hac₂ hrn] with x hx
    simp only [llr_def, hx]
  have hllr_trim : llr (μ.trim h) (ν.trim h) = fun x ↦ Real.log (g x).toReal := rfl
  have hint₂ : Integrable (llr μ ν) μ := by
    refine Integrable.congr ?_ hllr.symm
    have : Integrable (fun x ↦ Real.log (g x).toReal) (μ.trim h) := by
      rwa [hllr_trim] at hint
    exact integrable_of_integrable_trim h this
  -- both divergences are the same `ofReal`
  rw [klDiv_of_ac_of_integrable hac₂ hint₂, klDiv_of_ac_of_integrable hac hint]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  have hint_i : ∫ x, llr μ ν x ∂μ = ∫ x, llr (μ.trim h) (ν.trim h) x ∂(μ.trim h) := by
    rw [hllr_trim, integral_congr_ae hllr]
    exact integral_trim (μ := μ) h ((hg_meas.ennreal_toReal.log).stronglyMeasurable)
  have hμuniv : (μ.trim h).real univ = μ.real univ := by
    simp [measureReal_def, trim_measurableSet_eq h MeasurableSet.univ]
  have hνuniv : (ν.trim h).real univ = ν.real univ := by
    simp [measureReal_def, trim_measurableSet_eq h MeasurableSet.univ]
  rw [hint_i, hμuniv, hνuniv]

end
end CommunityReplay_d6955138_4196_47db_93bd_29222b212e60
noncomputable def InformationTheory.klDiv_le_klDiv_trim_of_trace_eq := @CommunityReplay_d6955138_4196_47db_93bd_29222b212e60.solution

namespace CommunityReplay_0ff0a9b8_f87d_4104_be12_aca651b2bc01
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# Data-processing inequality for the Kullback-Leibler divergence, for finite measures

`klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν` for finite measures `μ`, `ν`.

This is L&S Exercise 14.10 (printed p. 196). The probability-measure case is already available;
the extension to finite measures is what one needs as soon as the space is split along an event,
since restricting a probability measure to a proper subset leaves a sub-probability measure.

The argument is the standard one: the density on the coarse σ-algebra is the conditional
expectation of the density on the fine one, and `klFun` is convex, so conditional Jensen applies.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem solution {α : Type*} {m m₀ : MeasurableSpace α}
    (hm : m ≤ m₀) (μ ν : @Measure α m₀)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    @klDiv α m (μ.trim hm) (ν.trim hm) ≤ @klDiv α m₀ μ ν := by
  letI : @IsFiniteMeasure α m (μ.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top μ univ⟩
  letI : @IsFiniteMeasure α m (ν.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top ν univ⟩
  by_cases htop : klDiv μ ν = ⊤
  · simp [htop]
  have hac : μ ≪ ν := (klDiv_ne_top_iff.mp htop).1
  have hint : Integrable (llr μ ν) μ := (klDiv_ne_top_iff.mp htop).2
  have hactrim : μ.trim hm ≪ ν.trim hm := hac.trim hm
  -- the fine density and its conditional expectation
  set f : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal with hf
  have hfint : Integrable f ν := Measure.integrable_toReal_rnDeriv
  have hphiint : Integrable (fun x ↦ klFun (f x)) ν :=
    (integrable_klFun_rnDeriv_iff hac).2 hint
  have hjensen : (fun x ↦ klFun (ν[f | m] x)) ≤ᵐ[ν] ν[fun x ↦ klFun (f x) | m] := by
    simpa [Function.comp_def] using
      (convexOn_klFun.map_condExp_le hm
        continuous_klFun.continuousOn.lowerSemicontinuousOn
        (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)
        isClosed_Ici hfint hphiint)
  have hcondphi : Integrable (ν[fun x ↦ klFun (f x) | m]) ν := integrable_condExp
  have hnonneg : 0 ≤ᵐ[ν] (fun x ↦ klFun (ν[f | m] x)) := by
    filter_upwards [condExp_nonneg (μ := ν) (f := f) (m := m)
      (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)] with x hx
    exact klFun_nonneg hx
  have hleftmeas : StronglyMeasurable[m] (fun x ↦ klFun (ν[f | m] x)) :=
    continuous_klFun.comp_stronglyMeasurable
      (stronglyMeasurable_condExp (μ := ν) (f := f) (m := m))
  have hleftint : Integrable (fun x ↦ klFun (ν[f | m] x)) ν :=
    Integrable.mono' hcondphi (hleftmeas.mono hm).aestronglyMeasurable
      (by
        filter_upwards [hjensen, hnonneg] with x hle hnn
        simpa [abs_of_nonneg hnn] using hle)
  have hrn := toReal_rnDeriv_trim hm hac
  -- the coarse divergence is finite too
  have htrimtop : @klDiv α m (μ.trim hm) (ν.trim hm) ≠ ⊤ := by
    refine klDiv_ne_top hactrim ?_
    rw [← integrable_klFun_rnDeriv_iff hactrim]
    refine (hleftint.trim hm hleftmeas).congr ?_
    filter_upwards [hrn] with x hx
    exact congrArg klFun hx.symm
  rw [← ENNReal.toReal_le_toReal htrimtop htop,
    toReal_klDiv_eq_integral_klFun hactrim, toReal_klDiv_eq_integral_klFun hac]
  calc ∫ x, klFun (((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) ∂ν.trim hm
      = ∫ x, klFun (ν[f | m] x) ∂ν.trim hm := by
        refine integral_congr_ae ?_
        filter_upwards [hrn] with x hx
        exact congrArg klFun hx
    _ = ∫ x, klFun (ν[f | m] x) ∂ν := (integral_trim (μ := ν) hm hleftmeas).symm
    _ ≤ ∫ x, ν[fun x ↦ klFun (f x) | m] x ∂ν := integral_mono_ae hleftint hcondphi hjensen
    _ = ∫ x, klFun (f x) ∂ν := integral_condExp hm

end
end CommunityReplay_0ff0a9b8_f87d_4104_be12_aca651b2bc01
noncomputable def InformationTheory.klDiv_trim_le_of_isFiniteMeasure := @CommunityReplay_0ff0a9b8_f87d_4104_be12_aca651b2bc01.solution

namespace CommunityReplay_50679f25_ec9c_4d36_8aec_9909731ed4aa
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# Relative entropy between push-forward measures

For a measurable `φ : α → β`, the divergence between the push-forwards of `μ` and `ν` along `φ`
equals the divergence computed on the σ-algebra `φ` generates:

`klDiv (μ.map φ) (ν.map φ) = klDiv (μ.trim hφ.comap_le) (ν.trim hφ.comap_le)`.

This is L&S Exercise 14.9 (printed p. 195). It is the bridge between "observe a random element"
and "restrict to a sub-σ-algebra": the two ways of forgetting information agree.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem solution {φ : α → β} (hφ : Measurable φ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map φ) (ν.map φ) =
      @klDiv α (mβ.comap φ) (μ.trim hφ.comap_le) (ν.trim hφ.comap_le) := by
  classical
  haveI : IsFiniteMeasure (μ.map φ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]; exact measure_lt_top μ _⟩
  haveI : IsFiniteMeasure (ν.map φ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]; exact measure_lt_top ν _⟩
  haveI : @IsFiniteMeasure α (mβ.comap φ) (μ.trim hφ.comap_le) :=
    ⟨by rw [trim_measurableSet_eq hφ.comap_le MeasurableSet.univ]; exact measure_lt_top μ univ⟩
  haveI : @IsFiniteMeasure α (mβ.comap φ) (ν.trim hφ.comap_le) :=
    ⟨by rw [trim_measurableSet_eq hφ.comap_le MeasurableSet.univ]; exact measure_lt_top ν univ⟩
  -- the trimmed measure is the preimage measure
  have htrim : ∀ (ρ : Measure α) (B : Set β), MeasurableSet B →
      (ρ.trim hφ.comap_le) (φ ⁻¹' B) = (ρ.map φ) B := by
    intro ρ B hB
    rw [trim_measurableSet_eq hφ.comap_le ⟨B, hB, rfl⟩, Measure.map_apply hφ hB]
  by_cases hac : (μ.map φ) ≪ (ν.map φ)
  swap
  · -- both sides are `⊤`
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac]
    intro hac'
    refine hac (Measure.AbsolutelyContinuous.mk fun B hB hνB ↦ ?_)
    rw [← htrim μ B hB]
    exact hac' (by rw [htrim ν B hB]; exact hνB)
  -- the density on the comap σ-algebra is the pulled-back density
  set g : β → ℝ≥0∞ := (μ.map φ).rnDeriv (ν.map φ) with hg
  have hg_meas : Measurable g := Measure.measurable_rnDeriv _ _
  have hgφ_meas : Measurable[mβ.comap φ] (g ∘ φ) := hg_meas.comp (Measurable.of_comap_le le_rfl)
  have key : μ.trim hφ.comap_le = (ν.trim hφ.comap_le).withDensity (g ∘ φ) := by
    refine @Measure.ext _ (mβ.comap φ) _ _ (fun A hA ↦ ?_)
    obtain ⟨B, hB, rfl⟩ := hA
    have hpre : MeasurableSet[mβ.comap φ] (φ ⁻¹' B) := ⟨B, hB, rfl⟩
    rw [withDensity_apply _ hpre, htrim μ B hB]
    calc (μ.map φ) B = ∫⁻ y in B, g y ∂(ν.map φ) := (Measure.setLIntegral_rnDeriv hac _).symm
      _ = ∫⁻ y, B.indicator g y ∂(ν.map φ) := by rw [lintegral_indicator hB]
      _ = ∫⁻ x, B.indicator g (φ x) ∂ν := by
            rw [lintegral_map (hg_meas.indicator hB) hφ]
      _ = ∫⁻ x, (φ ⁻¹' B).indicator (g ∘ φ) x ∂ν := by
            refine lintegral_congr fun x ↦ ?_
            by_cases hx : φ x ∈ B <;> simp [Set.indicator_apply, hx, Function.comp]
      _ = ∫⁻ x, (φ ⁻¹' B).indicator (g ∘ φ) x ∂(ν.trim hφ.comap_le) :=
            (lintegral_trim hφ.comap_le (hgφ_meas.indicator hpre)).symm
      _ = ∫⁻ x in φ ⁻¹' B, (g ∘ φ) x ∂(ν.trim hφ.comap_le) := by
            rw [lintegral_indicator hpre]
  -- transfer absolute continuity and the log-likelihood ratio
  have hac₂ : μ.trim hφ.comap_le ≪ ν.trim hφ.comap_le := by
    rw [key]; exact withDensity_absolutelyContinuous _ _
  have hrn : (μ.trim hφ.comap_le).rnDeriv (ν.trim hφ.comap_le) =ᵐ[ν.trim hφ.comap_le] g ∘ φ := by
    rw [key]; exact Measure.rnDeriv_withDensity _ hgφ_meas
  have hllr : llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le)
      =ᵐ[μ.trim hφ.comap_le] fun x ↦ Real.log ((g ∘ φ) x).toReal := by
    filter_upwards [hac₂ hrn] with x hx
    simp only [llr_def, hx]
  -- integrability matches on both sides
  have hint_iff : Integrable (llr (μ.map φ) (ν.map φ)) (μ.map φ) ↔
      Integrable (llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le)) (μ.trim hφ.comap_le) := by
    constructor
    · intro hI
      refine Integrable.congr ?_ hllr.symm
      have h1 : Integrable (fun x ↦ Real.log (g (φ x)).toReal) μ := by
        rw [show (fun x ↦ Real.log (g (φ x)).toReal) = (fun y ↦ Real.log (g y).toReal) ∘ φ from rfl]
        exact (integrable_map_measure
          ((hg_meas.ennreal_toReal.log).aestronglyMeasurable) hφ.aemeasurable).mp hI
      exact h1.trim hφ.comap_le (hgφ_meas.ennreal_toReal.log).stronglyMeasurable
    · intro hI
      have h1 : Integrable (fun x ↦ Real.log ((g ∘ φ) x).toReal) (μ.trim hφ.comap_le) :=
        hI.congr hllr
      have h2 : Integrable (fun x ↦ Real.log ((g ∘ φ) x).toReal) μ :=
        integrable_of_integrable_trim hφ.comap_le h1
      exact (integrable_map_measure
        ((hg_meas.ennreal_toReal.log).aestronglyMeasurable) hφ.aemeasurable).mpr h2
  by_cases hint : Integrable (llr (μ.map φ) (ν.map φ)) (μ.map φ)
  swap
  · rw [klDiv_of_not_integrable hint, klDiv_of_not_integrable (fun h ↦ hint (hint_iff.mpr h))]
  rw [klDiv_of_ac_of_integrable hac hint,
    klDiv_of_ac_of_integrable hac₂ (hint_iff.mp hint)]
  congr 1
  have hI : ∫ y, llr (μ.map φ) (ν.map φ) y ∂(μ.map φ)
      = ∫ x, llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le) x ∂(μ.trim hφ.comap_le) := by
    have e1 : ∫ y, llr (μ.map φ) (ν.map φ) y ∂(μ.map φ) = ∫ x, Real.log ((g ∘ φ) x).toReal ∂μ :=
      integral_map hφ.aemeasurable (hg_meas.ennreal_toReal.log).aestronglyMeasurable
    have e2 : ∫ x, llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le) x ∂(μ.trim hφ.comap_le)
        = ∫ x, Real.log ((g ∘ φ) x).toReal ∂μ := by
      rw [integral_congr_ae hllr]
      exact (integral_trim (μ := μ) hφ.comap_le
        (hgφ_meas.ennreal_toReal.log).stronglyMeasurable).symm
    rw [e1, e2]
  rw [hI]
  congr 1
  · simp [measureReal_def, trim_measurableSet_eq hφ.comap_le MeasurableSet.univ,
      Measure.map_apply hφ MeasurableSet.univ]
  · simp [measureReal_def, trim_measurableSet_eq hφ.comap_le MeasurableSet.univ,
      Measure.map_apply hφ MeasurableSet.univ]

end
end CommunityReplay_50679f25_ec9c_4d36_8aec_9909731ed4aa
noncomputable def InformationTheory.klDiv_map_eq_klDiv_trim_comap := @CommunityReplay_50679f25_ec9c_4d36_8aec_9909731ed4aa.solution

namespace CommunityReplay_fafbe6cb_59dc_4a6f_bae5_3a0e7dda0f11
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# Relative entropy is invariant under a measurable embedding

`klDiv (μ.map f) (ν.map f) = klDiv μ ν` whenever `f` is a measurable embedding.

Pushing two measures forward along an injective measurable map with measurable range loses no
information, so the divergence is unchanged. This is the sharp form of the data-processing
inequality: equality holds exactly when nothing is forgotten.

It specialises Exercise 14.9 (relative entropy between push-forwards, printed p. 195): a
measurable embedding generates the whole σ-algebra, so the trim in that statement is trivial.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  -- for an embedding the generated σ-algebra is everything, so the trim does nothing
  have key : ∀ (m : MeasurableSpace α) (hm : m ≤ mα), m = mα →
      @klDiv α m (μ.trim hm) (ν.trim hm) = @klDiv α mα μ ν := by
    rintro m hm rfl
    simp only [trim_eq_self]
  rw [InformationTheory.klDiv_map_eq_klDiv_trim_comap hf.measurable μ ν]
  exact key _ hf.measurable.comap_le hf.comap_eq

end
end CommunityReplay_fafbe6cb_59dc_4a6f_bae5_3a0e7dda0f11
noncomputable def InformationTheory.klDiv_map_measurableEmbedding := @CommunityReplay_fafbe6cb_59dc_4a6f_bae5_3a0e7dda0f11.solution

namespace CommunityReplay_309502e7_3471_455e_8f5d_dfaf6d709f9e
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# The conditional term of the chain rule, as an integral

`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`, assuming fibrewise absolute
continuity only almost everywhere.

Mathlib's chain rule `klDiv_compProd_eq_add` leaves the conditional divergence in the form
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`; this evaluates it as the average of the fibrewise divergences,
which is the form in which conditional relative entropy is normally used and stated.

L&S Exercise 14.12 (chain rule, printed p. 196) writes the decomposition in exactly this form:
`D(P, Q) = ∑_t E_P[D(P_t(·|X_1..X_{t-1}), Q_t(·|X_1..X_{t-1}))]`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  classical
  -- the fibrewise density, as a jointly measurable function
  set f : α → β → ℝ≥0∞ := κ.rnDeriv η with hf
  have hf_meas : Measurable (Function.uncurry f) := κ.measurable_rnDeriv η
  have hκ : (η.withDensity f) =ᵐ[μ] κ := by
    filter_upwards [hac] with a ha
    ext s hs
    rw [hf, Kernel.withDensity_rnDeriv_eq ha]
  -- absolute continuity of the composition-products
  have hac' : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.AbsolutelyContinuous.compProd_right hac
  -- the density of the composition-products is the fibrewise one
  have hwd : (μ ⊗ₘ η).withDensity (fun p ↦ f p.1 p.2) = μ ⊗ₘ κ := by
    rw [← Measure.compProd_withDensity hf_meas]
    exact Measure.compProd_congr hκ
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ f p.1 p.2 := by
    conv_lhs => rw [← hwd]
    exact Measure.rnDeriv_withDensity _ hf_meas
  -- unfold both sides and use Fubini for the composition-product
  rw [klDiv_eq_lintegral_klFun_of_ac hac']
  have hmeas : Measurable (fun p : α × β ↦ ENNReal.ofReal (klFun ((f p.1 p.2).toReal))) :=
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp
      (ENNReal.measurable_toReal.comp hf_meas))
  calc ∫⁻ p, ENNReal.ofReal (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)) ∂(μ ⊗ₘ η)
      = ∫⁻ p, ENNReal.ofReal (klFun ((f p.1 p.2).toReal)) ∂(μ ⊗ₘ η) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn] with p hp
        rw [hp]
    _ = ∫⁻ a, ∫⁻ y, ENNReal.ofReal (klFun ((f a y).toReal)) ∂(η a) ∂μ := by
        rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hac] with a ha
        rw [klDiv_eq_lintegral_klFun_of_ac ha]
        refine lintegral_congr_ae ?_
        filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)] with y hy
        rw [hf]
        rw [hy]

end
end CommunityReplay_309502e7_3471_455e_8f5d_dfaf6d709f9e
noncomputable def InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae := @CommunityReplay_309502e7_3471_455e_8f5d_dfaf6d709f9e.solution

namespace CommunityReplay_3bd5e5d9_7d01_4286_926e_407c31ef11f6
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# The one-round divergence of the canonical bandit model

`klDiv (banditStepKernel ν π n h) (banditStepKernel ν' π n h)
  = ∑ i, (π.select n h) {i} * klDiv (ν.P i) (ν'.P i)`.

This is the conditional computation inside L&S Lemma 15.1 / Eq. (15.2) (printed pp. 198-199):
after conditioning on the arm actually selected, the policy factors cancel from the likelihood
ratio and only the reward divergences survive, weighted by the policy's selection probabilities.

It is stated here as a standalone reusable lemma: it is the per-round content of every divergence
decomposition in the canonical model, and is needed pointwise on an event whenever the
decomposition is localised (as in stopping-time arguments).
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- For a measure on a finite type, almost every point has positive mass. -/
private lemma ae_singleton_ne_zero {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure ι) : ∀ᵐ i ∂μ, μ {i} ≠ 0 := by
  classical
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have hset : {i : ι | μ {i} = 0} = ⋃ i ∈ {i : ι | μ {i} = 0}, ({i} : Set ι) := by
    ext i; simp
  rw [hset, measure_biUnion_null_iff (Set.to_countable _)]
  exact fun i hi ↦ hi

private theorem arm_ac {k : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤) (i : Fin k) :
    nu.P i ≪ nu'.P i :=
  (klDiv_ne_top_iff.mp (hKL i)).1

private theorem measurable_arm_rnDeriv {k : ℕ} (nu nu' : StochasticBandit k) :
    Measurable (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) := by
  classical
  let f : Fin k × ℝ → ENNReal := fun z ↦
    ∑ i, Set.indicator {z : Fin k × ℝ | z.1 = i}
      (fun z ↦ (nu.P i).rnDeriv (nu'.P i) z.2) z
  have hf : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro i _
    exact ((Measure.measurable_rnDeriv (nu.P i) (nu'.P i)).comp measurable_snd).indicator
      ((measurableSet_singleton i).preimage measurable_fst)
  have h_eq : f = fun z : Fin k × ℝ ↦
      (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
    funext z
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    simp
  rwa [← h_eq]

private theorem step_ac {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    banditStepKernel nu pi n h ≪ banditStepKernel nu' pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  filter_upwards [ae_singleton_ne_zero (pi.select n h)] with i hi
  show nu.P i ≪ nu'.P i
  exact (klDiv_ne_top_iff.mp (hKL i hi)).1

private theorem step_withDensity {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    (banditStepKernel nu' pi n h).withDensity
        (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) =
      banditStepKernel nu pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  ext s hs
  rw [withDensity_apply _ hs]
  rw [Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  rw [Measure.lintegral_compProd
    ((measurable_arm_rnDeriv nu nu').indicator hs)]
  apply lintegral_congr_ae
  filter_upwards [ae_singleton_ne_zero (pi.select n h)] with i hi
  rw [Kernel.sectR_apply, Kernel.sectR_apply]
  simp only [Kernel.comap_apply, banditRewardKernel]
  change (∫⁻ x, s.indicator
      (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) (i, x)
      ∂nu'.P i) = nu.P i (Prod.mk i ⁻¹' s)
  calc
    _ = ∫⁻ x in Prod.mk i ⁻¹' s,
        (nu.P i).rnDeriv (nu'.P i) x ∂nu'.P i := by
      rw [← lintegral_indicator (measurable_prodMk_left hs)]
      apply lintegral_congr
      intro x
      rfl
    _ = nu.P i (Prod.mk i ⁻¹' s) :=
      Measure.setLIntegral_rnDeriv (klDiv_ne_top_iff.mp (hKL i hi)).1 _

private theorem rnDeriv_step {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    (banditStepKernel nu pi n h).rnDeriv (banditStepKernel nu' pi n h) =ᵐ[
      banditStepKernel nu' pi n h]
        fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
  rw [← step_withDensity nu nu' pi h hKL]
  exact Measure.rnDeriv_withDensity _ (measurable_arm_rnDeriv nu nu')

private theorem klDiv_banditStepKernel_eq_sum {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
  rw [klDiv_eq_lintegral_klFun_of_ac (step_ac nu nu' pi h hKL)]
  calc
    (∫⁻ z, ENNReal.ofReal
        (klFun (((banditStepKernel nu pi n h).rnDeriv
          (banditStepKernel nu' pi n h)) z).toReal)
        ∂banditStepKernel nu' pi n h) =
        ∫⁻ z, ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))
          ∂banditStepKernel nu' pi n h := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_step nu nu' pi h hKL] with z hz
      rw [hz]
    _ = ∫⁻ i, klDiv (nu.P i) (nu'.P i) ∂pi.select n h := by
      rw [banditStepKernel]
      rw [Kernel.compProd_apply_eq_compProd_sectR]
      have hmeas : Measurable (fun z : Fin k × ℝ ↦ ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp (measurable_arm_rnDeriv nu nu')))
      rw [Measure.lintegral_compProd hmeas]
      apply lintegral_congr_ae
      filter_upwards [ae_singleton_ne_zero (pi.select n h)] with i hi
      rw [Kernel.sectR_apply]
      simp only [Kernel.comap_apply, banditRewardKernel]
      change (∫⁻ x, ENNReal.ofReal
          (klFun (((nu.P i).rnDeriv (nu'.P i) x).toReal)) ∂nu'.P i) = _
      rw [klDiv_eq_lintegral_klFun_of_ac (klDiv_ne_top_iff.mp (hKL i hi)).1]
    _ = ∑ i, klDiv (nu.P i) (nu'.P i) * (pi.select n h) {i} := by
      exact lintegral_fintype _
    _ = ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ofReal_measureReal, mul_comm]


open _root_.CommunityReplay_3bd5e5d9_7d01_4286_926e_407c31ef11f6.BanditAlgorithm in
theorem _root_.CommunityReplay_3bd5e5d9_7d01_4286_926e_407c31ef11f6.solution {k n : ℕ} (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) :=
  klDiv_banditStepKernel_eq_sum nu nu' pi h hKL

end BanditAlgorithm

end
end CommunityReplay_3bd5e5d9_7d01_4286_926e_407c31ef11f6
noncomputable def BanditAlgorithm.klDiv_banditStepKernel_eq_sum_of_support := @CommunityReplay_3bd5e5d9_7d01_4286_926e_407c31ef11f6.solution

namespace CommunityReplay_354db276_f75b_4900_8afe_0e35986f918c
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# Relabelling the first coordinate of a composition-product

`(μ.map ι) ⊗ₘ η = (μ ⊗ₘ (η.comap ι hι)).map (Prod.map ι id)`.

Pushing the first marginal forward along `ι` and then composing with a kernel `η` is the same as
composing with the pulled-back kernel first and relabelling afterwards.

This is the transport needed to move a composition-product between two indexings of the same
space — for instance between histories indexed by `Fin n` and by an initial segment `Iic (n-1)`,
which is how the finite-horizon and infinite-horizon canonical models are related.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution {α α' β : Type*} {mα : MeasurableSpace α} {mα' : MeasurableSpace α'}
    {mβ : MeasurableSpace β} (μ : Measure α) [SFinite μ]
    {ι : α → α'} (hι : Measurable ι) (η : Kernel α' β) [IsSFiniteKernel η] :
    (μ.map ι) ⊗ₘ η = (μ ⊗ₘ (η.comap ι hι)).map (Prod.map ι id) := by
  have hmap : Measurable (Prod.map ι (id : β → β)) := hι.prodMap measurable_id
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.compProd_apply hs,
    Measure.compProd_apply (hmap hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hι]
  refine lintegral_congr fun y ↦ ?_
  rw [Kernel.comap_apply]
  congr 1

end
end CommunityReplay_354db276_f75b_4900_8afe_0e35986f918c
noncomputable def ProbabilityTheory.compProd_map_left := @CommunityReplay_354db276_f75b_4900_8afe_0e35986f918c.solution

namespace CommunityReplay_86e9c194_3c6e_4289_bfef_f4478f27bcb9
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# The one-step joint law of the infinite-horizon canonical bandit model

`P.map (fun ω ↦ (prefix n ω, ω n)) = (P.map (prefix n)) ⊗ₘ banditStepKernel ν π n`

for `P = banditTrajMeasure ν π`: conditionally on the first `n` rounds, round `n + 1` is drawn
from the one-round step kernel. This is the structural fact that lets a divergence computation on
the infinite trajectory space be carried out one round at a time.

Mathlib supplies the corresponding statement for `Kernel.trajMeasure` in its own indexing, where
histories are indexed by an initial segment `Iic a` rather than by `Fin (a + 1)`; the two are
reconciled by `banditIicHistory` together with `ProbabilityTheory.compProd_map_left`.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace BanditAlgorithm

open _root_.CommunityReplay_86e9c194_3c6e_4289_bfef_f4478f27bcb9.BanditAlgorithm in
theorem _root_.CommunityReplay_86e9c194_3c6e_4289_bfef_f4478f27bcb9.solution {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k) (n : ℕ) :
    (banditTrajMeasure ν π).map (fun ω ↦ (banditTrajPrefix k n ω, ω n))
      = ((banditTrajMeasure ν π).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel ν π n) := by
  set P := banditTrajMeasure ν π with hP
  cases n with
  | succ a =>
      -- `banditTrajPrefix k (a+1)` is Mathlib's `frestrictLe a` followed by the reindexing
      have hprefix : banditTrajPrefix k (a + 1)
          = (banditIicHistory k a) ∘ (Preorder.frestrictLe a) := rfl
      have hι : Measurable (banditIicHistory k a) := measurable_banditIicHistory
      have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin k × ℝ) a) := by fun_prop
      have hmath := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ ↦ Fin k × ℝ)
        (μ₀ := banditStepKernel ν π 0 fun t ↦ t.elim0)
        (κ := banditTrajKernel ν π) (a := a)
      calc P.map (fun ω ↦ (banditTrajPrefix k (a + 1) ω, ω (a + 1)))
          = (P.map (fun ω ↦ (Preorder.frestrictLe a ω, ω (a + 1)))).map
              (Prod.map (banditIicHistory k a) id) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
        _ = ((P.map (Preorder.frestrictLe a)) ⊗ₘ (banditTrajKernel ν π a)).map
              (Prod.map (banditIicHistory k a) id) :=
            congrArg (Measure.map (Prod.map (banditIicHistory k a) id)) hmath.symm
        _ = ((P.map (Preorder.frestrictLe a)).map (banditIicHistory k a)) ⊗ₘ
              (banditStepKernel ν π (a + 1)) :=
            (ProbabilityTheory.compProd_map_left _ hι _).symm
        _ = (P.map (banditTrajPrefix k (a + 1))) ⊗ₘ (banditStepKernel ν π (a + 1)) := by
            rw [hprefix, ← Measure.map_map hι hfr]
  | zero =>
      -- the empty prefix carries no information: both sides are the law of round one
      have hcoord : P.map (fun ω ↦ ω 0)
          = banditStepKernel ν π 0 (fun t ↦ t.elim0) := by
        have h1 : P.map (Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin k × ℝ) 0)
            = (banditStepKernel ν π 0 fun t ↦ t.elim0).map
              (MeasurableEquiv.piUnique (fun _i : Finset.Iic (0 : ℕ) ↦ Fin k × ℝ)).symm := by
          rw [hP, banditTrajMeasure, Kernel.trajMeasure,
            Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
            Kernel.partialTraj_self, Measure.id_comp]
        have h2 : (fun ω : ℕ → Fin k × ℝ ↦ ω 0)
            = (MeasurableEquiv.piUnique (fun _i : Finset.Iic (0 : ℕ) ↦ Fin k × ℝ)) ∘
              (Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin k × ℝ) 0) := rfl
        rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), h1,
          Measure.map_map (by fun_prop) (by fun_prop)]
        exact Measure.map_id
      haveI : MeasurableSingletonClass (BanditHistory k 0) :=
        ⟨fun a ↦ by
          convert MeasurableSet.univ using 1
          ext x
          simp [Subsingleton.elim x a]⟩
      have hconst : banditTrajPrefix k 0
          = fun _ : ℕ → Fin k × ℝ ↦ (fun t : Fin 0 ↦ t.elim0) := by
        funext ω; funext t; exact t.elim0
      have hdirac : P.map (banditTrajPrefix k 0)
          = Measure.dirac (fun t : Fin 0 ↦ t.elim0) := by
        rw [hconst, Measure.map_const]
        simp
      ext s hs
      rw [hdirac, Measure.dirac_compProd_apply hs]
      calc (P.map (fun ω ↦ (banditTrajPrefix k 0 ω, ω 0))) s
          = P ((fun ω ↦ (banditTrajPrefix k 0 ω, ω 0)) ⁻¹' s) :=
            Measure.map_apply (by fun_prop) hs
        _ = P ((fun ω ↦ ω 0) ⁻¹' (Prod.mk (fun t : Fin 0 ↦ t.elim0) ⁻¹' s)) := by
            rw [hconst]; rfl
        _ = (P.map (fun ω ↦ ω 0)) (Prod.mk (fun t : Fin 0 ↦ t.elim0) ⁻¹' s) :=
            (Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)).symm
        _ = (banditStepKernel ν π 0 (fun t ↦ t.elim0))
              (Prod.mk (fun t : Fin 0 ↦ t.elim0) ⁻¹' s) := by rw [hcoord]

end BanditAlgorithm

end
end CommunityReplay_86e9c194_3c6e_4289_bfef_f4478f27bcb9
noncomputable def BanditAlgorithm.banditTrajMeasure_joint_eq_compProd := @CommunityReplay_86e9c194_3c6e_4289_bfef_f4478f27bcb9.solution

namespace CommunityReplay_d1c7fd66_aeb6_47f3_adc2_56d1e464abc3
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
# Restricting a composition-product to a cylinder over the first coordinate

`(μ ⊗ₘ κ).restrict (s ×ˢ univ) = (μ.restrict s) ⊗ₘ κ`.

Conditioning the joint law on an event that depends only on the first coordinate is the same as
conditioning the first marginal and then composing. Mathlib has the corresponding statement for
`Kernel.compProd`; this is the version for a measure composed with a kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {s : Set α} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).restrict (s ×ˢ (univ : Set β)) = (μ.restrict s) ⊗ₘ κ := by
  ext t ht
  rw [Measure.restrict_apply ht,
    Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    Measure.compProd_apply ht,
    ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ (univ : Set β)) = Prod.mk a ⁻¹' t := by
      ext b; simp [ha]
    rw [this, Set.indicator_of_mem ha]
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ (univ : Set β)) = (∅ : Set β) := by
      ext b; simp [ha]
    rw [this, Set.indicator_of_notMem ha, measure_empty]

end
end CommunityReplay_d1c7fd66_aeb6_47f3_adc2_56d1e464abc3
noncomputable def ProbabilityTheory.compProd_restrict_prod_univ := @CommunityReplay_d1c7fd66_aeb6_47f3_adc2_56d1e464abc3.solution

namespace CommunityReplay_f7e7038a_18d6_4b85_96c2_ce9535ad6d8b
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
Assembly of `BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

namespace BanditAlgorithm

theorem banditRewardKernel_apply_rfl' {k : ℕ} (ν : StochasticBandit k) (i : Fin k) :
    banditRewardKernel ν i = ν.P i := rfl

/-- Appending one round to a history, as a measurable equivalence. -/
noncomputable def snocEquiv (k n : ℕ) :
    (BanditHistory k n × (Fin k × ℝ)) ≃ᵐ BanditHistory k (n + 1) :=
  (MeasurableEquiv.prodComm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin k × ℝ) (Fin.last n)).symm

lemma snocEquiv_apply {k n : ℕ} (p : BanditHistory k n × (Fin k × ℝ)) :
    snocEquiv k n p = Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2 := by
  funext t
  simp [snocEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last]
  rfl

lemma prefix_succ {k n : ℕ} (ω : ℕ → Fin k × ℝ) :
    banditTrajPrefix k (n + 1) ω
      = snocEquiv k n (banditTrajPrefix k n ω, ω n) := by
  rw [snocEquiv_apply]
  funext t
  refine Fin.lastCases ?_ (fun j ↦ ?_) t
  · simp [banditTrajPrefix]
  · simp [banditTrajPrefix]

/-- The joint map: length-`n` prefix together with the next observation. -/
def prefixPair (k n : ℕ) (ω : ℕ → Fin k × ℝ) : BanditHistory k n × (Fin k × ℝ) :=
  (banditTrajPrefix k n ω, ω n)

lemma measurable_prefixPair {k n : ℕ} : Measurable (prefixPair k n) :=
  measurable_banditTrajPrefix.prodMk (measurable_pi_apply n)

/-- Trimming and restricting to a set of the small σ-algebra commute. -/
lemma trim_restrict {α : Type*} {m m₀ : MeasurableSpace α} (hm : m ≤ m₀)
    (ρ : @Measure α m₀) {T : Set α} (hT : MeasurableSet[m] T) :
    (ρ.trim hm).restrict T = (ρ.restrict T).trim hm := by
  refine @Measure.ext _ m _ _ (fun A hA ↦ ?_)
  rw [Measure.restrict_apply hA, trim_measurableSet_eq hm (hA.inter hT),
    trim_measurableSet_eq hm hA, Measure.restrict_apply (hm _ hA)]

open _root_.CommunityReplay_f7e7038a_18d6_4b85_96c2_ce9535ad6d8b.BanditAlgorithm in
/-- Skeleton of the assembly: the four steps, with the analytic content still to be filled. -/
theorem _root_.CommunityReplay_f7e7038a_18d6_4b85_96c2_ce9535ad6d8b.solution {k : ℕ}
    (ν ν' : StochasticBandit k) (π : BanditPolicy k) (n : ℕ)
    (E : Set (ℕ → Fin k × ℝ))
    (hE : MeasurableSet[banditFiltration k n] E) :
    @klDiv (ℕ → Fin k × ℝ) (banditFiltration k (n + 1))
        (((banditTrajMeasure ν π).trim ((banditFiltration k).le (n + 1))).restrict E)
        (((banditTrajMeasure ν' π).trim ((banditFiltration k).le (n + 1))).restrict E) ≤
      @klDiv (ℕ → Fin k × ℝ) (banditFiltration k n)
          (((banditTrajMeasure ν π).trim ((banditFiltration k).le n)).restrict E)
          (((banditTrajMeasure ν' π).trim ((banditFiltration k).le n)).restrict E) +
        ∑ i, (banditTrajMeasure ν π) (E ∩ {ω | (ω n).1 = i}) *
          klDiv (ν.P i) (ν'.P i) := by
  classical
  set P := banditTrajMeasure ν π with hP
  set Q := banditTrajMeasure ν' π with hQ
  -- STEP 0: if a played arm has infinite divergence the right-hand side is already `⊤`
  by_cases hbad : ∃ i, klDiv (ν.P i) (ν'.P i) = ⊤ ∧ P (E ∩ {ω | (ω n).1 = i}) ≠ 0
  · obtain ⟨i, hi, hne⟩ := hbad
    have hsum : ∑ j, P (E ∩ {ω | (ω n).1 = j}) * klDiv (ν.P j) (ν'.P j) = ⊤ := by
      refine ENNReal.sum_eq_top.mpr ⟨i, Finset.mem_univ i, ?_⟩
      rw [hi, ENNReal.mul_top hne]
    rw [hsum, add_top]
    exact le_top
  push_neg at hbad
  -- so every arm reachable on `E` at this round has finite divergence
  have hgood : ∀ i, P (E ∩ {ω | (ω n).1 = i}) ≠ 0 → klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
    intro i hne hi
    exact hne (hbad i hi)
  -- `E` is a cylinder over the length-`n` prefix
  obtain ⟨E', hE'meas, hE'eq⟩ : ∃ E' : Set (BanditHistory k n),
      MeasurableSet E' ∧ banditTrajPrefix k n ⁻¹' E' = E := id hE
  have hpre : ∀ ω, prefixPair k n ω ∈ E' ×ˢ (univ : Set (Fin k × ℝ)) ↔ ω ∈ E := by
    intro ω
    simp only [prefixPair, Set.mem_prod, Set.mem_univ, and_true]
    rw [← hE'eq]
    rfl
  have hEpre : prefixPair k n ⁻¹' (E' ×ˢ (univ : Set (Fin k × ℝ))) = E := by
    ext ω; exact hpre ω
  -- STEP 4 : the restricted one-step factorisation
  have hfact : ∀ ρ : Measure (ℕ → Fin k × ℝ), ∀ nu : StochasticBandit k,
      ρ = banditTrajMeasure nu π →
      (ρ.restrict E).map (prefixPair k n)
        = ((ρ.restrict E).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel nu π n) := by
    intro ρ nu hρ
    subst hρ
    have h1 : ((banditTrajMeasure nu π).restrict E).map (prefixPair k n)
        = ((banditTrajMeasure nu π).map (prefixPair k n)).restrict
            (E' ×ˢ (univ : Set (Fin k × ℝ))) := by
      rw [Measure.restrict_map measurable_prefixPair
        (hE'meas.prod MeasurableSet.univ), hEpre]
    rw [h1, show (banditTrajMeasure nu π).map (prefixPair k n)
        = ((banditTrajMeasure nu π).map (banditTrajPrefix k n)) ⊗ₘ
          (banditStepKernel nu π n) from
      BanditAlgorithm.banditTrajMeasure_joint_eq_compProd nu π n,
      ProbabilityTheory.compProd_restrict_prod_univ _ _ hE'meas,
      Measure.restrict_map measurable_banditTrajPrefix hE'meas, hE'eq]
  -- STEPS 1-3 : both sides become divergences of push-forwards
  have hEn : MeasurableSet[banditFiltration k n] E := hE
  have hEn1 : MeasurableSet[banditFiltration k (n + 1)] E :=
    (banditFiltration k).mono (Nat.le_succ n) _ hE
  have hpush : ∀ (m : ℕ) (hEm : MeasurableSet[banditFiltration k m] E),
      @klDiv (ℕ → Fin k × ℝ) (banditFiltration k m)
          ((P.trim ((banditFiltration k).le m)).restrict E)
          ((Q.trim ((banditFiltration k).le m)).restrict E)
        = klDiv ((P.restrict E).map (banditTrajPrefix k m))
            ((Q.restrict E).map (banditTrajPrefix k m)) := by
    intro m hEm
    rw [trim_restrict _ _ hEm, trim_restrict _ _ hEm]
    exact (InformationTheory.klDiv_map_eq_klDiv_trim_comap
      (measurable_banditTrajPrefix (k := k) (n := m)) _ _).symm
  rw [hpush n hEn, hpush (n + 1) hEn1]
  -- drop the append: it is a measurable embedding
  have hsnoc : ∀ ρ : Measure (ℕ → Fin k × ℝ),
      (ρ.restrict E).map (banditTrajPrefix k (n + 1))
        = ((ρ.restrict E).map (prefixPair k n)).map (snocEquiv k n) := by
    intro ρ
    rw [Measure.map_map (snocEquiv k n).measurable measurable_prefixPair]
    congr 1
    funext ω
    exact prefix_succ ω
  rw [hsnoc P, hsnoc Q,
    InformationTheory.klDiv_map_measurableEmbedding (snocEquiv k n).measurableEmbedding,
    hfact P ν rfl, hfact Q ν' rfl,
    klDiv_compProd_eq_add]
  refine add_le_add le_rfl ?_
  -- STEP 6 : evaluate the conditional term
  have hsing : ∀ (m : Measure (Fin k)), ∀ᵐ i ∂m, m {i} ≠ 0 := by
    intro m
    classical
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hset : {i : Fin k | m {i} = 0} = ⋃ i ∈ {i : Fin k | m {i} = 0}, ({i} : Set (Fin k)) := by
      ext i; simp
    rw [hset, measure_biUnion_null_iff (Set.to_countable _)]
    exact fun i hi ↦ hi
  -- the arm marginal of the step kernel
  have harm : ∀ (nu : StochasticBandit k) (h : BanditHistory k n) (i : Fin k),
      banditStepKernel nu π n h ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))
        = (π.select n h) {i} := by
    intro nu h i
    rw [banditStepKernel, Kernel.compProd_apply
      ((measurableSet_singleton i).prod MeasurableSet.univ)]
    simp only [Kernel.comap_apply]
    have hfun : ∀ b : Fin k, (banditRewardKernel nu) b
        (Prod.mk b ⁻¹' ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ)))
        = Set.indicator ({i} : Set (Fin k)) (fun _ ↦ (1 : ℝ≥0∞)) b := by
      intro b
      by_cases hb : b = i
      · subst hb
        have hu : Prod.mk b ⁻¹' ((({b} : Set (Fin k))) ×ˢ (univ : Set ℝ)) = univ := by
          ext c; simp
        rw [hu, Set.indicator_of_mem (by simp : b ∈ ({b} : Set (Fin k)))]
        have hk : (banditRewardKernel nu) b = nu.P b := rfl
        rw [hk, measure_univ]
      · have he : Prod.mk b ⁻¹' ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ)) = (∅ : Set ℝ) := by
          ext c; simp [hb]
        rw [he, Set.indicator_of_notMem (by simpa using hb), measure_empty]
    rw [lintegral_congr hfun, lintegral_indicator (measurableSet_singleton i)]
    simp
  -- the occupation identity
  have hocc : ∀ i : Fin k,
      ∫⁻ h, (π.select n h) {i} ∂((P.restrict E).map (banditTrajPrefix k n))
        = P (E ∩ {ω | (ω n).1 = i}) := by
    intro i
    have hSm : MeasurableSet ((univ : Set (BanditHistory k n)) ×ˢ
        ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))) :=
      MeasurableSet.univ.prod ((measurableSet_singleton i).prod MeasurableSet.univ)
    calc ∫⁻ h, (π.select n h) {i} ∂((P.restrict E).map (banditTrajPrefix k n))
        = ∫⁻ h, (banditStepKernel ν π n h) (Prod.mk h ⁻¹'
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))))
            ∂((P.restrict E).map (banditTrajPrefix k n)) := by
          refine lintegral_congr fun h ↦ ?_
          rw [← harm ν h i]
          congr 1
          ext x; simp
      _ = (((P.restrict E).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel ν π n))
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))) :=
          (Measure.compProd_apply hSm).symm
      _ = ((P.restrict E).map (prefixPair k n))
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))) := by
          rw [hfact P ν rfl]
      _ = (P.restrict E) (prefixPair k n ⁻¹'
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ)))) :=
          Measure.map_apply measurable_prefixPair hSm
      _ = P (E ∩ {ω | (ω n).1 = i}) := by
          rw [Measure.restrict_apply (measurable_prefixPair hSm)]
          congr 1
          ext ω
          simp [prefixPair, and_comm]
  -- almost every history only plays arms of finite divergence
  have hae : ∀ᵐ h ∂((P.restrict E).map (banditTrajPrefix k n)),
      ∀ i, (π.select n h) {i} ≠ 0 → klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
    rw [ae_all_iff]
    intro i
    by_cases hi : klDiv (ν.P i) (ν'.P i) = ⊤
    · have h0 : ∫⁻ h, (π.select n h) {i} ∂((P.restrict E).map (banditTrajPrefix k n)) = 0 := by
        rw [hocc i]; exact hbad i hi
      have hz := (lintegral_eq_zero_iff
        (Kernel.measurable_coe (π.select n) (measurableSet_singleton i))).mp h0
      filter_upwards [hz] with h hh hne
      exact absurd hh hne
    · filter_upwards with h _ ; exact hi
  -- fibrewise absolute continuity, almost everywhere
  have hac : ∀ᵐ h ∂((P.restrict E).map (banditTrajPrefix k n)),
      banditStepKernel ν π n h ≪ banditStepKernel ν' π n h := by
    filter_upwards [hae] with h hh
    rw [banditStepKernel, banditStepKernel, Kernel.compProd_apply_eq_compProd_sectR,
      Kernel.compProd_apply_eq_compProd_sectR]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards [hsing (π.select n h)] with i hi
    simpa [Kernel.sectR_apply, banditRewardKernel_apply_rfl'] using
      (klDiv_ne_top_iff.mp (hh i hi)).1
  rw [InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae _ _ _ hac]
  refine le_of_eq ?_
  calc ∫⁻ h, klDiv (banditStepKernel ν π n h) (banditStepKernel ν' π n h)
        ∂((P.restrict E).map (banditTrajPrefix k n))
      = ∫⁻ h, ∑ i, ENNReal.ofReal ((π.select n h).real {i}) * klDiv (ν.P i) (ν'.P i)
          ∂((P.restrict E).map (banditTrajPrefix k n)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with h hh
        exact BanditAlgorithm.klDiv_banditStepKernel_eq_sum_of_support ν ν' π h hh
    _ = ∑ i, ∫⁻ h, ENNReal.ofReal ((π.select n h).real {i}) * klDiv (ν.P i) (ν'.P i)
          ∂((P.restrict E).map (banditTrajPrefix k n)) := by
        refine lintegral_finset_sum _ fun i _ ↦ ?_
        exact ((Kernel.measurable_coe (π.select n)
          (measurableSet_singleton i)).ennreal_toReal.ennreal_ofReal).mul_const _
    _ = ∑ i, P (E ∩ {ω | (ω n).1 = i}) * klDiv (ν.P i) (ν'.P i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hcongr : ∫⁻ h, ENNReal.ofReal ((π.select n h).real {i}) * klDiv (ν.P i) (ν'.P i)
              ∂((P.restrict E).map (banditTrajPrefix k n))
            = ∫⁻ h, (π.select n h) {i} * klDiv (ν.P i) (ν'.P i)
              ∂((P.restrict E).map (banditTrajPrefix k n)) := by
          refine lintegral_congr fun h ↦ ?_
          rw [ofReal_measureReal]
        rw [hcongr, lintegral_mul_const _
          (Kernel.measurable_coe (π.select n) (measurableSet_singleton i)), hocc i]

end BanditAlgorithm

end
end CommunityReplay_f7e7038a_18d6_4b85_96c2_ce9535ad6d8b
noncomputable def BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event := @CommunityReplay_f7e7038a_18d6_4b85_96c2_ce9535ad6d8b.solution

namespace CommunityReplay_45ef0bd4_df3c_4efd_bc4c_8a61706c075a
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
/-!
Reduction of `BanditAlgorithm.bandit_stopped_klDiv_one_step` (L&S Exercise 14.13, printed p. 197,
specialised to the canonical bandit model of Lemma 15.1, Eq. (15.2), printed pp. 198-199).

Write `S = {τ ≤ n}`. The two stopped σ-algebras satisfy
`F_{τ∧m} = F_τ ⊓ F_m` (`IsStoppingTime.measurableSpace_min_const`), so:

* on `S` the learner has already stopped, and `F_{τ∧(n+1)}` and `F_{τ∧n}` have the same trace;
* on `Sᶜ = {τ > n}` the traces are those of the plain filtration `F_{n+1}` and `F_n`, and the
  comparison becomes the one-step chain rule on the `F_n`-event `Sᶜ`.

Splitting the divergence along `S` (additivity over a measurable partition) and treating the two
halves by these two principles gives the result.
-/

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

namespace BanditAlgorithm

/-- Trimming to a smaller σ-algebra commutes with restricting to a set of that σ-algebra. -/
private lemma trim_restrict_trim {α : Type*} {m m' m₀ : MeasurableSpace α}
    (hmm' : m ≤ m') (hm' : m' ≤ m₀) (ρ : @Measure α m₀) {T : Set α}
    (hT : MeasurableSet[m] T) :
    ((ρ.trim hm').restrict T).trim hmm' = (ρ.trim (hmm'.trans hm')).restrict T := by
  refine @Measure.ext _ m _ _ (fun A hA ↦ ?_)
  have hA' : MeasurableSet[m'] A := hmm' _ hA
  have hT' : MeasurableSet[m'] T := hmm' _ hT
  rw [trim_measurableSet_eq hmm' hA, Measure.restrict_apply hA', Measure.restrict_apply hA,
    trim_measurableSet_eq hm' (hA'.inter hT'), trim_measurableSet_eq (hmm'.trans hm') (hA.inter hT)]

open _root_.CommunityReplay_45ef0bd4_df3c_4efd_bc4c_8a61706c075a.BanditAlgorithm in
theorem _root_.CommunityReplay_45ef0bd4_df3c_4efd_bc4c_8a61706c075a.solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) (n : ℕ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const (n + 1)).measurableSpace
        ((banditTrajMeasure ν π).trim
          (hτ.min_const (n + 1)).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim
          (hτ.min_const (n + 1)).measurableSpace_le) ≤
      @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
          ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
          ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) +
        ∑ i, (banditTrajMeasure ν π)
            {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
          klDiv (ν.P i) (ν'.P i) := by
  classical
  set P := banditTrajMeasure ν π with hP
  set Q := banditTrajMeasure ν' π with hQ
  set m₁ := (hτ.min_const n).measurableSpace with hm₁
  set m₂ := (hτ.min_const (n + 1)).measurableSpace with hm₂
  have h₁ : m₁ ≤ _ := (hτ.min_const n).measurableSpace_le
  have h₂ : m₂ ≤ _ := (hτ.min_const (n + 1)).measurableSpace_le
  set S : Set (ℕ → Fin k × ℝ) := {ω | τ ω ≤ (n : ℕ∞)} with hS
  -- the two stopped σ-algebras are nested
  have hm₁₂ : m₁ ≤ m₂ :=
    IsStoppingTime.measurableSpace_mono (hτ.min_const n) (hτ.min_const (n + 1)) fun ω ↦
      min_le_min_left (τ ω) (WithTop.coe_le_coe.mpr (Nat.le_succ n))
  -- `S` lies in the smaller one
  have hSm₁ : MeasurableSet[m₁] S :=
    (IsStoppingTime.measurableSet_min_const_iff hτ S).mpr ⟨hτ.measurableSet_le' n, hτ n⟩
  have hSm₂ : MeasurableSet[m₂] S := hm₁₂ _ hSm₁
  -- comparison with the plain filtration
  have hm₂F : m₂ ≤ banditFiltration k (n + 1) := by
    rw [hm₂, IsStoppingTime.measurableSpace_min_const hτ]; exact inf_le_right
  have hm₁F : m₁ ≤ banditFiltration k n := by
    rw [hm₁, IsStoppingTime.measurableSpace_min_const hτ]; exact inf_le_right
  -- trace of `m₂` on `S` is contained in `m₁`
  have htraceS : ∀ A, MeasurableSet[m₂] A → MeasurableSet[m₁] (A ∩ S) := by
    intro A hA
    have hAτ : MeasurableSet[hτ.measurableSpace] A :=
      ((IsStoppingTime.measurableSet_min_const_iff hτ A).mp hA).1
    exact (hτ.measurableSet_inter_le_const_iff A n).mp (hAτ.inter (hτ.measurableSet_le' n))
  -- trace of `F n` on `Sᶜ` is contained in `m₁`
  have hScFn : MeasurableSet[banditFiltration k n] Sᶜ := (hτ n).compl
  have htraceSc : ∀ B, MeasurableSet[banditFiltration k n] B → MeasurableSet[m₁] (B ∩ Sᶜ) := by
    intro B hB
    refine (IsStoppingTime.measurableSet_min_const_iff hτ (B ∩ Sᶜ)).mpr
      ⟨⟨(le_iSup (fun t ↦ (banditFiltration k) t) n) _ (hB.inter hScFn), fun j ↦ ?_⟩, hB.inter hScFn⟩
    by_cases hj : n < j
    · have h1 : MeasurableSet[banditFiltration k j] B :=
        (banditFiltration k).mono hj.le _ hB
      have h2 : MeasurableSet[banditFiltration k j] Sᶜ :=
        (banditFiltration k).mono hj.le _ hScFn
      exact (h1.inter h2).inter (hτ j)
    · have hempty : B ∩ Sᶜ ∩ {ω | τ ω ≤ (j : ℕ∞)} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_compl_iff, hS, mem_setOf_eq, mem_empty_iff_false, iff_false,
          not_and]
        rintro ⟨-, hnS⟩ hle
        exact hnS (hle.trans (by exact_mod_cast Nat.le_of_not_lt hj))
      exact (@MeasurableSet.empty _ (banditFiltration k j)).congr hempty.symm
  -- finiteness instances for the trimmed measures
  haveI : IsFiniteMeasure (P.trim h₂) :=
    ⟨by rw [trim_measurableSet_eq h₂ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim h₂) :=
    ⟨by rw [trim_measurableSet_eq h₂ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  haveI : IsFiniteMeasure (P.trim h₁) :=
    ⟨by rw [trim_measurableSet_eq h₁ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim h₁) :=
    ⟨by rw [trim_measurableSet_eq h₁ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  have hF₂ : banditFiltration k (n + 1) ≤ _ := (banditFiltration k).le (n + 1)
  have hF₁ : banditFiltration k n ≤ _ := (banditFiltration k).le n
  haveI : IsFiniteMeasure (P.trim hF₂) :=
    ⟨by rw [trim_measurableSet_eq hF₂ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim hF₂) :=
    ⟨by rw [trim_measurableSet_eq hF₂ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  haveI : IsFiniteMeasure (P.trim hF₁) :=
    ⟨by rw [trim_measurableSet_eq hF₁ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim hF₁) :=
    ⟨by rw [trim_measurableSet_eq hF₁ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  have hScm₂ : MeasurableSet[m₂] Sᶜ := hSm₂.compl
  have hScm₁ : MeasurableSet[m₁] Sᶜ := hSm₁.compl
  -- the restricted measures live on `S` (resp. `Sᶜ`)
  have hnullS : ∀ {m : MeasurableSpace (ℕ → Fin k × ℝ)} (ρ : @Measure _ m)
      (T : Set (ℕ → Fin k × ℝ)), MeasurableSet[m] Tᶜ → (ρ.restrict T) Tᶜ = 0 := by
    intro m ρ T hT
    rw [Measure.restrict_apply hT, Set.compl_inter_self, measure_empty]
  -- STEP 1 : split along `S`
  have split₂ := @InformationTheory.klDiv_restrict_add_klDiv_restrict_compl _ m₂
    (P.trim h₂) (Q.trim h₂) _ _ S hSm₂
  have split₁ := @InformationTheory.klDiv_restrict_add_klDiv_restrict_compl _ m₁
    (P.trim h₁) (Q.trim h₁) _ _ S hSm₁
  -- STEP 2 : on `S` the finer stopped σ-algebra adds nothing
  have stepS : @klDiv _ m₂ ((P.trim h₂).restrict S) ((Q.trim h₂).restrict S) ≤
      @klDiv _ m₁ ((P.trim h₁).restrict S) ((Q.trim h₁).restrict S) := by
    have := InformationTheory.klDiv_le_klDiv_trim_of_trace_eq hm₁₂
      ((P.trim h₂).restrict S) ((Q.trim h₂).restrict S)
      (hnullS (P.trim h₂) S hScm₂) (hnullS (Q.trim h₂) S hScm₂) htraceS
    rwa [trim_restrict_trim hm₁₂ h₂ P hSm₁, trim_restrict_trim hm₁₂ h₂ Q hSm₁] at this
  -- STEP 3 : on `Sᶜ` we descend to the plain filtration, apply the one-step chain rule, come back
  have stepSc : @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ) ≤
      @klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) +
        ∑ i, P {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} * klDiv (ν.P i) (ν'.P i) := by
    have hScF₂ : MeasurableSet[banditFiltration k (n + 1)] Sᶜ :=
      (banditFiltration k).mono (Nat.le_succ n) _ hScFn
    -- (i) data processing : `m₂ ≤ F (n+1)`
    have hdp : @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ) ≤
        @klDiv _ (banditFiltration k (n + 1))
          ((P.trim hF₂).restrict Sᶜ) ((Q.trim hF₂).restrict Sᶜ) := by
      have := InformationTheory.klDiv_trim_le_of_isFiniteMeasure hm₂F
        ((P.trim hF₂).restrict Sᶜ) ((Q.trim hF₂).restrict Sᶜ)
      rwa [trim_restrict_trim hm₂F hF₂ P hScm₂, trim_restrict_trim hm₂F hF₂ Q hScm₂] at this
    -- (ii) the one-step chain rule on the `F n`-event `Sᶜ`
    have hchain := BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event ν ν' π n Sᶜ hScFn
    -- (iii) climb back to `m₁`
    have hback : @klDiv _ (banditFiltration k n)
        ((P.trim hF₁).restrict Sᶜ) ((Q.trim hF₁).restrict Sᶜ) ≤
        @klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) := by
      have := InformationTheory.klDiv_le_klDiv_trim_of_trace_eq hm₁F
        ((P.trim hF₁).restrict Sᶜ) ((Q.trim hF₁).restrict Sᶜ)
        (hnullS (P.trim hF₁) Sᶜ (by simpa using hScFn))
        (hnullS (Q.trim hF₁) Sᶜ (by simpa using hScFn)) htraceSc
      rwa [trim_restrict_trim hm₁F hF₁ P hScm₁, trim_restrict_trim hm₁F hF₁ Q hScm₁] at this
    -- the increment term is the same set
    have hsets : ∀ i : Fin k, Sᶜ ∩ {ω | (ω n).1 = i} = {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} := by
      intro i
      ext ω
      simp only [hS, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_le]
    calc @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ)
        ≤ @klDiv _ (banditFiltration k (n + 1))
            ((P.trim hF₂).restrict Sᶜ) ((Q.trim hF₂).restrict Sᶜ) := hdp
      _ ≤ @klDiv _ (banditFiltration k n)
            ((P.trim hF₁).restrict Sᶜ) ((Q.trim hF₁).restrict Sᶜ) +
            ∑ i, P (Sᶜ ∩ {ω | (ω n).1 = i}) * klDiv (ν.P i) (ν'.P i) := hchain
      _ ≤ @klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) +
            ∑ i, P {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} * klDiv (ν.P i) (ν'.P i) := by
            refine add_le_add hback (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
            rw [hsets i]
  -- STEP 4 : reassemble
  rw [split₂, split₁]
  calc @klDiv _ m₂ ((P.trim h₂).restrict S) ((Q.trim h₂).restrict S)
        + @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ)
      ≤ @klDiv _ m₁ ((P.trim h₁).restrict S) ((Q.trim h₁).restrict S)
        + (@klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) +
            ∑ i, P {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} * klDiv (ν.P i) (ν'.P i)) :=
        add_le_add stepS stepSc
    _ = _ := by rw [← add_assoc]

end BanditAlgorithm

end
end CommunityReplay_45ef0bd4_df3c_4efd_bc4c_8a61706c075a
noncomputable def BanditAlgorithm.bandit_stopped_klDiv_one_step := @CommunityReplay_45ef0bd4_df3c_4efd_bc4c_8a61706c075a.solution

namespace CommunityReplay_ce5eb1ce_d6e8_419a_90d3_c22e2b7b465e
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open scoped ENNReal

namespace BanditAlgorithm

private noncomputable def stoppedArmCount {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (i : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ≥0∞ :=
  ∑' t : ℕ,
    if (t : ℕ∞) < min (τ ω) n ∧ (ω t).1 = i then 1 else 0

private lemma stoppedArmCount_eq_sum_range {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (i : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    stoppedArmCount τ i n ω =
      ∑ t ∈ Finset.range n,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then 1 else 0 := by
  rw [stoppedArmCount, tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_range] at ht
    simp [ht]
  · intro t ht
    simp only [Finset.mem_range, not_lt] at ht
    simp [not_lt_of_ge ht]

private lemma stoppedArmCount_succ {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (i : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    stoppedArmCount τ i (n + 1) ω =
      stoppedArmCount τ i n ω +
        if (n : ℕ∞) < τ ω ∧ (ω n).1 = i then 1 else 0 := by
  rw [stoppedArmCount_eq_sum_range, stoppedArmCount_eq_sum_range,
    Finset.sum_range_succ]

private lemma measurable_stoppedStepEvent {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (i : Fin k) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} := by
  have ha : Measurable (fun ω : ℕ → Fin k × ℝ ↦ (ω n).1) :=
    measurable_fst.comp (measurable_pi_apply n)
  exact (hτ.measurableSpace_le _ (hτ.measurableSet_gt' n)).inter
    (ha (measurableSet_singleton i))

private lemma measurable_stoppedArmCount {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (i : Fin k) (n : ℕ) :
    Measurable (stoppedArmCount τ i n) := by
  rw [show stoppedArmCount τ i n =
      fun ω ↦ ∑ t ∈ Finset.range n,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then 1 else 0 by
    funext ω
    exact stoppedArmCount_eq_sum_range τ i n ω]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurable_stoppedStepEvent τ hτ i t)
    measurable_const measurable_const

private lemma lintegral_stoppedArmCount_succ {k : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (i : Fin k) (n : ℕ) :
    (∫⁻ ω, stoppedArmCount τ i (n + 1) ω ∂banditTrajMeasure ν π) =
      (∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) +
        (banditTrajMeasure ν π) {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} := by
  rw [lintegral_congr (fun ω ↦ stoppedArmCount_succ τ i n ω),
    lintegral_add_left (measurable_stoppedArmCount τ hτ i n)]
  have hE := measurable_stoppedStepEvent τ hτ i n
  rw [show (fun ω : ℕ → Fin k × ℝ ↦
      if (n : ℕ∞) < τ ω ∧ (ω n).1 = i then (1 : ℝ≥0∞) else 0) =
      {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i}.indicator (fun _ ↦ 1) by
        funext ω
        by_cases h : (n : ℕ∞) < τ ω ∧ (ω n).1 = i <;> simp [h]]
  rw [lintegral_indicator hE]
  simp

private lemma banditFiltration_zero {k : ℕ} :
    banditFiltration k 0 = ⊥ := by
  unfold banditFiltration
  change MeasurableSpace.comap (banditTrajPrefix k 0) inferInstance = ⊥
  have hconst :
      banditTrajPrefix k 0 =
        fun _ω : ℕ → Fin k × ℝ ↦ (fun t : Fin 0 ↦ t.elim0) := by
    funext ω t
    exact t.elim0
  rw [hconst, MeasurableSpace.comap_const]

private lemma bandit_stopped_klDiv_zero {k : ℕ}
    (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const 0).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const 0).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const 0).measurableSpace_le) = 0 := by
  have hm : (hτ.min_const 0).measurableSpace = ⊥ := by
    calc
      (hτ.min_const 0).measurableSpace =
          hτ.measurableSpace ⊓ banditFiltration k 0 :=
        hτ.measurableSpace_min_const
      _ = ⊥ := by rw [banditFiltration_zero, inf_bot_eq]
  have hmeasure :
      @Measure.trim (ℕ → Fin k × ℝ) (hτ.min_const 0).measurableSpace
          inferInstance (banditTrajMeasure ν π)
          (hτ.min_const 0).measurableSpace_le =
        @Measure.trim (ℕ → Fin k × ℝ) (hτ.min_const 0).measurableSpace
          inferInstance (banditTrajMeasure ν' π)
          (hτ.min_const 0).measurableSpace_le := by
    letI : MeasurableSpace (ℕ → Fin k × ℝ) :=
      (hτ.min_const 0).measurableSpace
    apply Measure.ext
    intro s hs
    have hsbot : @MeasurableSet (ℕ → Fin k × ℝ) ⊥ s := by
      rw [← hm]
      exact hs
    rcases MeasurableSpace.measurableSet_bot_iff.mp hsbot with rfl | rfl
    · simp
    · rw [trim_measurableSet_eq (hτ.min_const 0).measurableSpace_le
          (@MeasurableSet.univ _ (hτ.min_const 0).measurableSpace),
        trim_measurableSet_eq (hτ.min_const 0).measurableSpace_le
          (@MeasurableSet.univ _ (hτ.min_const 0).measurableSpace)]
      simp
  rw [hmeasure, klDiv_self]

open _root_.CommunityReplay_ce5eb1ce_d6e8_419a_90d3_c22e2b7b465e.BanditAlgorithm in
theorem _root_.CommunityReplay_ce5eb1ce_d6e8_419a_90d3_c22e2b7b465e.solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) (n : ℕ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < min (τ ω) n ∧ (ω t).1 = i
            then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  change
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) *
        klDiv (ν.P i) (ν'.P i)
  induction n with
  | zero =>
      rw [bandit_stopped_klDiv_zero ν ν' π τ hτ]
      exact bot_le
  | succ n ih =>
      refine (bandit_stopped_klDiv_one_step ν ν' π τ hτ n).trans ?_
      calc
        @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
              ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
              ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) +
            ∑ i, (banditTrajMeasure ν π)
                {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
              klDiv (ν.P i) (ν'.P i) ≤
            (∑ i, (∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) *
              klDiv (ν.P i) (ν'.P i)) +
            ∑ i, (banditTrajMeasure ν π)
                {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
              klDiv (ν.P i) (ν'.P i) :=
          add_le_add_left ih _
        _ = ∑ i,
            ((∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) +
              (banditTrajMeasure ν π)
                {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i}) *
              klDiv (ν.P i) (ν'.P i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [add_mul]
        _ = ∑ i, (∫⁻ ω, stoppedArmCount τ i (n + 1) ω
              ∂banditTrajMeasure ν π) *
              klDiv (ν.P i) (ν'.P i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [lintegral_stoppedArmCount_succ ν π τ hτ]

end BanditAlgorithm

end
end CommunityReplay_ce5eb1ce_d6e8_419a_90d3_c22e2b7b465e
noncomputable def BanditAlgorithm.bandit_bounded_stopping_klDiv_le_expected_information := @CommunityReplay_ce5eb1ce_d6e8_419a_90d3_c22e2b7b465e.solution

namespace CommunityReplay_baad5db1_8de4_43f6_b101_d808743504ff
section
open _root_.BanditAlgorithm _root_.InformationTheory _root_.ProbabilityTheory
open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    @klDiv (ℕ → Fin k × ℝ) hτ.measurableSpace
        ((banditTrajMeasure ν π).trim hτ.measurableSpace_le)
        ((banditTrajMeasure ν' π).trim hτ.measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  refine (klDiv_stopped_le_iSup_truncations ν ν' π τ hτ hfinite).trans ?_
  refine iSup_le fun n ↦
    (bandit_bounded_stopping_klDiv_le_expected_information ν ν' π τ hτ n).trans ?_
  refine Finset.sum_le_sum fun i _ ↦ _root_.mul_le_mul_left ?_ _
  refine lintegral_mono fun ω ↦ ENNReal.tsum_le_tsum fun t ↦ ?_
  split_ifs with htrunc hfull
  · exact le_rfl
  · exact False.elim (hfull ⟨htrunc.1.trans_le (min_le_left _ _), htrunc.2⟩)
  · exact bot_le
  · exact le_rfl

end
end CommunityReplay_baad5db1_8de4_43f6_b101_d808743504ff
noncomputable def BanditAlgorithm.bandit_stopped_klDiv_le_expected_information := @CommunityReplay_baad5db1_8de4_43f6_b101_d808743504ff.solution

open MeasureTheory InformationTheory
namespace SharpTesting
lemma tangent (x y r : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 0 < r)
    (hzero : y = 0 → x = 0) :
    x * Real.log r - (r-1)*y ≤ x*Real.log (x/y)+y-x := by
  by_cases h : x = 0
  · subst x
    nlinarith [mul_nonneg hr.le hy]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
  have hyp : 0 < y := lt_of_le_of_ne hy (fun he => h (hzero he.symm))
  have hb := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (mul_pos hr hyp) hxp)) hx
  have he : x*(r*y/x-1) = r*y-x := by field_simp
  rw [he,Real.log_div (mul_ne_zero hr.ne' hyp.ne') hxp.ne',Real.log_mul hr.ne' hyp.ne'] at hb
  rw [Real.log_div hxp.ne' hyp.ne']
  nlinarith

lemma threshold_tangent (δ x y : ℝ) (hδ : 0 < δ) (hδ2 : δ < 1/2)
    (hx : 1-δ ≤ x) (hy : y ≤ δ) :
    BanditAlgorithm.bernoulliRelativeEntropy (1-δ) δ ≤
      (x*Real.log ((1-δ)/δ) - ((1-δ)/δ-1)*y) +
      ((1-x)*Real.log (δ/(1-δ)) - (δ/(1-δ)-1)*(1-y)) := by
  have hd : 0 < 1-δ := by linarith
  have hr : 1 < (1-δ)/δ := (one_lt_div hδ).mpr (by linarith)
  have hs : δ/(1-δ) < 1 := (div_lt_one hd).mpr (by linarith)
  have hl : 0 < Real.log ((1-δ)/δ) := Real.log_pos hr
  have hlog : Real.log (δ/(1-δ)) = -Real.log ((1-δ)/δ) := by
    rw [Real.log_div hδ.ne' hd.ne',Real.log_div hd.ne' hδ.ne']
    ring
  have he1 : ((1-δ)/δ)*δ = 1-δ := div_mul_cancel₀ _ hδ.ne'
  have he2 : (δ/(1-δ))*(1-δ) = δ := div_mul_cancel₀ _ hd.ne'
  unfold BanditAlgorithm.bernoulliRelativeEntropy
  rw [show 1-(1-δ)=δ by ring,hlog]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) hl.le,
    mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr (le_trans hs.le hr.le))]
end SharpTesting


open MeasureTheory InformationTheory Set
open scoped ENNReal
namespace SharpTesting
lemma event_tangent {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set α)
    (hac : μ ≪ ν) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (μ.real A * Real.log r - (r-1)*ν.real A) ≤
      klDiv (μ.restrict A) (ν.restrict A) := by
  have hz : ν.real A = 0 → μ.real A = 0 := by
    intro h
    have hv : ν A = 0 := ((ENNReal.toReal_eq_zero_iff (ν A)).mp h).resolve_right (measure_ne_top ν A)
    simp only [Measure.real, hac hv, ENNReal.toReal_zero]
  have ht := tangent (μ.real A) (ν.real A) r ENNReal.toReal_nonneg ENNReal.toReal_nonneg hr hz
  have hm := mul_log_le_klDiv (μ.restrict A) (ν.restrict A)
  simp only [Measure.real, Measure.restrict_apply_univ] at hm
  exact (ENNReal.ofReal_le_ofReal ht).trans hm

lemma event_testing {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set α) (hA : MeasurableSet A)
    (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ < 1/2)
    (hx : 1-δ ≤ μ.real A) (hy : ν.real A ≤ δ) :
    ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1-δ) δ) ≤ klDiv μ ν := by
  by_cases ht : klDiv μ ν = ⊤
  · simp [ht]
  have hac := (klDiv_ne_top_iff.mp ht).1
  have hp : 0 < 1-δ := by linarith
  have h1 := event_tangent μ ν A hac ((1-δ)/δ) (div_pos hp hδ)
  have h2 := event_tangent μ ν Aᶜ hac (δ/(1-δ)) (div_pos hδ hp)
  have hmc : μ.real Aᶜ = 1-μ.real A := by
    have h := measureReal_add_measureReal_compl (μ := μ) hA
    simp only [Measure.real, measure_univ, ENNReal.toReal_one] at h
    simp only [Measure.real]
    linarith
  have hnc : ν.real Aᶜ = 1-ν.real A := by
    have h := measureReal_add_measureReal_compl (μ := ν) hA
    simp only [Measure.real, measure_univ, ENNReal.toReal_one] at h
    simp only [Measure.real]
    linarith
  rw [hmc,hnc] at h2
  have hb := ENNReal.ofReal_le_ofReal (threshold_tangent δ (μ.real A) (ν.real A) hδ hδ2 hx hy)
  exact hb.trans (ENNReal.ofReal_add_le.trans ((add_le_add h1 h2).trans_eq
    (InformationTheory.klDiv_restrict_add_klDiv_restrict_compl μ ν hA).symm))
end SharpTesting


open MeasureTheory InformationTheory BanditAlgorithm
open scoped ENNReal
 theorem solution {k : ℕ} (ν₀ ν₁ : StochasticBandit k) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2) (π : BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Bool) (hτ : IsBanditStoppingTime τ)
    (hψ : Measurable[hτ.measurableSpace] ψ) (hcorr : FairReplay.IsDeltaCorrect δ ν₀ ν₁ π τ ψ)
    (hfin : FairReplay.expectedRounds ν₀ π τ < ⊤) :
    ENNReal.ofReal (bernoulliRelativeEntropy (1 - δ) δ) ≤
      ∑ i, (∫⁻ ω, FairReplay.armCount i τ ω ∂banditTrajMeasure ν₀ π) *
        klDiv (ν₀.P i) (ν₁.P i) := by
  let E : Set (ℕ → Fin k × ℝ) := {ω | τ ω < ⊤ ∧ ψ ω = true}
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    (measurableSet_lt hτ.measurable measurable_const).inter
      (hψ (measurableSet_singleton true))
  let μ := (banditTrajMeasure ν₀ π).trim hτ.measurableSpace_le
  let ν := (banditTrajMeasure ν₁ π).trim hτ.measurableSpace_le
  haveI : @IsProbabilityMeasure _ hτ.measurableSpace μ := ⟨by
    dsimp [μ]
    rw [trim_measurableSet_eq _ MeasurableSet.univ, measure_univ]⟩
  haveI : @IsProbabilityMeasure _ hτ.measurableSpace ν := ⟨by
    dsimp [ν]
    rw [trim_measurableSet_eq _ MeasurableSet.univ, measure_univ]⟩
  have he0 : μ E ≤ ENNReal.ofReal δ := by
    simpa only [μ, trim_measurableSet_eq hτ.measurableSpace_le hE] using hcorr.1
  have he1 : ν Eᶜ ≤ ENNReal.ofReal δ := by
    change (banditTrajMeasure ν₁ π).trim hτ.measurableSpace_le Eᶜ ≤ _
    rw [trim_measurableSet_eq _ hE.compl]
    exact hcorr.2
  have hreal0 : μ.real E ≤ δ := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he0).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hreal1 : ν.real Eᶜ ≤ δ := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he1).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hcomp : 1-δ ≤ μ.real Eᶜ := by
    have h := @measureReal_add_measureReal_compl _ hτ.measurableSpace μ E _ hE
    have hu : μ.real Set.univ = 1 := by simp only [Measure.real,measure_univ,ENNReal.toReal_one]
    rw [hu] at h
    linarith
  have hb := @SharpTesting.event_testing _ hτ.measurableSpace μ ν inferInstance inferInstance Eᶜ hE.compl δ hδ hδ2 hcomp hreal1
  exact hb.trans (bandit_stopped_klDiv_le_expected_information ν₀ ν₁ π τ hτ hfin)
