-- Prove2me | solution 1 for BanditAlgorithm.klDiv_stopped_le_iSup_truncations
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T20:34:11.500181+00:00
-- url     : https://prove2.me/submissions/906eabbf-c33a-4814-8aa9-54b687d247bf

import Definitions.Def_BanditTrajectory
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

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

theorem _root_.solution
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
