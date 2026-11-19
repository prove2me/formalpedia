-- Prove2me | solution 1 for BilateralProfitMHR.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T11:51:26.507867+00:00
-- url     : https://prove2.me/submissions/d9832942-9174-499c-99e3-c2a272b49e99

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_BilateralProfitMHR_LogProfitOracle
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Theorems.Thm_BilateralProfitMHR_proposition_3_2
import Theorems.Thm_BilateralProfitMHR_claim_5_5
import Theorems.Thm_BilateralProfitMHR_corollary_3_1



namespace BilateralProfitMHR
open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade Set
open scoped ENNReal

private theorem prior_isProbabilityMeasure (E : Environment) (hE : UnitSupport E) :
    IsProbabilityMeasure E.prior := (positive_density_profit_facts E hE).1

private theorem continuousOn_mu (E : Environment) (hE : UnitSupport E) :
    ContinuousOn (muP E.prior) unitSq := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := positive_density_profit_facts E hE
  exact h

private theorem continuousOn_loss (E : Environment) (hE : UnitSupport E) :
    ContinuousOn (lossL E.prior) intT := by
  obtain ⟨_, _, _, _, _, _, _, h, _⟩ := positive_density_profit_facts E hE
  exact h
private lemma ptrade_nonneg (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade D a :=
  ENNReal.toReal_nonneg

private lemma ptrade_le_one (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (a : ℝ × ℝ) :
    Ptrade D a ≤ 1 := by
  unfold Ptrade
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr prob_le_one

private lemma mu_le_ptrade {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a ∈ unitSq) :
    muP D a ≤ Ptrade D a := by
  unfold muP
  apply mul_le_of_le_one_left (ptrade_nonneg D a)
  rcases ha with ⟨ha, hb⟩
  linarith [ha.1, hb.2]

private lemma intT_subset_unitSq : intT ⊆ unitSq := by
  intro a ha
  exact ⟨⟨ha.1.le, (ha.2.1.trans ha.2.2).le⟩, ⟨(ha.1.trans ha.2.1).le, ha.2.2.le⟩⟩

private theorem mu_pos (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ} (ha : a ∈ intT) :
    0 < muP E.prior a := by
  obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := positive_density_profit_facts E hE
  exact (h a (intT_subset_unitSq ha)).mpr ha
private theorem geomLaw_probability (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    IsProbabilityMeasure (geomLaw Q) := by
  have hs := (hasSum_geometric_of_lt_one (sub_nonneg.mpr hQ1)
    (sub_lt_self 1 hQ0)).mul_right Q
  have hs' : HasSum (fun k : ℕ => (1 - Q) ^ k * Q) 1 := by
    simpa only [show 1 - (1 - Q) = Q by ring, inv_mul_cancel₀ hQ0.ne'] using hs
  exact hs'.isProbabilityMeasure_sum_dirac (fun k => by positivity)

private theorem Ptrade_measurable (D : Measure (ℝ × ℝ)) [SFinite D] :
    Measurable (BilateralProfit.Ptrade D) := by
  unfold BilateralProfit.Ptrade
  exact (measurable_measure_prodMk_left
    (show MeasurableSet {w : (ℝ × ℝ) × (ℝ × ℝ) |
      BilateralProfit.Trades w.2 w.1} by
        unfold BilateralProfit.Trades
        exact (measurableSet_le (by fun_prop : Measurable (fun w :
          (ℝ × ℝ) × (ℝ × ℝ) => w.2.1)) (by fun_prop)).inter
          (measurableSet_le (by fun_prop : Measurable (fun w :
            (ℝ × ℝ) × (ℝ × ℝ) => w.1.2)) (by fun_prop)))).ennreal_toReal

private theorem oracleLaw_measurable (D : Measure (ℝ × ℝ)) [SFinite D] :
    Measurable (oracleLaw D) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hg : ∀ x : ℝ × ℝ, Measurable (fun N : ℕ =>
      harm (N - 1) - Real.log (x.2 - x.1)) := fun _ => measurable_of_countable _
  simp only [oracleLaw, Measure.map_apply (hg _) hs, geomLaw,
    Measure.sum_apply _ (hg _ hs), Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hg _ hs)]
  apply Measurable.tsum
  intro k
  apply Measurable.mul
  · exact ENNReal.measurable_ofReal.comp
      (((measurable_const.sub (Ptrade_measurable D)).pow_const k).mul (Ptrade_measurable D))
  · exact measurable_const.indicator (hs.preimage (by fun_prop : Measurable (fun x : ℝ × ℝ =>
      harm (k + 1 - 1) - Real.log (x.2 - x.1))))
end BilateralProfitMHR


namespace BilateralProfitMHR
open MeasureTheory Set BilateralProfit MechanismDesign.BilateralTrade
private lemma continuousOn_mu_compact_region (E : Environment) (hE : UnitSupport E)
    {R : Set (ℝ × ℝ)} (hR : R ⊆ intT) : ContinuousOn (muP E.prior) R :=
  (continuousOn_mu E hE).mono (hR.trans intT_subset_unitSq)

private lemma mu_max_on_compact_region (E : Environment) (hE : UnitSupport E)
    {R : Set (ℝ × ℝ)} (hne : R.Nonempty) (hcompact : IsCompact R) (hR : R ⊆ intT) :
    ∃ b ∈ R, muP E.prior b = sSup (muP E.prior '' R) ∧
      ∀ x ∈ R, muP E.prior x ≤ muP E.prior b := by
  obtain ⟨b,hb,hmax⟩ := hcompact.exists_isMaxOn hne (continuousOn_mu_compact_region E hE hR)
  have hbd : BddAbove (muP E.prior '' R) := by
    refine ⟨muP E.prior b, ?_⟩
    rintro v ⟨x,hx,rfl⟩
    exact hmax hx
  have hsup : sSup (muP E.prior '' R) = muP E.prior b := by
    apply le_antisymm
    · apply csSup_le (hne.image _)
      rintro v ⟨x,hx,rfl⟩
      exact hmax hx
    · exact le_csSup hbd ⟨b,hb,rfl⟩
  exact ⟨b,hb,hsup.symm,fun x hx => hmax hx⟩

private lemma mu_sSup_pos (E : Environment) (hE : UnitSupport E)
    {R : Set (ℝ × ℝ)} (hne : R.Nonempty) (hcompact : IsCompact R) (hR : R ⊆ intT) :
    0 < sSup (muP E.prior '' R) := by
  obtain ⟨b,hb,he,_⟩ := mu_max_on_compact_region E hE hne hcompact hR
  rw [← he]
  exact mu_pos E hE (hR hb)

private lemma loss_sInf_eq_neg_log_sSup_mu (E : Environment) (hE : UnitSupport E)
    {R : Set (ℝ × ℝ)} (hne : R.Nonempty) (hcompact : IsCompact R) (hR : R ⊆ intT) :
    sInf (lossL E.prior '' R) = -Real.log (sSup (muP E.prior '' R)) := by
  obtain ⟨b,hb,he,hmax⟩ := mu_max_on_compact_region E hE hne hcompact hR
  have hbmin : ∀ x ∈ R, lossL E.prior b ≤ lossL E.prior x := by
    intro x hx
    exact neg_le_neg (Real.log_le_log (mu_pos E hE (hR hx)) (hmax x hx))
  have hbd : BddBelow (lossL E.prior '' R) := by
    refine ⟨lossL E.prior b, ?_⟩
    rintro v ⟨x,hx,rfl⟩
    exact hbmin x hx
  have hinf : sInf (lossL E.prior '' R) = lossL E.prior b := by
    apply le_antisymm
    · exact csInf_le hbd ⟨b,hb,rfl⟩
    · apply le_csInf (hne.image _)
      rintro v ⟨x,hx,rfl⟩
      exact hbmin x hx
  rw [hinf, ← he]
  rfl

private lemma loss_sub_sInf_eq_log_ratio (E : Environment) (hE : UnitSupport E)
    {R : Set (ℝ × ℝ)} (hne : R.Nonempty) (hcompact : IsCompact R) (hR : R ⊆ intT)
    {x : ℝ × ℝ} (hx : x ∈ R) :
    lossL E.prior x - sInf (lossL E.prior '' R) =
      Real.log (sSup (muP E.prior '' R) / muP E.prior x) := by
  rw [loss_sInf_eq_neg_log_sSup_mu E hE hne hcompact hR,
    Real.log_div (mu_sSup_pos E hE hne hcompact hR).ne' (mu_pos E hE (hR hx)).ne']
  unfold lossL
  ring

private lemma loss_mem_Icc_scale_log (E : Environment) (hE : UnitSupport E) {δ : ℝ} (hδ : 0 < δ)
    {x : ℝ × ℝ} (hx : x ∈ intT) (hl : δ / 2 ≤ muP E.prior x) (hu : muP E.prior x ≤ 6 * δ) :
    lossL E.prior x ∈ Icc (-Real.log (6 * δ)) (-Real.log (6 * δ) + Real.log 12) := by
  have hpos := mu_pos E hE hx
  have hlo := Real.log_le_log hpos hu
  have hup := Real.log_le_log (div_pos hδ (by norm_num : (0:ℝ) < 2)) hl
  have he : -Real.log (δ / 2) = -Real.log (6 * δ) + Real.log 12 := by
    rw [Real.log_div hδ.ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hδ.ne',
      show (12:ℝ) = 6 * 2 by norm_num,
      Real.log_mul (by norm_num : (6:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    ring
  change -Real.log (6 * δ) ≤ -Real.log (muP E.prior x) ∧
    -Real.log (muP E.prior x) ≤ -Real.log (6 * δ) + Real.log 12
  exact ⟨neg_le_neg hlo, (neg_le_neg hup).trans_eq he⟩

private lemma loss_mem_Icc_scale (E : Environment) (hE : UnitSupport E) {δ : ℝ} (hδ : 0 < δ)
    {x : ℝ × ℝ} (hx : x ∈ intT) (hl : δ / 2 ≤ muP E.prior x) (hu : muP E.prior x ≤ 6 * δ) :
    lossL E.prior x ∈ Icc (-Real.log (6 * δ)) (-Real.log (6 * δ) + 12) := by
  have h := loss_mem_Icc_scale_log E hE hδ hx hl hu
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 12 by norm_num)
  exact ⟨h.1, by linarith [h.2]⟩
end BilateralProfitMHR



namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade Set
open scoped ENNReal

private theorem subgaussianNorm_map {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f) (g : Y → ℝ) (hg : Measurable g) :
    HighDimProb.Concentration.subgaussianNorm (μ.map f) g =
      HighDimProb.Concentration.subgaussianNorm μ (g ∘ f) := by
  unfold HighDimProb.Concentration.subgaussianNorm
  apply iInf_congr
  intro t
  apply iInf_congr
  intro ht
  have hm : Measurable (fun y => Real.exp ((g y) ^ 2 / t ^ 2)) := by fun_prop
  simp_rw [integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable,
    integral_map hf.aemeasurable hm.aestronglyMeasurable]
  rfl

private theorem oracleLaw_noise_at (E : Environment) (hE : UnitSupport E)
    (x : ℝ × ℝ) (hx : x ∈ intT) :
    IsProbabilityMeasure (oracleLaw E.prior x) ∧
      Integrable (fun z : ℝ => z) (oracleLaw E.prior x) ∧
      (∫ z, z ∂(oracleLaw E.prior x)) = lossL E.prior x ∧
      HighDimProb.Concentration.subgaussianNorm (oracleLaw E.prior x)
        (fun z => z - lossL E.prior x) ≤
          ENNReal.ofReal (4 * Real.sqrt (1 - Real.log (Ptrade E.prior x))) := by
  haveI := prior_isProbabilityMeasure E hE
  have hspread : 0 < x.2 - x.1 := sub_pos.mpr hx.2.1
  have hmu := mu_pos E hE hx
  have hQ0 : 0 < Ptrade E.prior x := (mul_pos_iff_of_pos_left hspread).mp hmu
  have hQ1 := ptrade_le_one E.prior x
  haveI := geomLaw_probability (Ptrade E.prior x) hQ0 hQ1
  have hfm : Measurable (fun N : ℕ => harm (N - 1) - Real.log (x.2 - x.1)) :=
    measurable_of_countable _
  have hprob : IsProbabilityMeasure (oracleLaw E.prior x) :=
    Measure.isProbabilityMeasure_map hfm.aemeasurable
  have hmean := claim_5_5 (Ptrade E.prior x) hQ0 hQ1
  have hL : lossL E.prior x = -Real.log (Ptrade E.prior x) - Real.log (x.2 - x.1) := by
    unfold lossL muP
    rw [Real.log_mul hspread.ne' hQ0.ne']
    ring
  have hint : Integrable (fun z : ℝ => z) (oracleLaw E.prior x) := by
    apply (integrable_map_measure (by fun_prop) hfm.aemeasurable).mpr
    exact hmean.1.sub (integrable_const _)
  refine ⟨hprob, hint, ?_, ?_⟩
  · unfold oracleLaw
    rw [integral_map hfm.aemeasurable (by fun_prop), integral_sub hmean.1 (integrable_const _),
      hmean.2.1, integral_const, probReal_univ, one_smul]
    exact hL.symm
  · unfold oracleLaw
    rw [subgaussianNorm_map _ _ hfm _ (by fun_prop)]
    have heq : (fun z : ℝ => z - lossL E.prior x) ∘
        (fun N : ℕ => harm (N - 1) - Real.log (x.2 - x.1)) =
        (fun N : ℕ => harm (N - 1) + Real.log (Ptrade E.prior x)) := by
      funext N
      simp only [Function.comp_apply, hL]
      ring
    rw [heq]
    exact hmean.2.2

private theorem oracleLaw_noiseCond (E : Environment) (hE : UnitSupport E)
    (K : ℕ) (hK : 2 ≤ K) (δ : ℝ) (hδ : 1 / (K : ℝ) ≤ δ)
    (R : Set (ℝ × ℝ)) (hR : R ⊆ intT)
    (hmu : ∀ x ∈ R, δ / 2 ≤ muP E.prior x) :
    NoiseCond R (lossL E.prior) (4 * Real.sqrt (1 + Real.log (2 * K)))
      (fun _ _ _ x => oracleLaw E.prior x) := by
  haveI := prior_isProbabilityMeasure E hE
  intro τ xs ys x hxs hx
  obtain ⟨hp, hi, hm, hn⟩ := oracleLaw_noise_at E hE x (hR hx)
  refine ⟨hp, hi, hm, hn.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hx' := hR hx
  have hxunit : x ∈ unitSq := ⟨⟨hx'.1.le, by linarith [hx'.2.1, hx'.2.2]⟩,
    ⟨by linarith [hx'.1, hx'.2.1], hx'.2.2.le⟩⟩
  have hq : 1 / (2 * (K : ℝ)) ≤ Ptrade E.prior x := by
    have := (hmu x hx).trans (mu_le_ptrade hxunit)
    have heq : 1 / (2 * (K : ℝ)) = (1 / (K : ℝ)) / 2 := by ring
    rw [heq]
    linarith
  have hl := Real.log_le_log (by positivity : 0 < 1 / (2 * (K : ℝ))) hq
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity), Real.log_one,
    zero_sub] at hl
  linarith

end BilateralProfitMHR

namespace BilateralProfitMHR.MHRQueryTransport
open MeasureTheory
open scoped ENNReal
section Geometry

variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

private def mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω) : QueryAlg X Ω where
  query τ ω y := f (A.query τ ω y)
  query_measurable τ := hf.comp (A.query_measurable τ)

private def pullKernel (f : Y → X) (ν : ObsKernel X) : ObsKernel Y :=
  fun τ xs ys x => ν τ (fun i => f (xs i)) ys (f x)

private theorem mapQuery_isOn (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    {K : Set X} {R : Set Y} (hA : A.IsOn R) (hfK : Set.MapsTo f R K) :
    (mapQuery f hf A).IsOn K := by
  intro τ ω y
  exact hfK (hA τ ω y)

private theorem pullKernel_measurable (f : Y → X) (hf : Measurable f)
    (ν : ObsKernel X) (hν : ν.IsMeasurable) : (pullKernel f ν).IsMeasurable := by
  intro τ
  change Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ν τ (fun i => f (w.1 i)) w.2.1 (f w.2.2))
  exact (hν τ).comp (show Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ((fun i => f (w.1 i)), w.2.1, f w.2.2)) from by fun_prop)

private theorem pullKernel_noiseCond (f : Y → X) (ν : ObsKernel X)
    {K : Set X} {R : Set Y} (hfK : Set.MapsTo f R K) (L : X → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) : NoiseCond R (L ∘ f) γ (pullKernel f ν) := by
  intro τ xs ys x hxs hx
  exact hν τ (fun i => f (xs i)) ys (f x) (fun i => hfK (hxs i)) (hfK hx)

private theorem cumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (ν : ObsKernel X) (g : X → ℝ≥0∞) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss (mapQuery f hf A) ν g ω m τ y =
      cumLoss A (pullKernel f ν) (g ∘ f) ω m τ y := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, mapQuery, Function.comp_apply]
      congr 1
      apply lintegral_congr
      intro z
      exact ih (τ + 1) (Fin.snoc y z)

private theorem expectedCumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (P : Measure Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν g n =
      expectedCumLoss A P (pullKernel f ν) (g ∘ f) n := by
  apply lintegral_congr
  intro ω
  exact cumLoss_mapQuery f hf A ν g ω n 0 Fin.elim0

end Geometry

private theorem sInf_loss_image {X Y : Type} (f : Y → X) {R : Set Y} {K : Set X}
    (himage : f '' R = K) (L : X → ℝ) :
    sInf ((L ∘ f) '' R) = sInf (L '' K) := by
  change sInf ((fun x => L (f x)) '' R) = _
  rw [← Set.image_image L f R, himage]

private theorem expectedRegret_mapQuery {X Y Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Ω] (f : Y → X) (hf : Measurable f)
    {R : Set Y} {K : Set X} (himage : f '' R = K) (L : X → ℝ)
    (A : QueryAlg Y Ω) (P : Measure Ω) (ν : ObsKernel X) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν
      (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n =
    expectedCumLoss A P (pullKernel f ν)
      (fun x => ENNReal.ofReal ((L ∘ f) x - sInf ((L ∘ f) '' R))) n := by
  rw [expectedCumLoss_mapQuery, sInf_loss_image f himage L]
  rfl
end BilateralProfitMHR.MHRQueryTransport



namespace BilateralProfitMHR

open MeasureTheory Set MHRQueryTransport
open scoped ENNReal

private noncomputable def euclideanPairEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv

private theorem corollary_3_1_pair (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ C : ℝ, ∀ R : Set (ℝ × ℝ), R.Nonempty → IsCompact R → Convex ℝ R →
      ∀ b γ : ℝ, 0 ≤ γ → ∀ n : ℕ, 2 ≤ n →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (ℝ × ℝ) Ω, A.IsOn R ∧
            ∀ L : (ℝ × ℝ) → ℝ, ContinuousOn L R → ConvexOn ℝ R L →
              (∀ x ∈ R, L x ∈ Icc b (b + ℓ)) →
              ∀ ν : ObsKernel (ℝ × ℝ), ν.IsMeasurable → NoiseCond R L γ ν →
                expectedCumLoss A P ν (fun x => ENNReal.ofReal (L x - sInf (L '' R))) n ≤
                  ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by
  obtain ⟨C, hC⟩ := corollary_3_1 2 ℓ hℓ
  refine ⟨C, ?_⟩
  intro R hRne hRc hRv b γ hγ n hn
  let e := euclideanPairEquiv
  let S := e ⁻¹' R
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hRne
    exact ⟨e.symm x, by simpa [S] using hx⟩
  have hSc : IsCompact S := e.toHomeomorph.isCompact_preimage.mpr hRc
  have hSv : Convex ℝ S := hRv.linear_preimage e.toLinearMap
  obtain ⟨Ω, mΩ, P, hp, A, hA, hreg⟩ := hC S hSne hSc hSv b γ hγ n hn
  refine ⟨Ω, mΩ, P, hp, mapQuery e e.continuous.measurable A,
    mapQuery_isOn e e.continuous.measurable A hA (fun _ hx => hx), ?_⟩
  intro L hLc hLv hLrange ν hνm hν
  have hmap : MapsTo e S R := fun _ hx => hx
  have himage : e '' S = R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa [S] using hx, e.apply_symm_apply x⟩
  have h := hreg (L ∘ e) (hLc.comp e.continuous.continuousOn hmap)
    (hLv.comp_linearMap e.toLinearMap) (fun x hx => hLrange (e x) hx)
    (pullKernel e ν) (pullKernel_measurable e e.continuous.measurable ν hνm)
    (pullKernel_noiseCond e ν hmap L γ hν)
  rw [expectedRegret_mapQuery e e.continuous.measurable himage L]
  exact h

private theorem cumLoss_mono_horizon {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞)
    (ω : Ω) (m m' : ℕ) (hmm' : m ≤ m') (τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss A ν g ω m τ y ≤ cumLoss A ν g ω m' τ y := by
  induction m generalizing m' τ with
  | zero => simp only [cumLoss]; exact bot_le
  | succ m ih =>
      rcases m' with _ | m'
      · omega
      change _ + _ ≤ _ + _
      exact add_le_add le_rfl (lintegral_mono fun z => ih m' (by omega) (τ + 1) (Fin.snoc y z))

private theorem expectedCumLoss_mono_horizon {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞)
    (m m' : ℕ) (hmm' : m ≤ m') :
    expectedCumLoss A P ν g m ≤ expectedCumLoss A P ν g m' :=
  lintegral_mono fun ω => cumLoss_mono_horizon A ν g ω m m' hmm' 0 Fin.elim0

private theorem cumLoss_congr_on {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (R : Set X) (hA : A.IsOn R)
    (g h : X → ℝ≥0∞) (hgh : EqOn g h R)
    (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss A ν g ω m τ y = cumLoss A ν h ω m τ y := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, hgh (hA τ ω y)]
      congr 1
      exact lintegral_congr fun z => ih (τ + 1) (Fin.snoc y z)

private theorem expectedCumLoss_congr_on {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (R : Set X) (hA : A.IsOn R)
    (g h : X → ℝ≥0∞) (hgh : EqOn g h R) (n : ℕ) :
    expectedCumLoss A P ν g n = expectedCumLoss A P ν h n :=
  lintegral_congr fun ω => cumLoss_congr_on A ν R hA g h hgh ω n 0 Fin.elim0

end BilateralProfitMHR


namespace BilateralProfitMHR

private theorem conOpt_rate (C : ℝ) (T K n : ℕ) (hK : 2 ≤ K) (hKT : K ≤ T) (hn : 1 ≤ n) :
    C * (1 + 4 * Real.sqrt (1 + Real.log (2 * K))) * Real.sqrt (n + 1) *
        Real.log (n + 1) ^ 2 ≤
      (20 * max C 0) * Real.sqrt (n * Real.log T) * Real.log (2 * n) ^ 2 := by
  have hT : 2 ≤ T := hK.trans hKT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hlogK : Real.log K ≤ Real.log T :=
    Real.log_le_log hK0 (by exact_mod_cast hKT)
  have hA : 1 + Real.log (2 * (K : ℝ)) ≤ 4 * Real.log T := by
    rw [Real.log_mul (by norm_num) hK0.ne']
    linarith
  have hsA : Real.sqrt (1 + Real.log (2 * (K : ℝ))) ≤ 2 * Real.sqrt (Real.log T) := by
    calc
      _ ≤ Real.sqrt (4 * Real.log T) := Real.sqrt_le_sqrt hA
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hsT : 1 ≤ 2 * Real.sqrt (Real.log T) := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log T by linarith)
    have hpos := Real.sqrt_nonneg (Real.log T)
    nlinarith
  have hscale : 1 + 4 * Real.sqrt (1 + Real.log (2 * (K : ℝ))) ≤
      10 * Real.sqrt (Real.log T) := by linarith
  have hsn : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt n := by
    calc
      _ ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hln : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hln0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hln2 : Real.log ((n : ℝ) + 1) ^ 2 ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
    nlinarith
  calc
    _ ≤ max C 0 * (10 * Real.sqrt (Real.log T)) * (2 * Real.sqrt n) *
        Real.log (2 * (n : ℝ)) ^ 2 := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul (le_max_left C 0) hscale (by positivity) (le_max_right C 0)
        · exact hsn
        · positivity
        · positivity
      · exact hln2
      · positivity
      · positivity
    _ = _ := by
      rw [Real.sqrt_mul (show 0 ≤ (n : ℝ) by positivity)]
      ring

end BilateralProfitMHR


namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade Set
open scoped ENNReal

theorem lemma_5_6 :
    ∃ C : ℝ, ∀ T K : ℕ, 2 ≤ K → K ≤ T → ∀ δ : ℝ, 1 / (K : ℝ) ≤ δ →
      ∀ R : Set (ℝ × ℝ), R.Nonempty → IsCompact R → Convex ℝ R → R ⊆ intT →
        ∀ n : ℕ, 1 ≤ n →
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
            ∃ A : QueryAlg (ℝ × ℝ) Ω, A.IsOn R ∧
              ∀ E : Environment, UnitSupport E → IsMHR E →
                (∀ x ∈ R, δ / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ 6 * δ) →
                expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) n =
                  expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal
                      (Real.log (sSup (muP E.prior '' R) / muP E.prior x))) n ∧
                expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) n ≤
                  ENNReal.ofReal (C * Real.sqrt (n * Real.log T) * Real.log (2 * n) ^ 2) := by
  obtain ⟨C, hC⟩ := corollary_3_1_pair 12 (by norm_num)
  refine ⟨20 * max C 0, ?_⟩
  intro T K hK hKT δ hδ R hRne hRc hRv hR n hn
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity : 0 < 1 / (K : ℝ)) hδ
  obtain ⟨Ω, mΩ, P, hp, A, hA, hreg⟩ :=
    hC R hRne hRc hRv (-Real.log (6 * δ)) (4 * Real.sqrt (1 + Real.log (2 * K)))
      (by positivity) (n + 1) (by omega)
  refine ⟨Ω, mΩ, P, hp, A, hA, ?_⟩
  intro E hE hM hmu
  haveI := prior_isProbabilityMeasure E hE
  have hνm : ObsKernel.IsMeasurable (X := ℝ × ℝ) (fun _ _ _ x => oracleLaw E.prior x) := by
    intro τ
    exact (oracleLaw_measurable E.prior).comp measurable_snd.snd
  have hν := oracleLaw_noiseCond E hE K hK δ hδ R hR (fun x hx => (hmu x hx).1)
  constructor
  · apply expectedCumLoss_congr_on A P _ R hA
    intro x hx
    exact congrArg ENNReal.ofReal (loss_sub_sInf_eq_log_ratio E hE hRne hRc hR hx)
  · calc
      _ ≤ expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
          (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) (n + 1) :=
        expectedCumLoss_mono_horizon A P _ _ n (n + 1) (by omega)
      _ ≤ ENNReal.ofReal (C * (1 + 4 * Real.sqrt (1 + Real.log (2 * K))) *
          Real.sqrt (n + 1) * Real.log (n + 1) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hreg (lossL E.prior) ((continuousOn_loss E hE).mono hR)
          ((proposition_3_2 E hE hM).2.subset hR hRv)
          (fun x hx => loss_mem_Icc_scale E hE hδ0 (hR hx) (hmu x hx).1 (hmu x hx).2)
          _ hνm hν
      _ ≤ _ := ENNReal.ofReal_le_ofReal (conOpt_rate C T K n hK hKT hn)


end BilateralProfitMHR
open BilateralProfitMHR MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

theorem solution :
    ∃ C : ℝ, ∀ T K : ℕ, 2 ≤ K → K ≤ T → ∀ δ : ℝ, 1 / (K : ℝ) ≤ δ →
      ∀ R : Set (ℝ × ℝ), R.Nonempty → IsCompact R → Convex ℝ R → R ⊆ intT →
        ∀ n : ℕ, 1 ≤ n →
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
            ∃ A : QueryAlg (ℝ × ℝ) Ω, A.IsOn R ∧
              ∀ E : Environment, UnitSupport E → IsMHR E →
                (∀ x ∈ R, δ / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ 6 * δ) →
                expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) n =
                  expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal
                      (Real.log (sSup (muP E.prior '' R) / muP E.prior x))) n ∧
                expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) n ≤
                  ENNReal.ofReal (C * Real.sqrt (n * Real.log T) * Real.log (2 * n) ^ 2) := BilateralProfitMHR.lemma_5_6
