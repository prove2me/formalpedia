-- Prove2me | solution 1 for DistTransform.Distortion.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:04.517602+00:00
-- url     : https://prove2.me/submissions/3ecbb11a-6f86-4753-9348-b9990cbed05a

import Mathlib
import Definitions.Def_DistTransform_Distortion_Supplement_Choquet

open DistTransform
open DistTransform.Distortion
open DistTransform.Distortion.Supplement

open MeasureTheory

/-- Theorem 2, p. 11. One family works for all bounded laws, with a per-law
Lebesgue null set. Uniqueness concerns the output law, not the family. -/
theorem solution (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hT : Set.MapsTo T Minf Minf) :
    (IsMonotoneT Minf T ∧ PreservesConstants T ∧ IsAdditive T) ↔
      ∃ h : ℝ → ℝ → ℝ, IsOrderedFamily h ∧
        ∀ F ∈ Minf, Represents h F (T F) ∧
          ∀ G : ProbabilityMeasure ℝ, Represents h F G → G = T F := by
            have hcdfc : ∀ x y : ℝ, ProbabilityTheory.cdf ((constantLaw x : ProbabilityMeasure ℝ) : Measure ℝ) y
                = if x ≤ y then 1 else 0 := by
              intro x y
              rw [ProbabilityTheory.cdf_eq_real]
              show (Measure.dirac x).real (Set.Iic y) = _
              rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
              by_cases hxy : x ≤ y
              · simp [hxy, Set.indicator_of_mem (show x ∈ Set.Iic y from hxy)]
              · simp [hxy, Set.indicator_of_notMem (show x ∉ Set.Iic y from hxy)]
            have hqc : ∀ x p : ℝ, p ∈ Set.Ioo (0 : ℝ) 1 → leftQuantile (constantLaw x) p = x := by
              intro x p hp
              unfold leftQuantile
              have : {y : ℝ | p ≤ ProbabilityTheory.cdf ((constantLaw x : ProbabilityMeasure ℝ) : Measure ℝ) y}
                  = Set.Ici x := by
                ext y
                simp only [Set.mem_setOf_eq, Set.mem_Ici, hcdfc]
                by_cases hxy : x ≤ y
                · simp [hxy, hp.2.le]
                · simp [hxy, not_le.mpr hp.1]
              rw [this, csInf_Ici]
            have hchc : ∀ g : ℝ → ℝ, IsH g → ∀ x : ℝ, choquet g (constantLaw x) = x := by
              intro g hg x
              obtain ⟨-, hg0, hg1⟩ := hg
              unfold choquet
              have e1 : (fun y : ℝ => g (1 - ProbabilityTheory.cdf
                  ((constantLaw x : ProbabilityMeasure ℝ) : Measure ℝ) y) - 1)
                  = (Set.Ici x).indicator (fun _ => (-1 : ℝ)) := by
                funext y
                rw [hcdfc]
                by_cases hxy : x ≤ y
                · simp [hxy, hg0, Set.indicator_of_mem (show y ∈ Set.Ici x from hxy)]
                · simp [hxy, hg1, Set.indicator_of_notMem (show y ∉ Set.Ici x from hxy)]
              have e2 : (fun y : ℝ => g (1 - ProbabilityTheory.cdf
                  ((constantLaw x : ProbabilityMeasure ℝ) : Measure ℝ) y))
                  = (Set.Iio x).indicator (fun _ => (1 : ℝ)) := by
                funext y
                rw [hcdfc]
                by_cases hxy : x ≤ y
                · simp [hxy, hg0, Set.indicator_of_notMem (show y ∉ Set.Iio x from not_lt.mpr hxy)]
                · simp [hxy, hg1, Set.indicator_of_mem (show y ∈ Set.Iio x from not_le.mp hxy)]
              rw [e1, e2, setIntegral_indicator measurableSet_Ici, setIntegral_indicator measurableSet_Iio,
                setIntegral_const, setIntegral_const]
              have i1 : Set.Iic (0:ℝ) ∩ Set.Ici x = Set.Icc x 0 := by
                ext y; simp [and_comm]
              have i2 : Set.Ioi (0:ℝ) ∩ Set.Iio x = Set.Ioo 0 x := by
                ext y; simp
              rw [i1, i2, Real.volume_real_Icc, Real.volume_real_Ioo]
              simp only [smul_eq_mul]
              rcases le_total x 0 with hx | hx
              · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
              · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
            have hcM : ∀ x : ℝ, constantLaw x ∈ Minf := by
              intro x
              refine ⟨x, x, ?_⟩
              show Measure.dirac x (Set.Icc x x) = 1
              rw [Measure.dirac_apply' _ measurableSet_Icc]
              simp
            have hgb : ∀ g : ℝ → ℝ, IsH g → ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ g t ∧ g t ≤ 1 := by
              intro g hg t ht
              obtain ⟨hm, h0, h1⟩ := hg
              constructor
              · rw [← h0]; exact hm ⟨le_rfl, zero_le_one⟩ ht ht.1
              · rw [← h1]; exact hm ht ⟨zero_le_one, le_rfl⟩ ht.2
            have hcdf01 : ∀ (F : ProbabilityMeasure ℝ) (y : ℝ),
                1 - ProbabilityTheory.cdf (F : Measure ℝ) y ∈ Set.Icc (0:ℝ) 1 := by
              intro F y
              have h1 := ProbabilityTheory.cdf_nonneg (F : Measure ℝ) y
              have h2 := ProbabilityTheory.cdf_le_one (F : Measure ℝ) y
              constructor <;> linarith
            have hanti : ∀ g : ℝ → ℝ, IsH g → ∀ F : ProbabilityMeasure ℝ,
                Antitone (fun y => g (1 - ProbabilityTheory.cdf (F : Measure ℝ) y)) := by
              intro g hg F y z hyz
              apply hg.1 (hcdf01 F z) (hcdf01 F y)
              have := (ProbabilityTheory.cdf (F : Measure ℝ)).mono hyz
              linarith
            have hlow : ∀ F : ProbabilityMeasure ℝ, ∀ a b : ℝ, (F : Measure ℝ) (Set.Icc a b) = 1 →
                ∀ y, y < a → ProbabilityTheory.cdf (F : Measure ℝ) y = 0 := by
              intro F a b hab y hy
              rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
              have hc : (F : Measure ℝ) (Set.Icc a b)ᶜ = 0 := by
                rw [prob_compl_eq_zero_iff measurableSet_Icc]; exact hab
              have : (F : Measure ℝ) (Set.Iic y) = 0 := by
                apply measure_mono_null _ hc
                intro z hz
                simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
                intro h
                exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hz) hy) (not_lt.mpr h)
              rw [this]; simp
            have hhigh : ∀ F : ProbabilityMeasure ℝ, ∀ a b : ℝ, (F : Measure ℝ) (Set.Icc a b) = 1 →
                ∀ y, b ≤ y → ProbabilityTheory.cdf (F : Measure ℝ) y = 1 := by
              intro F a b hab y hy
              rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
              have : (F : Measure ℝ) (Set.Iic y) = 1 := by
                apply le_antisymm prob_le_one
                rw [← hab]
                exact measure_mono (fun z hz => Set.mem_Iic.mpr (hz.2.trans hy))
              rw [this]; simp
            have hint : ∀ g : ℝ → ℝ, IsH g → ∀ F ∈ Minf,
                IntegrableOn (fun y => g (1 - ProbabilityTheory.cdf (F : Measure ℝ) y) - 1) (Set.Iic 0) ∧
                IntegrableOn (fun y => g (1 - ProbabilityTheory.cdf (F : Measure ℝ) y)) (Set.Ioi 0) := by
              intro g hg F hF
              obtain ⟨a, b, hab⟩ := hF
              have hmeas : Measurable (fun y => g (1 - ProbabilityTheory.cdf (F : Measure ℝ) y)) :=
                (hanti g hg F).measurable
              constructor
              · refine Integrable.mono' (g := (Set.Icc a 0).indicator (fun _ => (1:ℝ))) ?_ ?_ ?_
                · exact ((integrable_indicator_iff measurableSet_Icc).2
                    continuous_const.integrableOn_Icc).restrict
                · exact (hmeas.sub measurable_const).aestronglyMeasurable
                · refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall ?_)
                  intro y hy
                  by_cases hya : y < a
                  · rw [hlow F a b hab y hya]
                    simp [hg.2.2]
                    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
                  · have hy' : y ∈ Set.Icc a 0 := ⟨not_lt.mp hya, hy⟩
                    rw [Set.indicator_of_mem hy']
                    have := hgb g hg _ (hcdf01 F y)
                    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
              · refine Integrable.mono' (g := (Set.Icc 0 b).indicator (fun _ => (1:ℝ))) ?_ ?_ ?_
                · exact ((integrable_indicator_iff measurableSet_Icc).2
                    continuous_const.integrableOn_Icc).restrict
                · exact hmeas.aestronglyMeasurable
                · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
                  intro y hy
                  by_cases hyb : b ≤ y
                  · rw [hhigh F a b hab y hyb]
                    simp [hg.2.1]
                    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
                  · have hy' : y ∈ Set.Icc 0 b := ⟨le_of_lt hy, (not_le.mp hyb).le⟩
                    rw [Set.indicator_of_mem hy']
                    have := hgb g hg _ (hcdf01 F y)
                    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
            have hchmono : ∀ g : ℝ → ℝ, IsH g → ∀ F ∈ Minf, ∀ G ∈ Minf,
                (∀ y, ProbabilityTheory.cdf (G : Measure ℝ) y ≤ ProbabilityTheory.cdf (F : Measure ℝ) y) →
                choquet g F ≤ choquet g G := by
              intro g hg F hF G hG hFG
              have hp : ∀ y, g (1 - ProbabilityTheory.cdf (F : Measure ℝ) y)
                  ≤ g (1 - ProbabilityTheory.cdf (G : Measure ℝ) y) := fun y =>
                hg.1 (hcdf01 F y) (hcdf01 G y) (by linarith [hFG y])
              unfold choquet
              apply add_le_add
              · exact setIntegral_mono (hint g hg F hF).1 (hint g hg G hG).1 (fun y => by linarith [hp y])
              · exact setIntegral_mono (hint g hg F hF).2 (hint g hg G hG).2 hp
            have hkey : ∀ (P : ProbabilityMeasure ℝ) (x : ℝ), (P : Measure ℝ) {ω | x < id ω}
                = ENNReal.ofReal (1 - ProbabilityTheory.cdf (P : Measure ℝ) x) := by
              intro P x
              have e : {ω : ℝ | x < id ω} = (Set.Iic x)ᶜ := by ext; simp
              rw [e, prob_compl_eq_one_sub measurableSet_Iic, ProbabilityTheory.cdf_eq_real,
                ENNReal.ofReal_sub _ measureReal_nonneg, ENNReal.ofReal_one, ofReal_measureReal]
            have hst_cdf : ∀ F G : ProbabilityMeasure ℝ, StLE F G ↔
                ∀ y, ProbabilityTheory.cdf (G : Measure ℝ) y ≤ ProbabilityTheory.cdf (F : Measure ℝ) y := by
              intro F G
              unfold StLE StochasticOrders.Usual.UsualOrder
              simp only [hkey]
              constructor
              · intro H y
                have := H y
                rw [ENNReal.ofReal_le_ofReal_iff (hcdf01 G y).1] at this
                linarith
              · intro H y
                exact ENNReal.ofReal_le_ofReal (by linarith [H y])
            have hq_cdf : ∀ P Q : ProbabilityMeasure ℝ,
                (∀ᵐ p ∂(volume.restrict (Set.Ioo (0:ℝ) 1)), leftQuantile P p ≤ leftQuantile Q p) →
                ∀ x, ProbabilityTheory.cdf (Q : Measure ℝ) x ≤ ProbabilityTheory.cdf (P : Measure ℝ) x := by
              intro P Q hPQ x
              by_contra hlt
              push_neg at hlt
              have ha0 : 0 ≤ ProbabilityTheory.cdf (P : Measure ℝ) x := ProbabilityTheory.cdf_nonneg _ _
              have hb1 : ProbabilityTheory.cdf (Q : Measure ℝ) x ≤ 1 := ProbabilityTheory.cdf_le_one _ _
              have hall : ∀ p ∈ Set.Ioo (ProbabilityTheory.cdf (P : Measure ℝ) x)
                  (ProbabilityTheory.cdf (Q : Measure ℝ) x), leftQuantile Q p < leftQuantile P p := by
                intro p hp
                have hp0 : 0 < p := lt_of_le_of_lt ha0 hp.1
                have hp1 : p < 1 := lt_of_lt_of_le hp.2 hb1
                have hQ : leftQuantile Q p ≤ x := by
                  apply csInf_le
                  · obtain ⟨y0, hy0⟩ : ∃ y0, ProbabilityTheory.cdf (Q : Measure ℝ) y0 < p :=
                      ((ProbabilityTheory.tendsto_cdf_atBot (Q : Measure ℝ)).eventually
                        (gt_mem_nhds hp0)).exists
                    refine ⟨y0, fun y hy => ?_⟩
                    by_contra hyy
                    push_neg at hyy
                    have := (ProbabilityTheory.cdf (Q : Measure ℝ)).mono hyy.le
                    simp only [Set.mem_setOf_eq] at hy
                    linarith
                  · exact hp.2.le
                have hP : x < leftQuantile P p := by
                  have hrc := (ProbabilityTheory.cdf (P : Measure ℝ)).right_continuous' x
                  rw [Metric.continuousWithinAt_iff] at hrc
                  obtain ⟨δ, hδ, hδlt⟩ := hrc (p - ProbabilityTheory.cdf (P : Measure ℝ) x)
                    (by linarith [hp.1])
                  have hd := hδlt (x := x + δ / 2) (by simp only [Set.mem_Ici]; linarith)
                    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
                  rw [Real.dist_eq, abs_lt] at hd
                  have hne : {y | p ≤ ProbabilityTheory.cdf (P : Measure ℝ) y}.Nonempty :=
                    (((ProbabilityTheory.tendsto_cdf_atTop (P : Measure ℝ)).eventually
                        (lt_mem_nhds hp1)).exists).imp fun y hy => hy.le
                  have : x + δ / 2 ≤ leftQuantile P p := by
                    apply le_csInf hne
                    intro y hy
                    by_contra hyy
                    push_neg at hyy
                    have := (ProbabilityTheory.cdf (P : Measure ℝ)).mono hyy.le
                    simp only [Set.mem_setOf_eq] at hy
                    linarith [hd.2]
                  linarith
                linarith
              have hnull : volume (Set.Ioo (ProbabilityTheory.cdf (P : Measure ℝ) x)
                  (ProbabilityTheory.cdf (Q : Measure ℝ) x)) = 0 := by
                have h2 := (ae_restrict_iff' measurableSet_Ioo).1 hPQ
                rw [ae_iff] at h2
                apply measure_mono_null _ h2
                intro p hp
                simp only [Set.mem_setOf_eq, _root_.not_imp, not_le]
                exact ⟨⟨lt_of_le_of_lt ha0 hp.1, lt_of_lt_of_le hp.2 hb1⟩, hall p hp⟩
              rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
              linarith
            have hgal : ∀ (A : ProbabilityMeasure ℝ), ∀ p ∈ Set.Ioo (0:ℝ) 1, ∀ x : ℝ,
                leftQuantile A p ≤ x ↔ p ≤ ProbabilityTheory.cdf (A : Measure ℝ) x := by
              intro A p hp x
              have hne : {y | p ≤ ProbabilityTheory.cdf (A : Measure ℝ) y}.Nonempty :=
                (((ProbabilityTheory.tendsto_cdf_atTop (A : Measure ℝ)).eventually
                    (lt_mem_nhds hp.2)).exists).imp fun y hy => hy.le
              have hbdd : BddBelow {y | p ≤ ProbabilityTheory.cdf (A : Measure ℝ) y} := by
                obtain ⟨y0, hy0⟩ : ∃ y0, ProbabilityTheory.cdf (A : Measure ℝ) y0 < p :=
                  ((ProbabilityTheory.tendsto_cdf_atBot (A : Measure ℝ)).eventually
                    (gt_mem_nhds hp.1)).exists
                refine ⟨y0, fun y hy => ?_⟩
                by_contra hyy
                push_neg at hyy
                have := (ProbabilityTheory.cdf (A : Measure ℝ)).mono hyy.le
                simp only [Set.mem_setOf_eq] at hy
                linarith
              constructor
              · intro hq
                -- right-continuity
                by_contra hlt
                push_neg at hlt
                have hrc := (ProbabilityTheory.cdf (A : Measure ℝ)).right_continuous' x
                rw [Metric.continuousWithinAt_iff] at hrc
                obtain ⟨δ, hδ, hδlt⟩ := hrc (p - ProbabilityTheory.cdf (A : Measure ℝ) x)
                  (by linarith)
                have hd := hδlt (x := x + δ / 2) (by simp only [Set.mem_Ici]; linarith)
                  (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
                rw [Real.dist_eq, abs_lt] at hd
                have : x + δ / 2 ≤ leftQuantile A p := by
                  apply le_csInf hne
                  intro y hy
                  by_contra hyy
                  push_neg at hyy
                  have := (ProbabilityTheory.cdf (A : Measure ℝ)).mono hyy.le
                  simp only [Set.mem_setOf_eq] at hy
                  linarith [hd.2]
                linarith
              · intro hx
                exact csInf_le hbdd hx
            have hmq : ∀ (A : ProbabilityMeasure ℝ), ∀ u ∈ Set.Ioo (0:ℝ) 1, ∀ v ∈ Set.Ioo (0:ℝ) 1,
                u ≤ v → leftQuantile A u ≤ leftQuantile A v := fun A u hu v hv huv =>
              (hgal A u hu _).2 (le_trans huv ((hgal A v hv _).1 le_rfl))
            -- left continuity, in the form needed
            have hlc : ∀ (A : ProbabilityMeasure ℝ), ∀ p ∈ Set.Ioo (0:ℝ) 1, ∀ d : ℝ, 0 < d →
                ∃ u, 0 < u ∧ u < p ∧ leftQuantile A p - d < leftQuantile A u := by
              intro A p hp d hd
              have h1 : ¬ p ≤ ProbabilityTheory.cdf (A : Measure ℝ) (leftQuantile A p - d) := by
                rw [← hgal A p hp]; linarith
              push_neg at h1
              refine ⟨(max (ProbabilityTheory.cdf (A : Measure ℝ) (leftQuantile A p - d)) 0 + p) / 2,
                ?_, ?_, ?_⟩
              · have := le_max_right (ProbabilityTheory.cdf (A : Measure ℝ) (leftQuantile A p - d)) 0
                linarith [hp.1]
              · have := max_lt h1 hp.1
                linarith
              · have hm := max_lt h1 hp.1
                have hc := le_max_left (ProbabilityTheory.cdf (A : Measure ℝ) (leftQuantile A p - d)) 0
                have hu : (max (ProbabilityTheory.cdf (A : Measure ℝ) (leftQuantile A p - d)) 0 + p) / 2
                    ∈ Set.Ioo (0:ℝ) 1 := by
                  have := le_max_right (ProbabilityTheory.cdf (A : Measure ℝ) (leftQuantile A p - d)) 0
                  constructor <;> linarith [hp.1, hp.2]
                by_contra hle
                push_neg at hle
                have := (hgal A _ hu _).1 hle
                linarith
            have hspec0 : ∀ A B : ProbabilityMeasure ℝ, ∃ S : ProbabilityMeasure ℝ, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
                leftQuantile S p = leftQuantile A p + leftQuantile B p := by
              intro A B
              set f : ℝ → ℝ := fun u => leftQuantile A u + leftQuantile B u with hf
              have hfm : MonotoneOn f (Set.Ioo 0 1) := fun u hu v hv huv =>
                add_le_add (hmq A u hu v hv huv) (hmq B u hu v hv huv)
              have hae : AEMeasurable f (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
                aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hfm
              have hprob : IsProbabilityMeasure ((volume.restrict (Set.Ioo (0:ℝ) 1)).map f) := by
                constructor
                rw [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ, Set.preimage_univ,
                  Measure.restrict_apply_univ, Real.volume_Ioo]
                simp
              let S : ProbabilityMeasure ℝ := ⟨_, hprob⟩
              refine ⟨S, ?_⟩
              intro p hp
              have hcdf : ∀ x, ProbabilityTheory.cdf (S : Measure ℝ) x
                  = (volume (f ⁻¹' Set.Iic x ∩ Set.Ioo 0 1)).toReal := by
                intro x
                rw [ProbabilityTheory.cdf_eq_real]
                show (Measure.map f (volume.restrict (Set.Ioo (0:ℝ) 1))).real (Set.Iic x) = _
                rw [measureReal_def,
                  Measure.map_apply_of_aemeasurable hae measurableSet_Iic,
                  Measure.restrict_apply' measurableSet_Ioo]
              have hfin : ∀ x, volume (f ⁻¹' Set.Iic x ∩ Set.Ioo (0:ℝ) 1) ≠ ⊤ := by
                intro x
                refine ne_top_of_le_ne_top (b := volume (Set.Ioo (0:ℝ) 1)) ?_ (measure_mono Set.inter_subset_right)
                rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
              have key : ∀ x, p ≤ ProbabilityTheory.cdf (S : Measure ℝ) x
                  ↔ f p ≤ x := by
                intro x
                rw [hcdf]
                constructor
                · intro hle
                  by_contra hlt
                  push_neg at hlt
                  obtain ⟨uA, huA0, huAp, huA⟩ := hlc A p hp ((f p - x) / 2) (by linarith)
                  obtain ⟨uB, huB0, huBp, huB⟩ := hlc B p hp ((f p - x) / 2) (by linarith)
                  have hsub : f ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 ⊆ Set.Ioo 0 (max uA uB) := by
                    intro v hv
                    refine ⟨hv.2.1, ?_⟩
                    by_contra hvu
                    push_neg at hvu
                    have h1 := hmq A uA ⟨huA0, by linarith [hp.2]⟩ v hv.2 (le_trans (le_max_left _ _) hvu)
                    have h2 := hmq B uB ⟨huB0, by linarith [hp.2]⟩ v hv.2 (le_trans (le_max_right _ _) hvu)
                    have h3 : f v ≤ x := hv.1
                    simp only [hf] at h3 hlt
                    linarith
                  have := ENNReal.toReal_le_of_le_ofReal (le_max_of_le_left huA0.le)
                    ((measure_mono hsub).trans (by rw [Real.volume_Ioo, sub_zero]))
                  have := max_lt huAp huBp
                  linarith
                · intro hle
                  have hsub : Set.Ioc 0 p ⊆ f ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 := by
                    intro v hv
                    have hv' : v ∈ Set.Ioo (0:ℝ) 1 := ⟨hv.1, lt_of_le_of_lt hv.2 hp.2⟩
                    exact ⟨le_trans (hfm hv' hp hv.2) hle, hv'⟩
                  rw [← ENNReal.ofReal_le_iff_le_toReal (hfin x)]
                  have := measure_mono (μ := volume) hsub
                  rwa [Real.volume_Ioc, sub_zero] at this
              show sInf {x | p ≤ ProbabilityTheory.cdf (S : Measure ℝ) x} = f p
              have : {x | p ≤ ProbabilityTheory.cdf (S : Measure ℝ) x}
                  = Set.Ici (f p) := by
                ext x; exact key x
              rw [this, csInf_Ici]
            have hspec : ∀ A B : ProbabilityMeasure ℝ, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
                leftQuantile (comonoSum A B) p = leftQuantile A p + leftQuantile B p := by
              intro A B
              exact Classical.epsilon_spec (p := fun H : ProbabilityMeasure ℝ => ∀ p ∈ Set.Ioo (0 : ℝ) 1,
                leftQuantile H p = leftQuantile A p + leftQuantile B p) (hspec0 A B)
            have hqbd : ∀ F : ProbabilityMeasure ℝ, ∀ a b : ℝ, (F : Measure ℝ) (Set.Icc a b) = 1 →
                ∀ p ∈ Set.Ioo (0:ℝ) 1, a ≤ leftQuantile F p ∧ leftQuantile F p ≤ b := by
              intro F a b hab p hp
              constructor
              · by_contra hlt
                push_neg at hlt
                have h1 := (hgal F p hp _).1 le_rfl
                rw [hlow F a b hab _ hlt] at h1
                linarith [hp.1]
              · exact (hgal F p hp b).2 (by rw [hhigh F a b hab b le_rfl]; exact hp.2.le)
            have hMq : ∀ S : ProbabilityMeasure ℝ, ∀ a b : ℝ,
                (∀ p ∈ Set.Ioo (0:ℝ) 1, a ≤ leftQuantile S p ∧ leftQuantile S p ≤ b) → S ∈ Minf := by
              intro S a b hq
              refine ⟨a - 1, b, ?_⟩
              have hb : ProbabilityTheory.cdf (S : Measure ℝ) b = 1 := by
                apply le_antisymm (ProbabilityTheory.cdf_le_one _ _)
                by_contra hlt
                push_neg at hlt
                have hc0 := ProbabilityTheory.cdf_nonneg (S : Measure ℝ) b
                have hp : (ProbabilityTheory.cdf (S : Measure ℝ) b + 1) / 2 ∈ Set.Ioo (0:ℝ) 1 := by
                  constructor <;> linarith
                have := (hgal S _ hp b).1 (hq _ hp).2
                linarith
              have ha : ProbabilityTheory.cdf (S : Measure ℝ) (a - 1) = 0 := by
                apply le_antisymm _ (ProbabilityTheory.cdf_nonneg _ _)
                by_contra hlt
                push_neg at hlt
                have hp : min (ProbabilityTheory.cdf (S : Measure ℝ) (a - 1)) (1/2) ∈ Set.Ioo (0:ℝ) 1 := by
                  constructor
                  · exact lt_min hlt (by norm_num)
                  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
                have := (hgal S _ hp (a - 1)).2 (min_le_left _ _)
                linarith [(hq _ hp).1]
              rw [ProbabilityTheory.cdf_eq_real, measureReal_def] at ha hb
              have hb' : (S : Measure ℝ) (Set.Iic b) = 1 := by
                rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), hb, ENNReal.ofReal_one]
              have ha' : (S : Measure ℝ) (Set.Iic (a - 1)) = 0 := by
                rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ha, ENNReal.ofReal_zero]
              apply le_antisymm prob_le_one
              calc (1 : ENNReal) = (S : Measure ℝ) (Set.Iic b) := hb'.symm
                _ ≤ (S : Measure ℝ) (Set.Icc (a - 1) b ∪ Set.Iic (a - 1)) := by
                    apply measure_mono
                    intro z hz
                    by_cases hza : a - 1 ≤ z
                    · exact Or.inl ⟨hza, hz⟩
                    · exact Or.inr (le_of_lt (not_le.mp hza))
                _ ≤ (S : Measure ℝ) (Set.Icc (a - 1) b) + (S : Measure ℝ) (Set.Iic (a - 1)) :=
                    measure_union_le _ _
                _ = (S : Measure ℝ) (Set.Icc (a - 1) b) := by rw [ha', add_zero]
            have hSMg : ∀ F ∈ Minf, ∀ G ∈ Minf, comonoSum F G ∈ Minf := by
              intro F hF G hG
              obtain ⟨a1, b1, h1⟩ := hF
              obtain ⟨a2, b2, h2⟩ := hG
              refine hMq _ (a1 + a2) (b1 + b2) (fun p hp => ?_)
              rw [hspec F G p hp]
              have e1 := hqbd F a1 b1 h1 p hp
              have e2 := hqbd G a2 b2 h2 p hp
              constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
            -- comonotonic additivity of the Choquet integral
            have hadd_chg : ∀ F ∈ Minf, ∀ G ∈ Minf, ∀ g : ℝ → ℝ, IsH g →
                choquet g (comonoSum F G) = choquet g F + choquet g G := by
              intro F hF G hG
              have hSM := hSMg F hF G hG
              intro g hg
              classical
              have hg1 : g 1 = 1 := hg.2.2
              have hg0 : g 0 = 0 := hg.2.1
              have hPanti : ∀ t u w : ℝ, 0 ≤ u → u ≤ w → w ≤ 1 → t < g (1 - w) → t < g (1 - u) := by
                intro t u w hu huw hw h
                exact lt_of_lt_of_le h (hg.1 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
                  (by linarith))
              set Mq : (ℝ → ℝ) → ℝ → ℝ := fun q t =>
                if (∃ v ∈ Set.Ioo (0:ℝ) 1, ¬ t < g (1 - v)) then
                  sInf (q '' {v | v ∈ Set.Ioo (0:ℝ) 1 ∧ ¬ t < g (1 - v)})
                else sSup (q '' Set.Ioo (0:ℝ) 1) with hMq_def
              have hlevel : ∀ X : ProbabilityMeasure ℝ, ∀ a b : ℝ, (X : Measure ℝ) (Set.Icc a b) = 1 →
                  ∀ t ∈ Set.Ioo (0:ℝ) 1,
                  (volume.restrict (Set.Icc a b)).real
                    {x | t < g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x)}
                    = Mq (leftQuantile X) t - a := by
                intro X a b hab t ht
                have hqb := hqbd X a b hab
                obtain ⟨hMa, hMb, hin, hout⟩ : a ≤ Mq (leftQuantile X) t ∧ Mq (leftQuantile X) t ≤ b ∧
                    (∀ x, a ≤ x → x < Mq (leftQuantile X) t →
                      t < g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x)) ∧
                    (∀ x, t < g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x) →
                      x ≤ Mq (leftQuantile X) t) := by
                  by_cases hV : ∃ v ∈ Set.Ioo (0:ℝ) 1, ¬ t < g (1 - v)
                  · have hM : Mq (leftQuantile X) t = sInf (leftQuantile X ''
                        {v | v ∈ Set.Ioo (0:ℝ) 1 ∧ ¬ t < g (1 - v)}) := by
                      simp only [hMq_def, if_pos hV]
                    rw [hM]
                    obtain ⟨v0, hv0, hv0'⟩ := hV
                    have hne : (leftQuantile X ''
                        {v | v ∈ Set.Ioo (0:ℝ) 1 ∧ ¬ t < g (1 - v)}).Nonempty :=
                      ⟨_, v0, ⟨hv0, hv0'⟩, rfl⟩
                    have hbdd : BddBelow (leftQuantile X ''
                        {v | v ∈ Set.Ioo (0:ℝ) 1 ∧ ¬ t < g (1 - v)}) :=
                      ⟨a, by rintro _ ⟨v, hv, rfl⟩; exact (hqb v hv.1).1⟩
                    refine ⟨le_csInf hne (by rintro _ ⟨v, hv, rfl⟩; exact (hqb v hv.1).1),
                      (csInf_le hbdd ⟨v0, ⟨hv0, hv0'⟩, rfl⟩).trans (hqb v0 hv0).2, ?_, ?_⟩
                    · intro x hax hxM
                      by_contra hP
                      have hw0 := ProbabilityTheory.cdf_nonneg (X : Measure ℝ) x
                      have hw1 := ProbabilityTheory.cdf_le_one (X : Measure ℝ) x
                      by_cases hz : ProbabilityTheory.cdf (X : Measure ℝ) x ≤ 0
                      · have : ProbabilityTheory.cdf (X : Measure ℝ) x = 0 := le_antisymm hz hw0
                        rw [this, sub_zero, hg1] at hP
                        exact hP ht.2
                      · by_cases ho : 1 ≤ ProbabilityTheory.cdf (X : Measure ℝ) x
                        · have h1 : leftQuantile X v0 ≤ x := (hgal X v0 hv0 x).2 (by linarith [hv0.2])
                          have := csInf_le hbdd ⟨v0, ⟨hv0, hv0'⟩, rfl⟩
                          linarith
                        · push_neg at hz ho
                          have hmem : ProbabilityTheory.cdf (X : Measure ℝ) x ∈ Set.Ioo (0:ℝ) 1 := ⟨hz, ho⟩
                          have h1 : leftQuantile X (ProbabilityTheory.cdf (X : Measure ℝ) x) ≤ x :=
                            (hgal X _ hmem x).2 le_rfl
                          have := csInf_le hbdd ⟨_, ⟨hmem, hP⟩, rfl⟩
                          linarith
                    · intro x hP
                      apply le_csInf hne
                      rintro _ ⟨v, ⟨hv, hv'⟩, rfl⟩
                      by_contra hlt
                      push_neg at hlt
                      have : v ≤ ProbabilityTheory.cdf (X : Measure ℝ) x := (hgal X v hv x).1 hlt.le
                      exact hv' (hPanti t v _ hv.1.le this (ProbabilityTheory.cdf_le_one _ _) hP)
                  · have hV' : ∀ v ∈ Set.Ioo (0:ℝ) 1, t < g (1 - v) := by
                      intro v hv; by_contra h; exact hV ⟨v, hv, h⟩
                    have hM : Mq (leftQuantile X) t = sSup (leftQuantile X '' Set.Ioo (0:ℝ) 1) := by
                      simp only [hMq_def, if_neg hV]
                    rw [hM]
                    have hh : (1/2 : ℝ) ∈ Set.Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
                    have hne : (leftQuantile X '' Set.Ioo (0:ℝ) 1).Nonempty := ⟨_, _, hh, rfl⟩
                    have hbdd : BddAbove (leftQuantile X '' Set.Ioo (0:ℝ) 1) :=
                      ⟨b, by rintro _ ⟨v, hv, rfl⟩; exact (hqb v hv).2⟩
                    refine ⟨(hqb _ hh).1.trans (le_csSup hbdd ⟨_, hh, rfl⟩),
                      csSup_le hne (by rintro _ ⟨v, hv, rfl⟩; exact (hqb v hv).2), ?_, ?_⟩
                    · intro x hax hxM
                      obtain ⟨_, ⟨v, hv, rfl⟩, hxv⟩ := exists_lt_of_lt_csSup hne hxM
                      have hw : ProbabilityTheory.cdf (X : Measure ℝ) x < v := by
                        by_contra h
                        push_neg at h
                        exact absurd ((hgal X v hv x).2 h) (not_le.mpr hxv)
                      by_cases hw0 : ProbabilityTheory.cdf (X : Measure ℝ) x ≤ 0
                      · have : ProbabilityTheory.cdf (X : Measure ℝ) x = 0 :=
                          le_antisymm hw0 (ProbabilityTheory.cdf_nonneg _ _)
                        rw [this, sub_zero, hg1]; exact ht.2
                      · exact hV' _ ⟨lt_of_not_ge hw0, hw.trans hv.2⟩
                    · intro x hP
                      have hw1 : ProbabilityTheory.cdf (X : Measure ℝ) x < 1 := by
                        by_contra h
                        push_neg at h
                        have : ProbabilityTheory.cdf (X : Measure ℝ) x = 1 :=
                          le_antisymm (ProbabilityTheory.cdf_le_one _ _) h
                        rw [this, sub_self, hg0] at hP
                        linarith [ht.1]
                      have hc0 := ProbabilityTheory.cdf_nonneg (X : Measure ℝ) x
                      have hv : (ProbabilityTheory.cdf (X : Measure ℝ) x + 1) / 2 ∈ Set.Ioo (0:ℝ) 1 :=
                        ⟨by linarith, by linarith⟩
                      have : x < leftQuantile X ((ProbabilityTheory.cdf (X : Measure ℝ) x + 1) / 2) := by
                        by_contra h
                        push_neg at h
                        have := (hgal X _ hv x).1 h
                        linarith
                      exact this.le.trans (le_csSup hbdd ⟨_, hv, rfl⟩)
                have hset1 : Set.Ico a (Mq (leftQuantile X) t) ⊆
                    {x | t < g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x)} ∩ Set.Icc a b :=
                  fun x hx => ⟨hin x hx.1 hx.2, hx.1, hx.2.le.trans hMb⟩
                have hset2 : {x | t < g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x)} ∩ Set.Icc a b ⊆
                    Set.Icc a (Mq (leftQuantile X) t) := fun x hx => ⟨hx.2.1, hout x hx.1⟩
                rw [measureReal_def, Measure.restrict_apply' measurableSet_Icc]
                have e : volume ({x | t < g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x)} ∩ Set.Icc a b)
                    = ENNReal.ofReal (Mq (leftQuantile X) t - a) := by
                  apply le_antisymm
                  · have := measure_mono (μ := volume) hset2
                    rwa [Real.volume_Icc] at this
                  · have := measure_mono (μ := volume) hset1
                    rwa [Real.volume_Ico] at this
                rw [e, ENNReal.toReal_ofReal (by linarith)]
              have hrep : ∀ X ∈ Minf, choquet g X = ∫ t in Set.Ioo (0:ℝ) 1, Mq (leftQuantile X) t ∧
                  IntegrableOn (fun t => Mq (leftQuantile X) t) (Set.Ioo (0:ℝ) 1) := by
                intro X hX
                obtain ⟨a0, b0, hab0⟩ := hX
                have ha : min a0 0 ≤ 0 := min_le_right _ _
                have hb : (0:ℝ) ≤ max b0 0 := le_max_right _ _
                have hab : (X : Measure ℝ) (Set.Icc (min a0 0) (max b0 0)) = 1 :=
                  le_antisymm prob_le_one (hab0 ▸ measure_mono
                    (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)))
                set a := min a0 0
                set b := max b0 0
                set ψ : ℝ → ℝ := fun x => g (1 - ProbabilityTheory.cdf (X : Measure ℝ) x) with hψ
                have hmeas : Measurable ψ := (hanti g hg X).measurable
                have hbd : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
                  have := hgb g hg _ (hcdf01 X x)
                  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
                have hψint : ∀ s : Set ℝ, volume s ≠ ⊤ → IntegrableOn ψ s := fun s hs =>
                  Measure.integrableOn_of_bounded hs hmeas.aestronglyMeasurable (ae_of_all _ hbd)
                have hlowψ : ∀ x, x < a → ψ x = 1 := by
                  intro x hx; simp only [hψ]; rw [hlow X a b hab x hx, sub_zero, hg1]
                have hhighψ : ∀ x, b ≤ x → ψ x = 0 := by
                  intro x hx; simp only [hψ]; rw [hhigh X a b hab x hx, sub_self, hg0]
                have s1 : ∫ x in Set.Iic (0:ℝ), (ψ x - 1) = ∫ x in Set.Icc a 0, (ψ x - 1) :=
                  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
                    (fun x hx => hx.2) (fun x hx => by
                      have : x < a := by
                        by_contra h; push_neg at h; exact hx.2 ⟨h, hx.1⟩
                      rw [hlowψ x this, sub_self])
                have s2 : ∫ x in Set.Ioi (0:ℝ), ψ x = ∫ x in Set.Ioc 0 b, ψ x :=
                  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
                    (fun x hx => hx.1) (fun x hx => by
                      have : b ≤ x := by
                        by_contra h; push_neg at h; exact hx.2 ⟨hx.1, h.le⟩
                      rw [hhighψ x this])
                have fin1 : volume (Set.Icc a 0) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
                have fin2 : volume (Set.Ioc 0 b) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
                have fin3 : volume (Set.Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
                have s3 : ∫ x in Set.Icc a 0, (ψ x - 1) = (∫ x in Set.Icc a 0, ψ x) - (0 - a) := by
                  rw [integral_sub (hψint _ fin1) (integrableOn_const fin1), setIntegral_const,
                    Real.volume_real_Icc, max_eq_left (by linarith)]
                  simp
                have s4 : ∫ x in Set.Icc a b, ψ x = (∫ x in Set.Icc a 0, ψ x) + ∫ x in Set.Ioc 0 b, ψ x := by
                  rw [← Set.Icc_union_Ioc_eq_Icc ha hb]
                  exact setIntegral_union (Set.disjoint_left.2 (fun x h1 h2 => not_lt.2 h1.2 h2.1))
                    measurableSet_Ioc (hψint _ fin1) (hψint _ fin2)
                have s5 : ∫ x in Set.Icc a b, ψ x =
                    ∫ t in Set.Ioi (0:ℝ), (volume.restrict (Set.Icc a b)).real {x | t < ψ x} :=
                  Integrable.integral_eq_integral_meas_lt (hψint _ fin3)
                    (ae_of_all _ (fun x => (hgb g hg _ (hcdf01 X x)).1))
                have s6 : ∫ t in Set.Ioi (0:ℝ), (volume.restrict (Set.Icc a b)).real {x | t < ψ x} =
                    ∫ t in Set.Ioo (0:ℝ) 1, (volume.restrict (Set.Icc a b)).real {x | t < ψ x} :=
                  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
                    Set.Ioo_subset_Ioi_self (fun t ht => by
                      have h1 : 1 ≤ t := by
                        by_contra h; push_neg at h; exact ht.2 ⟨ht.1, h⟩
                      have : {x | t < ψ x} = ∅ := by
                        ext x
                        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                        have := hbd x
                        rw [Real.norm_eq_abs, abs_le] at this
                        linarith [this.2]
                      rw [this, measureReal_empty])
                have s7 : ∫ t in Set.Ioo (0:ℝ) 1, (volume.restrict (Set.Icc a b)).real {x | t < ψ x} =
                    ∫ t in Set.Ioo (0:ℝ) 1, (Mq (leftQuantile X) t - a) :=
                  setIntegral_congr_fun measurableSet_Ioo (fun t ht => hlevel X a b hab t ht)
                have hfinr : ∀ s : Set ℝ, (volume.restrict (Set.Icc a b)) s ≠ ⊤ := by
                  intro s
                  rw [Measure.restrict_apply' measurableSet_Icc]
                  exact ne_top_of_le_ne_top fin3 (measure_mono Set.inter_subset_right)
                have hmanti : Antitone (fun t => (volume.restrict (Set.Icc a b)).real {x | t < ψ x}) :=
                  fun t t' htt' => measureReal_mono (fun x hx => lt_of_le_of_lt htt' hx) (hfinr _)
                have hmint : IntegrableOn (fun t => (volume.restrict (Set.Icc a b)).real {x | t < ψ x})
                    (Set.Ioo (0:ℝ) 1) :=
                  ((hmanti.antitoneOn _).integrableOn_isCompact isCompact_Icc).mono_set
                    Set.Ioo_subset_Icc_self
                have hMint : IntegrableOn (fun t => Mq (leftQuantile X) t) (Set.Ioo (0:ℝ) 1) := by
                  have h2 : IntegrableOn (fun t => (volume.restrict (Set.Icc a b)).real {x | t < ψ x} + a)
                      (Set.Ioo (0:ℝ) 1) := hmint.add (integrableOn_const (by
                        rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
                  refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioo
                  simp only
                  rw [hlevel X a b hab t ht]; ring
                refine ⟨?_, hMint⟩
                have s8 : ∫ t in Set.Ioo (0:ℝ) 1, (Mq (leftQuantile X) t - a) =
                    (∫ t in Set.Ioo (0:ℝ) 1, Mq (leftQuantile X) t) - a := by
                  rw [integral_sub hMint (integrableOn_const (by
                        rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)), setIntegral_const,
                    Real.volume_real_Ioo]
                  simp
                show (∫ x in Set.Iic (0:ℝ), (ψ x - 1)) + ∫ x in Set.Ioi (0:ℝ), ψ x = _
                rw [s1, s2, s3]
                have := s4.symm.trans (s5.trans (s6.trans (s7.trans s8)))
                linarith
              have hMadd : ∀ t ∈ Set.Ioo (0:ℝ) 1, Mq (leftQuantile (comonoSum F G)) t =
                  Mq (leftQuantile F) t + Mq (leftQuantile G) t := by
                intro t ht
                obtain ⟨a1, b1, h1⟩ := hF
                obtain ⟨a2, b2, h2⟩ := hG
                have hq1 := hqbd F a1 b1 h1
                have hq2 := hqbd G a2 b2 h2
                by_cases hV : ∃ v ∈ Set.Ioo (0:ℝ) 1, ¬ t < g (1 - v)
                · simp only [hMq_def, if_pos hV]
                  obtain ⟨v0, hv0, hv0'⟩ := hV
                  set V := {v | v ∈ Set.Ioo (0:ℝ) 1 ∧ ¬ t < g (1 - v)} with hVdef
                  have hv0V : v0 ∈ V := ⟨hv0, hv0'⟩
                  have hneF : (leftQuantile F '' V).Nonempty := ⟨_, v0, hv0V, rfl⟩
                  have hneG : (leftQuantile G '' V).Nonempty := ⟨_, v0, hv0V, rfl⟩
                  have hneS : (leftQuantile (comonoSum F G) '' V).Nonempty := ⟨_, v0, hv0V, rfl⟩
                  have hbF : BddBelow (leftQuantile F '' V) :=
                    ⟨a1, by rintro _ ⟨v, hv, rfl⟩; exact (hq1 v hv.1).1⟩
                  have hbG : BddBelow (leftQuantile G '' V) :=
                    ⟨a2, by rintro _ ⟨v, hv, rfl⟩; exact (hq2 v hv.1).1⟩
                  have hbS : BddBelow (leftQuantile (comonoSum F G) '' V) :=
                    ⟨a1 + a2, by
                      rintro _ ⟨v, hv, rfl⟩
                      rw [hspec F G v hv.1]
                      linarith [(hq1 v hv.1).1, (hq2 v hv.1).1]⟩
                  apply le_antisymm
                  · by_contra hlt
                    push_neg at hlt
                    obtain ⟨_, ⟨v1, hv1, rfl⟩, hl1⟩ := exists_lt_of_csInf_lt hneF
                      (show sInf (leftQuantile F '' V) < sInf (leftQuantile F '' V) +
                        (sInf (leftQuantile (comonoSum F G) '' V) - sInf (leftQuantile F '' V)
                          - sInf (leftQuantile G '' V)) / 2 by linarith)
                    obtain ⟨_, ⟨v2, hv2, rfl⟩, hl2⟩ := exists_lt_of_csInf_lt hneG
                      (show sInf (leftQuantile G '' V) < sInf (leftQuantile G '' V) +
                        (sInf (leftQuantile (comonoSum F G) '' V) - sInf (leftQuantile F '' V)
                          - sInf (leftQuantile G '' V)) / 2 by linarith)
                    rcases le_total v1 v2 with h12 | h12
                    · have := csInf_le hbS ⟨v1, hv1, rfl⟩
                      rw [hspec F G v1 hv1.1] at this
                      have := hmq G v1 hv1.1 v2 hv2.1 h12
                      linarith
                    · have := csInf_le hbS ⟨v2, hv2, rfl⟩
                      rw [hspec F G v2 hv2.1] at this
                      have := hmq F v2 hv2.1 v1 hv1.1 h12
                      linarith
                  · apply le_csInf hneS
                    rintro _ ⟨v, hv, rfl⟩
                    rw [hspec F G v hv.1]
                    exact add_le_add (csInf_le hbF ⟨v, hv, rfl⟩) (csInf_le hbG ⟨v, hv, rfl⟩)
                · simp only [hMq_def, if_neg hV]
                  have hh : (1/2 : ℝ) ∈ Set.Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
                  have hneF : (leftQuantile F '' Set.Ioo (0:ℝ) 1).Nonempty := ⟨_, _, hh, rfl⟩
                  have hneG : (leftQuantile G '' Set.Ioo (0:ℝ) 1).Nonempty := ⟨_, _, hh, rfl⟩
                  have hneS : (leftQuantile (comonoSum F G) '' Set.Ioo (0:ℝ) 1).Nonempty :=
                    ⟨_, _, hh, rfl⟩
                  have hbF : BddAbove (leftQuantile F '' Set.Ioo (0:ℝ) 1) :=
                    ⟨b1, by rintro _ ⟨v, hv, rfl⟩; exact (hq1 v hv).2⟩
                  have hbG : BddAbove (leftQuantile G '' Set.Ioo (0:ℝ) 1) :=
                    ⟨b2, by rintro _ ⟨v, hv, rfl⟩; exact (hq2 v hv).2⟩
                  have hbS : BddAbove (leftQuantile (comonoSum F G) '' Set.Ioo (0:ℝ) 1) :=
                    ⟨b1 + b2, by
                      rintro _ ⟨v, hv, rfl⟩
                      rw [hspec F G v hv]
                      linarith [(hq1 v hv).2, (hq2 v hv).2]⟩
                  apply le_antisymm
                  · apply csSup_le hneS
                    rintro _ ⟨v, hv, rfl⟩
                    rw [hspec F G v hv]
                    exact add_le_add (le_csSup hbF ⟨v, hv, rfl⟩) (le_csSup hbG ⟨v, hv, rfl⟩)
                  · by_contra hlt
                    push_neg at hlt
                    obtain ⟨_, ⟨v1, hv1, rfl⟩, hl1⟩ := exists_lt_of_lt_csSup hneF
                      (show sSup (leftQuantile F '' Set.Ioo (0:ℝ) 1) -
                        (sSup (leftQuantile F '' Set.Ioo (0:ℝ) 1) + sSup (leftQuantile G '' Set.Ioo (0:ℝ) 1)
                          - sSup (leftQuantile (comonoSum F G) '' Set.Ioo (0:ℝ) 1)) / 2
                          < sSup (leftQuantile F '' Set.Ioo (0:ℝ) 1) by linarith)
                    obtain ⟨_, ⟨v2, hv2, rfl⟩, hl2⟩ := exists_lt_of_lt_csSup hneG
                      (show sSup (leftQuantile G '' Set.Ioo (0:ℝ) 1) -
                        (sSup (leftQuantile F '' Set.Ioo (0:ℝ) 1) + sSup (leftQuantile G '' Set.Ioo (0:ℝ) 1)
                          - sSup (leftQuantile (comonoSum F G) '' Set.Ioo (0:ℝ) 1)) / 2
                          < sSup (leftQuantile G '' Set.Ioo (0:ℝ) 1) by linarith)
                    rcases le_total v1 v2 with h12 | h12
                    · have := le_csSup hbS ⟨v2, hv2, rfl⟩
                      rw [hspec F G v2 hv2] at this
                      have := hmq F v1 hv1 v2 hv2 h12
                      linarith
                    · have := le_csSup hbS ⟨v1, hv1, rfl⟩
                      rw [hspec F G v1 hv1] at this
                      have := hmq G v2 hv2 v1 hv1 h12
                      linarith
              obtain ⟨eS, -⟩ := hrep _ hSM
              obtain ⟨eF, iF⟩ := hrep F hF
              obtain ⟨eG, iG⟩ := hrep G hG
              rw [eS, eF, eG, ← integral_add iF iG]
              exact setIntegral_congr_fun measurableSet_Ioo hMadd
            constructor
            · rintro ⟨hmono, hconst, hadd⟩
              have hex : ∃ h : ℝ → ℝ → ℝ, IsOrderedFamily h ∧ ∀ F ∈ Minf, Represents h F (T F) := by
                -- laws with a prescribed left-continuous monotone quantile
                have hexq : ∀ f : ℝ → ℝ, MonotoneOn f (Set.Ioo 0 1) →
                    (∀ p ∈ Set.Ioo (0:ℝ) 1, ∀ d : ℝ, 0 < d → ∃ u, 0 < u ∧ u < p ∧ f p - d < f u) →
                    ∃ S : ProbabilityMeasure ℝ, ∀ p ∈ Set.Ioo (0:ℝ) 1, leftQuantile S p = f p := by
                  intro f hfm hlcf
                  have hae : AEMeasurable f (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
                    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hfm
                  have hprob : IsProbabilityMeasure ((volume.restrict (Set.Ioo (0:ℝ) 1)).map f) := by
                    constructor
                    rw [Measure.map_apply_of_aemeasurable hae MeasurableSet.univ, Set.preimage_univ,
                      Measure.restrict_apply_univ, Real.volume_Ioo]
                    simp
                  let S : ProbabilityMeasure ℝ := ⟨_, hprob⟩
                  refine ⟨S, ?_⟩
                  intro p hp
                  have hcdf : ∀ x, ProbabilityTheory.cdf (S : Measure ℝ) x
                      = (volume (f ⁻¹' Set.Iic x ∩ Set.Ioo 0 1)).toReal := by
                    intro x
                    rw [ProbabilityTheory.cdf_eq_real]
                    show (Measure.map f (volume.restrict (Set.Ioo (0:ℝ) 1))).real (Set.Iic x) = _
                    rw [measureReal_def,
                      Measure.map_apply_of_aemeasurable hae measurableSet_Iic,
                      Measure.restrict_apply' measurableSet_Ioo]
                  have hfin : ∀ x, volume (f ⁻¹' Set.Iic x ∩ Set.Ioo (0:ℝ) 1) ≠ ⊤ := by
                    intro x
                    refine ne_top_of_le_ne_top (b := volume (Set.Ioo (0:ℝ) 1)) ?_
                      (measure_mono Set.inter_subset_right)
                    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
                  have key : ∀ x, p ≤ ProbabilityTheory.cdf (S : Measure ℝ) x ↔ f p ≤ x := by
                    intro x
                    rw [hcdf]
                    constructor
                    · intro hle
                      by_contra hlt
                      push_neg at hlt
                      obtain ⟨u, hu0, hup, hu⟩ := hlcf p hp ((f p - x) / 2) (by linarith)
                      have hsub : f ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 ⊆ Set.Ioo 0 u := by
                        intro v hv
                        refine ⟨hv.2.1, ?_⟩
                        by_contra hvu
                        push_neg at hvu
                        have h1 := hfm ⟨hu0, by linarith [hp.2]⟩ hv.2 hvu
                        have h3 : f v ≤ x := hv.1
                        linarith
                      have := ENNReal.toReal_le_of_le_ofReal hu0.le
                        ((measure_mono hsub).trans (by rw [Real.volume_Ioo, sub_zero]))
                      linarith
                    · intro hle
                      have hsub : Set.Ioc 0 p ⊆ f ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 := by
                        intro v hv
                        have hv' : v ∈ Set.Ioo (0:ℝ) 1 := ⟨hv.1, lt_of_le_of_lt hv.2 hp.2⟩
                        exact ⟨le_trans (hfm hv' hp hv.2) hle, hv'⟩
                      rw [← ENNReal.ofReal_le_iff_le_toReal (hfin x)]
                      have := measure_mono (μ := volume) hsub
                      rwa [Real.volume_Ioc, sub_zero] at this
                  show sInf {x | p ≤ ProbabilityTheory.cdf (S : Measure ℝ) x} = f p
                  have : {x | p ≤ ProbabilityTheory.cdf (S : Measure ℝ) x} = Set.Ici (f p) := by
                    ext x; exact key x
                  rw [this, csInf_Ici]
                have hQ : ∀ A B : ProbabilityMeasure ℝ,
                    (∀ p ∈ Set.Ioo (0:ℝ) 1, leftQuantile A p = leftQuantile B p) → A = B := by
                  intro A B hAB
                  apply ProbabilityMeasure.toMeasure_injective
                  apply Measure.eq_of_cdf
                  ext x
                  exact le_antisymm
                    (hq_cdf _ _ (ae_restrict_of_forall_mem measurableSet_Ioo (fun p hp => (hAB p hp).ge)) x)
                    (hq_cdf _ _ (ae_restrict_of_forall_mem measurableSet_Ioo (fun p hp => (hAB p hp).le)) x)
                have hqmono : ∀ A B : ProbabilityMeasure ℝ,
                    (∀ p ∈ Set.Ioo (0:ℝ) 1, leftQuantile A p ≤ leftQuantile B p) →
                    ∀ x, ProbabilityTheory.cdf (B : Measure ℝ) x ≤ ProbabilityTheory.cdf (A : Measure ℝ) x :=
                  fun A B h => hq_cdf A B (ae_restrict_of_forall_mem measurableSet_Ioo h)
                -- scaled Bernoulli laws
                have hB : ∀ c t : ℝ, ∃ S : ProbabilityMeasure ℝ, ∀ p ∈ Set.Ioo (0:ℝ) 1,
                    leftQuantile S p = if 1 - t < p then max c 0 else 0 := by
                  intro c t
                  apply hexq
                  · intro u hu v hv huv
                    simp only
                    split_ifs with h1 h2 h2
                    · exact le_rfl
                    · exact absurd (lt_of_lt_of_le h1 huv) h2
                    · exact le_max_right _ _
                    · exact le_rfl
                  · intro p hp d hd
                    by_cases h1 : 1 - t < p
                    · refine ⟨(max (1 - t) 0 + p) / 2, ?_, ?_, ?_⟩
                      · have := le_max_right (1 - t) 0; linarith [hp.1]
                      · have := max_lt h1 hp.1; linarith
                      · have hlt : 1 - t < (max (1 - t) 0 + p) / 2 := by
                          have := le_max_left (1 - t) 0; linarith
                        simp only [if_pos h1, if_pos hlt]; linarith
                    · refine ⟨p / 2, by linarith [hp.1], by linarith [hp.1], ?_⟩
                      have h2 : ¬ 1 - t < p / 2 := fun h => h1 (by linarith [hp.1])
                      simp only [if_neg h1, if_neg h2]; linarith
                choose B hBq using hB
                have hBM : ∀ c t, B c t ∈ Minf := by
                  intro c t
                  refine hMq _ 0 (max c 0) (fun p hp => ?_)
                  rw [hBq c t p hp]
                  split_ifs
                  · exact ⟨le_max_right _ _, le_rfl⟩
                  · exact ⟨le_rfl, le_max_right _ _⟩
                -- the uniqueness lemma
                have huniq : ∀ φ ψ : ProbabilityMeasure ℝ → ℝ,
                    (∀ A ∈ Minf, ∀ A' ∈ Minf,
                      (∀ p ∈ Set.Ioo (0:ℝ) 1, leftQuantile A p ≤ leftQuantile A' p) → φ A ≤ φ A') →
                    (∀ A ∈ Minf, ∀ A' ∈ Minf,
                      (∀ p ∈ Set.Ioo (0:ℝ) 1, leftQuantile A p ≤ leftQuantile A' p) → ψ A ≤ ψ A') →
                    (∀ A ∈ Minf, ∀ A' ∈ Minf, φ (comonoSum A A') = φ A + φ A') →
                    (∀ A ∈ Minf, ∀ A' ∈ Minf, ψ (comonoSum A A') = ψ A + ψ A') →
                    (∀ x, φ (constantLaw x) = x) → (∀ x, ψ (constantLaw x) = x) →
                    (∀ t ∈ Set.Icc (0:ℝ) 1, φ (B 1 t) = ψ (B 1 t)) → ∀ F ∈ Minf, φ F = ψ F := by
                  intro φ ψ hφm hψm hφa hψa hφc hψc hagree F hF
                  obtain ⟨a, b, hab⟩ := id hF
                  have hqb := hqbd F a b hab
                  have hhom : ∀ χ : ProbabilityMeasure ℝ → ℝ,
                      (∀ A ∈ Minf, ∀ A' ∈ Minf, χ (comonoSum A A') = χ A + χ A') →
                      (∀ x, χ (constantLaw x) = x) → ∀ δ : ℝ, 0 ≤ δ → ∀ s : ℝ, ∀ k : ℕ,
                      χ (B ((k : ℝ) * δ) s) = (k : ℝ) * χ (B δ s) := by
                    intro χ hχa hχc δ hδ s k
                    induction k with
                    | zero =>
                      simp only [Nat.cast_zero, zero_mul]
                      have hB00 : B 0 s = constantLaw 0 := hQ _ _ (fun p hp => by
                        rw [hBq 0 s p hp, hqc 0 p hp, max_self]; split_ifs <;> rfl)
                      rw [hB00, hχc]
                    | succ k ih =>
                      have hk : (0:ℝ) ≤ (k:ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
                      have hk1 : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
                      have e : B (((k + 1 : ℕ) : ℝ) * δ) s = comonoSum (B ((k:ℝ) * δ) s) (B δ s) := by
                        apply hQ
                        intro p hp
                        rw [hspec _ _ p hp, hBq _ _ p hp, hBq _ _ p hp, hBq _ _ p hp,
                          max_eq_left hk1, max_eq_left hk, max_eq_left hδ]
                        push_cast
                        split_ifs <;> ring
                      rw [e, hχa _ (hBM _ _) _ (hBM _ _), ih]
                      push_cast
                      ring
                  have hagreeδ : ∀ n : ℕ, ∀ s ∈ Set.Icc (0:ℝ) 1,
                      φ (B (1 / ((n:ℝ) + 1)) s) = ψ (B (1 / ((n:ℝ) + 1)) s) := by
                    intro n s hs
                    have hδ : (0:ℝ) ≤ 1 / ((n:ℝ) + 1) := by positivity
                    have h1 := hhom φ hφa hφc _ hδ s (n + 1)
                    have h2 := hhom ψ hψa hψc _ hδ s (n + 1)
                    have e : ((n + 1 : ℕ) : ℝ) * (1 / ((n:ℝ) + 1)) = 1 := by
                      push_cast
                      field_simp
                    rw [e, hagree s hs] at h1
                    rw [e] at h2
                    have hn : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
                    exact mul_left_cancel₀ hn.ne' (h1.symm.trans h2)
                  have hbound : ∀ n : ℕ, |φ F - ψ F| ≤ 1 / ((n:ℝ) + 1) := by
                    intro n
                    have hagδ := hagreeδ n
                    set δ : ℝ := 1 / ((n:ℝ) + 1) with hδdef
                    have hδ : 0 < δ := by positivity
                    let P : ℕ → ProbabilityMeasure ℝ := fun N =>
                      Nat.rec (motive := fun _ => ProbabilityMeasure ℝ) (constantLaw a)
                        (fun k Pk => comonoSum Pk
                          (B δ (1 - ProbabilityTheory.cdf (F : Measure ℝ) (a + ((k:ℝ) + 1) * δ)))) N
                    have hPs : ∀ N : ℕ, P (N + 1) = comonoSum (P N)
                        (B δ (1 - ProbabilityTheory.cdf (F : Measure ℝ) (a + ((N:ℝ) + 1) * δ))) :=
                      fun N => rfl
                    have hP0 : P 0 = constantLaw a := rfl
                    have hPM : ∀ N, P N ∈ Minf := by
                      intro N
                      induction N with
                      | zero => rw [hP0]; exact hcM a
                      | succ N ih => rw [hPs]; exact hSMg _ ih _ (hBM _ _)
                    have hPeq : ∀ N, φ (P N) = ψ (P N) := by
                      intro N
                      induction N with
                      | zero => rw [hP0, hφc, hψc]
                      | succ N ih =>
                        rw [hPs, hφa _ (hPM N) _ (hBM _ _), hψa _ (hPM N) _ (hBM _ _), ih,
                          hagδ _ (hcdf01 F _)]
                    have hPq : ∀ N : ℕ, ∀ u ∈ Set.Ioo (0:ℝ) 1,
                        leftQuantile (P N) u ≤ leftQuantile F u ∧ leftQuantile (P N) u ≤ a + N * δ ∧
                        (leftQuantile F u ≤ leftQuantile (P N) u + δ ∨ leftQuantile (P N) u = a + N * δ) := by
                      intro N u hu
                      induction N with
                      | zero =>
                        rw [hP0, hqc a u hu]
                        exact ⟨(hqb u hu).1, by simp, Or.inr (by simp)⟩
                      | succ N ih =>
                        obtain ⟨i1, i2, i3⟩ := ih
                        have hstep : leftQuantile (P (N + 1)) u = leftQuantile (P N) u +
                            (if a + ((N:ℝ) + 1) * δ < leftQuantile F u then δ else 0) := by
                          rw [hPs, hspec _ _ u hu, hBq _ _ u hu, max_eq_left hδ.le, sub_sub_cancel]
                          congr 1
                          have hiff : (ProbabilityTheory.cdf (F : Measure ℝ) (a + ((N:ℝ) + 1) * δ) < u) ↔
                              (a + ((N:ℝ) + 1) * δ < leftQuantile F u) := by
                            rw [← not_le, ← not_le, hgal F u hu]
                          by_cases hc : a + ((N:ℝ) + 1) * δ < leftQuantile F u
                          · rw [if_pos hc, if_pos (hiff.2 hc)]
                          · rw [if_neg hc, if_neg (fun h => hc (hiff.1 h))]
                        rw [hstep]
                        push_cast
                        have hr : ((N:ℝ) + 1) * δ = N * δ + δ := by ring
                        by_cases hc : a + ((N:ℝ) + 1) * δ < leftQuantile F u
                        · rw [if_pos hc]
                          have hqN : leftQuantile (P N) u = a + N * δ := by
                            rcases i3 with h | h
                            · exfalso; linarith
                            · exact h
                          refine ⟨by linarith, by linarith, Or.inr (by linarith)⟩
                        · rw [if_neg hc]
                          refine ⟨by linarith, by linarith, ?_⟩
                          rcases i3 with h | h
                          · left; linarith
                          · left; push_neg at hc; linarith
                    have hN := Nat.le_ceil ((b - a) / δ)
                    set N := ⌈(b - a) / δ⌉₊
                    have hN' : b - a ≤ N * δ := (div_le_iff₀ hδ).1 hN
                    have hsand : ∀ u ∈ Set.Ioo (0:ℝ) 1, leftQuantile (P N) u ≤ leftQuantile F u ∧
                        leftQuantile F u ≤ leftQuantile (P N) u + δ := by
                      intro u hu
                      obtain ⟨i1, i2, i3⟩ := hPq N u hu
                      refine ⟨i1, ?_⟩
                      rcases i3 with h | h
                      · exact h
                      · have := (hqb u hu).2; linarith
                    have hUM : comonoSum (P N) (constantLaw δ) ∈ Minf := hSMg _ (hPM N) _ (hcM δ)
                    have hUq : ∀ u ∈ Set.Ioo (0:ℝ) 1,
                        leftQuantile F u ≤ leftQuantile (comonoSum (P N) (constantLaw δ)) u := by
                      intro u hu
                      rw [hspec _ _ u hu, hqc δ u hu]
                      exact (hsand u hu).2
                    have hφ1 := hφm _ (hPM N) _ hF (fun u hu => (hsand u hu).1)
                    have hφ2 := hφm _ hF _ hUM hUq
                    have hψ1 := hψm _ (hPM N) _ hF (fun u hu => (hsand u hu).1)
                    have hψ2 := hψm _ hF _ hUM hUq
                    rw [hφa _ (hPM N) _ (hcM δ), hφc] at hφ2
                    rw [hψa _ (hPM N) _ (hcM δ), hψc] at hψ2
                    have := hPeq N
                    rw [abs_le]
                    constructor <;> linarith
                  by_contra hne
                  have hpos : 0 < |φ F - ψ F| := abs_pos.2 (sub_ne_zero.2 hne)
                  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
                  linarith [hbound n]
                have hρmono : ∀ p ∈ Set.Ioo (0:ℝ) 1, ∀ A ∈ Minf, ∀ A' ∈ Minf,
                    (∀ u ∈ Set.Ioo (0:ℝ) 1, leftQuantile A u ≤ leftQuantile A' u) →
                    leftQuantile (T A) p ≤ leftQuantile (T A') p := by
                  intro p hp A hA A' hA' hle
                  have h1 := hmono A hA A' hA' ((hst_cdf A A').2 (hqmono A A' hle))
                  rw [hst_cdf] at h1
                  exact (hgal (T A) p hp _).2 (le_trans ((hgal (T A') p hp _).1 le_rfl) (h1 _))
                have hB0 : ∀ c, c ≤ 0 → ∀ t, B c t = constantLaw 0 := by
                  intro c hc t
                  apply hQ
                  intro p hp
                  rw [hBq c t p hp, hqc 0 p hp, max_eq_right hc]
                  split_ifs <;> rfl
                have hBt0 : B 1 0 = constantLaw 0 := by
                  apply hQ
                  intro p hp
                  rw [hBq 1 0 p hp, hqc 0 p hp, if_neg (by linarith [hp.2])]
                have hBt1 : B 1 1 = constantLaw 1 := by
                  apply hQ
                  intro p hp
                  rw [hBq 1 1 p hp, hqc 1 p hp, if_pos (by linarith [hp.1])]
                  norm_num
                have hBmono : ∀ s t : ℝ, s ≤ t → ∀ u ∈ Set.Ioo (0:ℝ) 1,
                    leftQuantile (B 1 s) u ≤ leftQuantile (B 1 t) u := by
                  intro s t hst u hu
                  rw [hBq 1 s u hu, hBq 1 t u hu]
                  split_ifs with h1 h2 h2
                  · exact le_rfl
                  · exact absurd (by linarith) h2
                  · exact le_max_right _ _
                  · exact le_rfl
                have hhH : ∀ p ∈ Set.Ioo (0:ℝ) 1, IsH (fun t => leftQuantile (T (B 1 t)) p) := by
                  intro p hp
                  refine ⟨fun s _ t _ hst => hρmono p hp _ (hBM 1 s) _ (hBM 1 t) (hBmono s t hst), ?_, ?_⟩
                  · show leftQuantile (T (B 1 0)) p = 0
                    rw [hBt0, hconst 0, hqc 0 p hp]
                  · show leftQuantile (T (B 1 1)) p = 1
                    rw [hBt1, hconst 1, hqc 1 p hp]
                -- the Choquet integral of a Bernoulli law
                have hCB : ∀ g : ℝ → ℝ, IsH g → ∀ t ∈ Set.Icc (0:ℝ) 1, choquet g (B 1 t) = g t := by
                  intro g hg t ht
                  have hlev : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
                      (∀ p ∈ Set.Ioo (0:ℝ) 1, p ≤ a ↔ p ≤ b) → a = b := by
                    intro a b ha0 ha1 hb0 hb1 h
                    by_contra hne
                    rcases lt_or_gt_of_ne hne with hab | hab
                    · have := (h ((a + b) / 2) ⟨by linarith, by linarith⟩).2 (by linarith)
                      linarith
                    · have := (h ((a + b) / 2) ⟨by linarith, by linarith⟩).1 (by linarith)
                      linarith
                  have hcdfB : ∀ x, ProbabilityTheory.cdf ((B 1 t : ProbabilityMeasure ℝ) : Measure ℝ) x =
                      if x < 0 then 0 else if x < 1 then 1 - t else 1 := by
                    intro x
                    apply hlev _ _ (ProbabilityTheory.cdf_nonneg _ _) (ProbabilityTheory.cdf_le_one _ _)
                      (by split_ifs <;> linarith [ht.1, ht.2]) (by split_ifs <;> linarith [ht.1, ht.2])
                    intro p hp
                    rw [← hgal (B 1 t) p hp x, hBq 1 t p hp, max_eq_left zero_le_one]
                    by_cases h1 : 1 - t < p <;> by_cases hx0 : x < 0 <;> by_cases hx1 : x < 1 <;>
                      simp only [h1, hx0, hx1, if_true, if_false] <;>
                      first
                      | (constructor <;> intro h <;> linarith [hp.1, hp.2])
                      | (simp only [true_iff, false_iff, not_le]; linarith [hp.1, hp.2])
                      | (simp; linarith [hp.1, hp.2])
                      | simp
                  unfold choquet
                  rw [integral_Iic_eq_integral_Iio]
                  have e1 : ∫ x in Set.Iio (0:ℝ), (g (1 - ProbabilityTheory.cdf
                      ((B 1 t : ProbabilityMeasure ℝ) : Measure ℝ) x) - 1) = 0 := by
                    rw [setIntegral_congr_fun measurableSet_Iio (g := fun _ => (0:ℝ)) (fun x hx => by
                      simp only
                      rw [hcdfB, if_pos (show x < 0 from hx), sub_zero, hg.2.2, sub_self])]
                    simp
                  have e2 : ∫ x in Set.Ioi (0:ℝ), g (1 - ProbabilityTheory.cdf
                      ((B 1 t : ProbabilityMeasure ℝ) : Measure ℝ) x) = ∫ x in Set.Ioo (0:ℝ) 1, g (1 -
                      ProbabilityTheory.cdf ((B 1 t : ProbabilityMeasure ℝ) : Measure ℝ) x) :=
                    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
                      Set.Ioo_subset_Ioi_self (fun x hx => by
                        have h1 : 1 ≤ x := by
                          by_contra h; push_neg at h; exact hx.2 ⟨hx.1, h⟩
                        have h0 : (0:ℝ) < x := hx.1
                        rw [hcdfB, if_neg (by linarith), if_neg (by linarith), sub_self, hg.2.1])
                  have e3 : ∫ x in Set.Ioo (0:ℝ) 1, g (1 - ProbabilityTheory.cdf
                      ((B 1 t : ProbabilityMeasure ℝ) : Measure ℝ) x) = ∫ x in Set.Ioo (0:ℝ) 1, g t :=
                    setIntegral_congr_fun measurableSet_Ioo (fun x hx => by
                      rw [hcdfB, if_neg (not_lt.2 hx.1.le), if_pos hx.2, sub_sub_cancel])
                  rw [e1, e2, e3, setIntegral_const, Real.volume_real_Ioo]
                  simp
                refine ⟨fun p t => leftQuantile (T (B 1 t)) p, ⟨hhH, ?_⟩, ?_⟩
                · intro p₁ hp₁ p₂ hp₂ hle t ht
                  exact hmq _ p₁ hp₁ p₂ hp₂ hle
                · intro F hF
                  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun p hp => ?_)
                  refine huniq (fun A => leftQuantile (T A) p) (choquet (fun t => leftQuantile (T (B 1 t)) p))
                    (fun A hA A' hA' hle => hρmono p hp A hA A' hA' hle)
                    (fun A hA A' hA' hle => hchmono _ (hhH p hp) A hA A' hA' (hqmono A A' hle))
                    (fun A hA A' hA' => ?_) (fun A hA A' hA' => hadd_chg A hA A' hA' _ (hhH p hp))
                    (fun x => by show leftQuantile (T (constantLaw x)) p = x; rw [hconst x, hqc x p hp])
                    (fun x => hchc _ (hhH p hp) x)
                    (fun t ht => (hCB _ (hhH p hp) t ht).symm) F hF
                  show leftQuantile (T (comonoSum A A')) p = leftQuantile (T A) p + leftQuantile (T A') p
                  rw [hadd A hA A' hA', hspec _ _ p hp]
              obtain ⟨h, hfam, hrep⟩ := hex
              refine ⟨h, hfam, fun F hF => ⟨hrep F hF, fun G hG => ?_⟩⟩
              have e1 : ∀ᵐ p ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
                  leftQuantile G p ≤ leftQuantile (T F) p := by
                filter_upwards [hG, hrep F hF] with p h1 h2
                rw [h1, h2]
              have e2 : ∀ᵐ p ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
                  leftQuantile (T F) p ≤ leftQuantile G p := by
                filter_upwards [hG, hrep F hF] with p h1 h2
                rw [h1, h2]
              apply ProbabilityMeasure.toMeasure_injective
              apply Measure.eq_of_cdf
              ext x
              exact le_antisymm (hq_cdf _ _ e2 x) (hq_cdf _ _ e1 x)
            · rintro ⟨h, hfam, hrep⟩
              refine ⟨?_, ?_, ?_⟩
              · intro F hF G hG hFG
                rw [hst_cdf] at hFG ⊢
                apply hq_cdf
                filter_upwards [(hrep F hF).1, (hrep G hG).1, ae_restrict_mem measurableSet_Ioo]
                  with p h1 h2 hp
                rw [h1, h2]
                exact hchmono _ (hfam.1 p hp) F hF G hG hFG
              · intro x
                have hR : Represents h (constantLaw x) (constantLaw x) := by
                  unfold Represents
                  refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
                  intro p hp
                  rw [hqc x p hp, hchc _ (hfam.1 p hp)]
                have := (hrep _ (hcM x)).2 _ hR
                exact this.symm
              · intro F hF G hG
                -- existence of the comonotonic sum (a law with the summed quantile function)
                -- the comonotonic sum of bounded laws is bounded
                have hSM := hSMg F hF G hG
                have hadd_ch := hadd_chg F hF G hG
                have hR : Represents h (comonoSum F G) (comonoSum (T F) (T G)) := by
                  unfold Represents
                  filter_upwards [(hrep F hF).1, (hrep G hG).1, ae_restrict_mem measurableSet_Ioo]
                    with p h1 h2 hp
                  rw [hspec _ _ p hp, h1, h2, hadd_ch _ (hfam.1 p hp)]
                exact ((hrep _ hSM).2 _ hR).symm
