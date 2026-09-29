-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_pull_count_bound_exact_ranks
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T22:41:46.864942+00:00
-- url     : https://prove2.me/submissions/240d90eb-f5c4-49f9-947f-26422534c375

import Definitions.Def_ThompsonSampling
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem gaussianReal_real_Ioi_pos
    (m : ℝ) (v : NNReal) (hv : v ≠ 0) (c : ℝ) :
    0 < (gaussianReal m v).real (Set.Ioi c) := by
  apply ENNReal.toReal_pos
  · intro hzero
    have hac : (volume : Measure ℝ) ≪ gaussianReal m v :=
      gaussianReal_absolutelyContinuous' m hv
    have := hac hzero
    rw [Real.volume_Ioi] at this
    exact ENNReal.top_ne_zero this
  · exact measure_ne_top _ _

private theorem measurable_gaussianReal_real_Ioi (c : ℝ) :
    Measurable (fun p : ℝ × NNReal ↦ (gaussianReal p.1 p.2).real (Set.Ioi c)) := by
  have hpdf :
      Measurable
        (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) := by
    rw [show
      (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) =
        fun p ↦ ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi * (p.1.2 : ℝ)))⁻¹ *
            Real.exp (-((p.2 - p.1.1) ^ 2) / (2 * (p.1.2 : ℝ)))) by
      funext p
      rfl]
    fun_prop
  have hint :
      Measurable
        (fun p : ℝ × NNReal ↦
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal) := by
    apply Measurable.ennreal_toReal
    have hrestricted :
        Measurable
          (fun z : (ℝ × NNReal) × ℝ ↦
            (Set.Ioi c).indicator
              (fun x ↦ gaussianPDF z.1.1 z.1.2 x) z.2) :=
      hpdf.indicator
        (measurableSet_Ioi.preimage measurable_snd)
    simpa only [lintegral_indicator measurableSet_Ioi] using
        (hrestricted.lintegral_prod_right' (ν := (volume : Measure ℝ)))
  have hzero :
      Measurable
        (fun p : ℝ × NNReal ↦
          if c < p.1 then (1 : ℝ) else 0) := by
    exact Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      measurable_const measurable_const
  have heq :
      (fun p : ℝ × NNReal ↦ (gaussianReal p.1 p.2).real (Set.Ioi c)) =
        fun p ↦ if p.2 = 0 then
          (if c < p.1 then 1 else 0)
        else
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal := by
    funext p
    by_cases hp : p.2 = 0
    · rw [if_pos hp, hp, gaussianReal_zero_var]
      by_cases hc : c < p.1 <;> simp [Measure.real, Set.indicator, hc]
    · rw [if_neg hp, Measure.real, gaussianReal_apply p.1 hp]
  rw [heq]
  apply Measurable.ite
  · exact (measurableSet_singleton (0 : NNReal)).preimage measurable_snd
  · exact hzero
  · exact hint

private theorem product_minArgmax_low_le
    {k : ℕ} [NeZero k] (μ : Fin k → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)]
    (i₀ i : Fin k) (hi : i ≠ i₀) (c : ℝ)
    (hq : 0 < (μ i₀).real (Set.Ioi c)) :
    (Measure.pi μ).real
        {θ | minArgmax θ = i ∧ θ i ≤ c} ≤
      (1 / (μ i₀).real (Set.Ioi c) - 1) *
        (Measure.pi μ).real {θ | minArgmax θ = i₀} := by
  classical
  let ρ : Measure (Fin k → ℝ) := Measure.pi μ
  let S : Finset (Fin k) := {i₀}
  let T : Finset (Fin k) := Finset.univ.erase i₀
  have hiT : i ∈ T := by simp [T, hi]
  let iT : T := ⟨i, hiT⟩
  let iS : S := ⟨i₀, Finset.mem_singleton_self i₀⟩
  let coord : (Fin k → ℝ) → ℝ := fun θ ↦ θ i₀
  let rest : (Fin k → ℝ) → (T → ℝ) := fun θ j ↦ θ j
  let B : Set (T → ℝ) :=
    {z | (∀ j, z j ≤ z iT) ∧ z iT ≤ c}
  have hB : MeasurableSet B := by
    change MeasurableSet ({z : T → ℝ | ∀ j, z j ≤ z iT} ∩ {z | z iT ≤ c})
    apply MeasurableSet.inter
    · have heq :
          {z : T → ℝ | ∀ j, z j ≤ z iT} =
            ⋂ j : T, {z | z j ≤ z iT} := by
          ext z
          simp
      rw [heq]
      exact MeasurableSet.iInter fun j ↦
        measurableSet_le (measurable_pi_apply j) (measurable_pi_apply iT)
    · exact measurableSet_le (measurable_pi_apply iT) measurable_const
  have hind_all :
      iIndepFun (fun j (θ : Fin k → ℝ) ↦ θ j) ρ := by
    dsimp [ρ]
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hST : Disjoint S T := by
    simp [S, T]
  have hind_vec :
      IndepFun
        (fun θ (j : S) ↦ θ j)
        (fun θ (j : T) ↦ θ j) ρ :=
    iIndepFun.indepFun_finset S T hST hind_all
      (fun j ↦ measurable_pi_apply j)
  have hcoord_meas : Measurable (fun z : S → ℝ ↦ z iS) :=
    measurable_pi_apply iS
  have hrest_meas : Measurable (id : (T → ℝ) → (T → ℝ)) :=
    measurable_id
  have hind : IndepFun coord rest ρ := by
    have hc := hind_vec.comp hcoord_meas hrest_meas
    simpa [coord, rest, Function.comp_def, iS, S, T] using hc
  let Ehi : Set (Fin k → ℝ) := coord ⁻¹' Set.Ioi c ∩ rest ⁻¹' B
  let Elo : Set (Fin k → ℝ) := coord ⁻¹' Set.Iic c ∩ rest ⁻¹' B
  have hEhi :
      ρ.real Ehi =
        ρ.real (coord ⁻¹' Set.Ioi c) * ρ.real (rest ⁻¹' B) := by
    have he := hind.measure_inter_preimage_eq_mul
      (Set.Ioi c) B measurableSet_Ioi hB
    change (ρ Ehi).toReal =
      (ρ (coord ⁻¹' Set.Ioi c)).toReal *
        (ρ (rest ⁻¹' B)).toReal
    rw [show Ehi = coord ⁻¹' Set.Ioi c ∩ rest ⁻¹' B by rfl, he]
    exact ENNReal.toReal_mul
  have hElo :
      ρ.real Elo =
        ρ.real (coord ⁻¹' Set.Iic c) * ρ.real (rest ⁻¹' B) := by
    have he := hind.measure_inter_preimage_eq_mul
      (Set.Iic c) B measurableSet_Iic hB
    change (ρ Elo).toReal =
      (ρ (coord ⁻¹' Set.Iic c)).toReal *
        (ρ (rest ⁻¹' B)).toReal
    rw [show Elo = coord ⁻¹' Set.Iic c ∩ rest ⁻¹' B by rfl, he]
    exact ENNReal.toReal_mul
  have hcoord_map : Measure.map coord ρ = μ i₀ := by
    dsimp [coord, ρ]
    simpa using (MeasureTheory.measurePreserving_eval μ i₀).map_eq
  have hcoord_hi :
      ρ.real (coord ⁻¹' Set.Ioi c) = (μ i₀).real (Set.Ioi c) := by
    change (ρ (coord ⁻¹' Set.Ioi c)).toReal = _
    rw [← Measure.map_apply (by fun_prop : Measurable coord) measurableSet_Ioi,
      hcoord_map]
    rfl
  have hcoord_lo :
      ρ.real (coord ⁻¹' Set.Iic c) =
        1 - (μ i₀).real (Set.Ioi c) := by
    have hcompl : Set.Iic c = (Set.Ioi c)ᶜ := by ext x; simp
    change (ρ (coord ⁻¹' Set.Iic c)).toReal = _
    rw [← Measure.map_apply (by fun_prop : Measurable coord) measurableSet_Iic,
      hcoord_map, hcompl]
    change (μ i₀).real (Set.Ioi c)ᶜ =
      1 - (μ i₀).real (Set.Ioi c)
    rw [measureReal_compl measurableSet_Ioi]
    simp
  have hbad_subset :
      {θ : Fin k → ℝ | minArgmax θ = i ∧ θ i ≤ c} ⊆ Elo := by
    intro θ hθ
    have hmax := (minArgmax_eq_iff.mp hθ.1).1
    constructor
    · exact le_trans (hmax i₀) hθ.2
    · constructor
      · intro j
        exact hmax j
      · exact hθ.2
  have hgood_subset :
      Ehi ⊆ {θ : Fin k → ℝ | minArgmax θ = i₀} := by
    intro θ hθ
    have hstrict : ∀ j, j ≠ i₀ → θ j < θ i₀ := by
      intro j hj
      have hjT : j ∈ T := by simp [T, hj]
      have hle : θ j ≤ θ i := hθ.2.1 ⟨j, hjT⟩
      exact lt_of_le_of_lt (le_trans hle hθ.2.2) hθ.1
    apply (minArgmax_eq_iff).2
    constructor
    · intro j
      by_cases hj : j = i₀
      · simp [hj]
      · exact (hstrict j hj).le
    · intro j hjmax
      have hji : j = i₀ := by
        by_contra hne
        exact (not_lt_of_ge (hjmax i₀)) (hstrict j hne)
      simp [hji]
  have hbad_le : ρ.real {θ | minArgmax θ = i ∧ θ i ≤ c} ≤ ρ.real Elo :=
    measureReal_mono hbad_subset
  have hgood_le : ρ.real Ehi ≤ ρ.real {θ | minArgmax θ = i₀} :=
    measureReal_mono hgood_subset
  rw [hElo, hcoord_lo] at hbad_le
  rw [hEhi, hcoord_hi] at hgood_le
  let q := (μ i₀).real (Set.Ioi c)
  let b := ρ.real (rest ⁻¹' B)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    calc
      (μ i₀).real (Set.Ioi c) ≤ (μ i₀).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have halg : (1 - q) * b = (1 / q - 1) * (q * b) := by
    have hq0 : q ≠ 0 := ne_of_gt hq
    field_simp [hq0]
  calc
    ρ.real {θ | minArgmax θ = i ∧ θ i ≤ c} ≤ (1 - q) * b := hbad_le
    _ = (1 / q - 1) * (q * b) := halg
    _ ≤ (1 / q - 1) * ρ.real {θ | minArgmax θ = i₀} := by
      apply mul_le_mul_of_nonneg_left hgood_le
      exact sub_nonneg.mpr (by
        simpa [one_div, q] using (one_le_inv₀ hq).2 hq1)

private noncomputable def currentGaussianTSTail {k m : ℕ}
    (j : Fin k) (c : ℝ) (h : BanditHistory k m) : ℝ :=
  if armPullCount j h = 0 then 1
  else
    (gaussianReal (armEmpiricalMean j h)
      ((armPullCount j h : NNReal))⁻¹).real (Set.Ioi c)

private theorem armPullCount_eq_sum_indicator {k m : ℕ}
    (j : Fin k) (h : BanditHistory k m) :
    armPullCount j h =
      ∑ t : Fin m, if (h t).1 = j then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset :
      {t | (h t).1 = j}.toFinset =
        Finset.univ.filter fun t ↦ (h t).1 = j := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℕ) (fun t : Fin m ↦ (h t).1 = j)
      Finset.univ).symm

private theorem measurable_armPullCount {k m : ℕ} (j : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ armPullCount j h) := by
  simp_rw [armPullCount_eq_sum_indicator]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite
    ((measurableSet_singleton j).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem armEmpiricalMean_eq_sum_indicator {k m : ℕ}
    (j : Fin k) (h : BanditHistory k m) :
    armEmpiricalMean j h =
      (∑ t : Fin m, if (h t).1 = j then (h t).2 else 0) /
        armPullCount j h := by
  classical
  rw [armEmpiricalMean]
  have hset :
      {t | (h t).1 = j}.toFinset =
        Finset.univ.filter fun t ↦ (h t).1 = j := by
    ext t
    simp
  rw [hset, Finset.sum_filter]

private theorem measurable_armEmpiricalMean {k m : ℕ} (j : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ armEmpiricalMean j h) := by
  simp_rw [armEmpiricalMean_eq_sum_indicator]
  apply Measurable.div
  · apply Finset.measurable_sum
    intro t ht
    exact Measurable.ite
      ((measurableSet_singleton j).preimage
        (measurable_fst.comp (measurable_pi_apply t)))
      (measurable_snd.comp (measurable_pi_apply t))
      measurable_const
  · exact ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_armPullCount j) : Measurable
      (fun h : BanditHistory k m ↦ (armPullCount j h : ℝ)))

private theorem measurable_currentGaussianTSTail {k m : ℕ}
    (j : Fin k) (c : ℝ) :
    Measurable (fun h : BanditHistory k m ↦ currentGaussianTSTail j c h) := by
  rw [show
    (fun h : BanditHistory k m ↦ currentGaussianTSTail j c h) =
      fun h ↦ if armPullCount j h = 0 then 1
      else
        (gaussianReal (armEmpiricalMean j h)
          ((armPullCount j h : NNReal))⁻¹).real (Set.Ioi c) by
    funext h
    rfl]
  apply Measurable.ite
  · exact (measurableSet_singleton 0).preimage (measurable_armPullCount j)
  · exact measurable_const
  · have hp : Measurable
        (fun h : BanditHistory k m ↦
          (armEmpiricalMean j h,
            ((armPullCount j h : NNReal))⁻¹)) := by
      apply Measurable.prodMk (measurable_armEmpiricalMean j)
      exact Measurable.inv
        ((MeasurableEmbedding.natCast (α := NNReal)).measurable.comp
          (measurable_armPullCount j))
    exact (measurable_gaussianReal_real_Ioi c).comp hp

private theorem currentGaussianTSTail_pos {k m : ℕ}
    (j : Fin k) (c : ℝ) (h : BanditHistory k m) :
    0 < currentGaussianTSTail j c h := by
  rw [currentGaussianTSTail]
  split_ifs with hj
  · norm_num
  · apply gaussianReal_real_Ioi_pos
    exact inv_ne_zero (by
      exact_mod_cast hj)

private theorem currentGaussianTSTail_le_one {k m : ℕ}
    (j : Fin k) (c : ℝ) (h : BanditHistory k m) :
    currentGaussianTSTail j c h ≤ 1 := by
  rw [currentGaussianTSTail]
  split_ifs
  · norm_num
  · calc
      (gaussianReal (armEmpiricalMean j h)
          (↑(armPullCount j h) : NNReal)⁻¹).real (Set.Ioi c) ≤
          (gaussianReal (armEmpiricalMean j h)
            (↑(armPullCount j h) : NNReal)⁻¹).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp

private theorem gaussianTSDistribution_selection_bound
    {k m N : ℕ} [NeZero k] (hN : 0 < N)
    (h : BanditHistory k m) (i₀ i : Fin k) (hi : i ≠ i₀) (c : ℝ) :
    (gaussianTSDistribution h).real {i} ≤
      (1 / currentGaussianTSTail i₀ c h - 1) *
          (gaussianTSDistribution h).real {i₀} +
        if 1 / (N : ℝ) < currentGaussianTSTail i c h then
          (gaussianTSDistribution h).real {i}
        else 1 / (N : ℝ) := by
  classical
  by_cases hunplayed : ∃ j, armPullCount j h = 0
  · rw [gaussianTSDistribution, if_pos hunplayed]
    let jstar : Fin k :=
      minArgmax fun j ↦ if armPullCount j h = 0 then (1 : ℝ) else 0
    have hsel (j : Fin k) :
        (Measure.dirac jstar).real {j} = if jstar = j then 1 else 0 := by
      change ((Measure.dirac jstar) {j}).toReal =
        if jstar = j then 1 else 0
      rw [Measure.dirac_apply' jstar (measurableSet_singleton j)]
      by_cases hj : jstar = j <;> simp [hj]
    rw [hsel i, hsel i₀]
    have hcoef :
        0 ≤ 1 / currentGaussianTSTail i₀ c h - 1 := by
      exact sub_nonneg.mpr (by
        simpa [one_div] using
          (one_le_inv₀ (currentGaussianTSTail_pos i₀ c h)).2
            (currentGaussianTSTail_le_one i₀ c h))
    by_cases hji : jstar = i
    · have hcount : armPullCount i h = 0 := by
        obtain ⟨j, hj⟩ := hunplayed
        have hmax :=
          (minArgmax_eq_iff.mp (show
            minArgmax (fun j ↦ if armPullCount j h = 0 then (1 : ℝ) else 0) =
              jstar by rfl)).1 j
        rw [hji] at hmax
        by_contra hne
        simp [hj, hne] at hmax
        norm_num at hmax
      have hqi : currentGaussianTSTail i c h = 1 := by
        simp [currentGaussianTSTail, hcount]
      rw [if_pos hji]
      simp only [hqi]
      have hsec :
          1 ≤ if 1 / (N : ℝ) < 1 then 1 else 1 / (N : ℝ) := by
        by_cases hsmall : 1 / (N : ℝ) < 1
        · rw [if_pos hsmall]
        · rw [if_neg hsmall]
          exact le_of_not_gt hsmall
      exact hsec.trans (le_add_of_nonneg_left
        (mul_nonneg hcoef (by split <;> positivity)))
    · rw [if_neg hji]
      apply add_nonneg
      · apply mul_nonneg hcoef
        split <;> positivity
      · split <;> positivity
  · rw [gaussianTSDistribution, if_neg hunplayed]
    let μ : Fin k → Measure ℝ := fun j ↦
      gaussianReal (armEmpiricalMean j h) ((armPullCount j h : NNReal))⁻¹
    let ρ : Measure (Fin k → ℝ) := Measure.pi μ
    have hcount (j : Fin k) : armPullCount j h ≠ 0 := by
      intro hj
      exact hunplayed ⟨j, hj⟩
    have htail (j : Fin k) :
        currentGaussianTSTail j c h = (μ j).real (Set.Ioi c) := by
      simp [currentGaussianTSTail, μ, hcount j]
    have hmap (j : Fin k) :
        (Measure.map minArgmax ρ).real {j} =
          ρ.real {θ | minArgmax θ = j} := by
      rw [map_measureReal_apply measurable_minArgmax (measurableSet_singleton j)]
      rfl
    rw [htail i₀, htail i, hmap i, hmap i₀]
    by_cases hlarge : 1 / (N : ℝ) < (μ i).real (Set.Ioi c)
    · rw [if_pos hlarge]
      have hcoef :
          0 ≤ 1 / (μ i₀).real (Set.Ioi c) - 1 := by
        apply sub_nonneg.mpr
        rw [one_div]
        apply (one_le_inv₀ (by
          simpa [htail] using currentGaussianTSTail_pos i₀ c h)).2
        simpa [← htail] using currentGaussianTSTail_le_one i₀ c h
      exact le_add_of_nonneg_left (mul_nonneg hcoef measureReal_nonneg)
    · rw [if_neg hlarge]
      have hlow := product_minArgmax_low_le μ i₀ i hi c
        (by simpa [← htail] using currentGaussianTSTail_pos i₀ c h)
      have hsplit :
          ρ.real {θ | minArgmax θ = i} ≤
            ρ.real {θ | minArgmax θ = i ∧ θ i ≤ c} +
              ρ.real {θ | c < θ i} := by
        apply (measureReal_mono ?_).trans (measureReal_union_le _ _)
        intro θ hθ
        by_cases hc : θ i ≤ c
        · exact Set.mem_union_left _ ⟨hθ, hc⟩
        · exact Set.mem_union_right _ (lt_of_not_ge hc)
      have htail_event :
          ρ.real {θ | c < θ i} = (μ i).real (Set.Ioi c) := by
        change ρ.real ((fun θ : Fin k → ℝ ↦ θ i) ⁻¹' Set.Ioi c) = _
        rw [← map_measureReal_apply (measurable_pi_apply i) measurableSet_Ioi]
        change (Measure.map (Function.eval i) (Measure.pi μ)).real (Set.Ioi c) = _
        rw [(MeasureTheory.measurePreserving_eval μ i).map_eq]
      rw [htail_event] at hsplit
      calc
        ρ.real {θ | minArgmax θ = i} ≤
            ρ.real {θ | minArgmax θ = i ∧ θ i ≤ c} +
              (μ i).real (Set.Ioi c) := hsplit
        _ ≤
            (1 / (μ i₀).real (Set.Ioi c) - 1) *
                ρ.real {θ | minArgmax θ = i₀} +
              (μ i).real (Set.Ioi c) := by gcongr
        _ ≤
            (1 / (μ i₀).real (Set.Ioi c) - 1) *
                ρ.real {θ | minArgmax θ = i₀} +
              1 / (N : ℝ) := by
          gcongr
          exact le_of_not_gt hlarge

private def banditHistoryPrefixLen {k n : ℕ}
    (h : BanditHistory k n) (m : ℕ) (hm : m ≤ n) :
    BanditHistory k m :=
  fun t ↦ h (Fin.castLE hm t)

private theorem measurable_banditHistoryPrefixLen {k n m : ℕ}
    (hm : m ≤ n) :
    Measurable (fun h : BanditHistory k n ↦
      banditHistoryPrefixLen h m hm) :=
  measurable_pi_lambda _ fun t ↦ measurable_pi_apply (Fin.castLE hm t)

private theorem banditHistoryPrefixLen_self {k n : ℕ}
    (h : BanditHistory k n) :
    banditHistoryPrefixLen h n le_rfl = h := by
  funext t
  rfl

private theorem banditHistoryPrefixLen_snoc {k n m : ℕ}
    (hm : m ≤ n) (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixLen
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) m
        (hm.trans (Nat.le_succ n)) =
      banditHistoryPrefixLen h m hm := by
  funext t
  unfold banditHistoryPrefixLen
  have hlt :
      (Fin.castLE (hm.trans (Nat.le_succ n)) t).val < n :=
    lt_of_lt_of_le t.isLt hm
  rw [Fin.snoc, dif_pos hlt]
  congr 1

private theorem banditMeasure_map_init {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) :
    (banditMeasure ν π (n + 1)).map
        (fun h : BanditHistory k (n + 1) ↦ Fin.init h) =
      banditMeasure ν π n := by
  rw [banditMeasure]
  rw [Measure.map_map
    (by fun_prop :
      Measurable (fun h : BanditHistory k (n + 1) ↦ Fin.init h))
    measurable_banditHistorySnoc]
  have hfun :
      ((fun h : BanditHistory k (n + 1) ↦ Fin.init h) ∘
        (fun p : BanditHistory k n × (Fin k × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2)) =
        Prod.fst := by
    funext p
    simp
  rw [hfun]
  change Measure.fst
      ((banditMeasure ν π n).compProd (banditStepKernel ν π n)) =
    banditMeasure ν π n
  exact Measure.fst_compProd
    (banditMeasure ν π n) (banditStepKernel ν π n)

private theorem banditMeasure_map_prefixLen {k n m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (hm : m ≤ n) :
    (banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixLen h m hm) =
      banditMeasure ν π m := by
  induction n with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rw [banditMeasure]
      rw [Measure.map_dirac'
        (measurable_banditHistoryPrefixLen hm)]
      apply congrArg Measure.dirac
      funext t
      exact Fin.elim0 t
  | succ n ih =>
      by_cases hmn : m = n + 1
      · subst m
        simpa [banditHistoryPrefixLen_self] using
          (Measure.map_id (banditMeasure ν π (n + 1)))
      · have hmn' : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hm hmn)
        have hfun :
            (fun h : BanditHistory k (n + 1) ↦
              banditHistoryPrefixLen h m hm) =
              (fun h : BanditHistory k n ↦
                banditHistoryPrefixLen h m hmn') ∘
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h) := by
          funext h
          rw [← Fin.snoc_init_self h]
          simpa [Function.comp_apply] using
            banditHistoryPrefixLen_snoc hmn'
              (Fin.init h) (h (Fin.last n))
        rw [hfun, ← Measure.map_map
          (measurable_banditHistoryPrefixLen hmn')
          (by fun_prop :
            Measurable (fun h : BanditHistory k (n + 1) ↦ Fin.init h)),
          banditMeasure_map_init ν π, ih hmn']

private theorem armPullCountBefore_lt_of_selected {k n : ℕ}
    (j : Fin k) (t : Fin n) (h : BanditHistory k n)
    (ht : (h t).1 = j) :
    armPullCountBefore j t h < armPullCount j h := by
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter fun u ↦ u < t ∧ (h u).1 = j
  let B : Finset (Fin n) :=
    Finset.univ.filter fun u ↦ (h u).1 = j
  have hAB : A ⊂ B := by
    constructor
    · intro u hu
      exact Finset.mem_filter.2
        ⟨Finset.mem_univ _, (Finset.mem_filter.1 hu).2.2⟩
    · intro hBA
      have htA : t ∈ A := hBA (Finset.mem_filter.2
        ⟨Finset.mem_univ _, ht⟩)
      exact (lt_irrefl t) (Finset.mem_filter.1 htA).2.1
  have hset :
      {u | (h u).1 = j}.toFinset = B := by
    ext u
    simp [B]
  rw [armPullCountBefore, armPullCount, hset]
  exact Finset.card_lt_card hAB

private theorem armFirstRewardsMean_pullCount_eq_empiricalMean
    {k n : ℕ} (j : Fin k) (h : BanditHistory k n) :
    armFirstRewardsMean j (armPullCount j h) h =
      armEmpiricalMean j h := by
  classical
  unfold armFirstRewardsMean armEmpiricalMean
  congr 1
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · exact fun ht ↦ ht.1
    · intro ht
      exact ⟨ht, armPullCountBefore_lt_of_selected j t h ht⟩
  · intro t ht
    rfl

private theorem armPullCountBefore_castSucc_snoc {k n : ℕ}
    (j : Fin k) (t : Fin n) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armPullCountBefore j t.castSucc
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCountBefore j t h := by
  classical
  unfold armPullCountBefore
  refine Finset.card_bij
    (fun u hu ↦
      (⟨u.val, lt_trans
        (Finset.mem_filter.1 hu).2.1 t.isLt⟩ : Fin n)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hut := (Finset.mem_filter.1 hu).2.1
    have hun : u.val < n :=
      lt_trans hut t.isLt
    constructor
    · exact hut
    · have hsel := (Finset.mem_filter.1 hu).2.2
      simp [Fin.snoc, hun] at hsel
      exact hsel
  · intro u₁ hu₁ u₂ hu₂ heq
    apply Fin.ext
    change u₁.val = u₂.val
    exact congrArg (fun q : Fin n ↦ q.val) heq
  · intro v hv
    let u : Fin (n + 1) := v.castSucc
    have hu : u ∈ Finset.univ.filter
        (fun q : Fin (n + 1) ↦
          q < t.castSucc ∧
            ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) q).1 = j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simpa [u] using (Finset.mem_filter.1 hv).2.1
      · simpa [u] using (Finset.mem_filter.1 hv).2.2
    refine ⟨u, hu, ?_⟩
    rfl

private theorem armPullCountBefore_last_snoc {k n : ℕ}
    (j : Fin k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCountBefore j (Fin.last n)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount j h := by
  classical
  unfold armPullCountBefore armPullCount
  have hset :
      (Finset.univ.filter fun u : Fin (n + 1) ↦
          u < Fin.last n ∧
            ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) u).1 = j).card =
        (Finset.univ.filter fun t : Fin n ↦ (h t).1 = j).card := by
    refine Finset.card_bij
      (fun u hu ↦ ⟨u.val,
        (Finset.mem_filter.1 hu).2.1⟩) ?_ ?_ ?_
    · intro u hu
      have hun : u.val < n := (Finset.mem_filter.1 hu).2.1
      have hsel := (Finset.mem_filter.1 hu).2.2
      rw [Fin.snoc, dif_pos hun] at hsel
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (h ⟨u.val, hun⟩).1 = j
      exact hsel
    · intro u₁ hu₁ u₂ hu₂ heq
      apply Fin.ext
      change u₁.val = u₂.val
      exact congrArg (fun q : Fin n ↦ q.val) heq
    · intro v hv
      refine ⟨v.castSucc, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact v.isLt
      · simpa using (Finset.mem_filter.1 hv).2
  have hto :
      {t | (h t).1 = j}.toFinset =
        Finset.univ.filter fun t : Fin n ↦ (h t).1 = j := by
    ext t
    simp
  rw [hto]
  exact hset

private theorem armFirstRewardsMean_snoc_of_le {k n : ℕ}
    (j : Fin k) (s : ℕ) (h : BanditHistory k n)
    (z : Fin k × ℝ) (hs : s ≤ armPullCount j h) :
    armFirstRewardsMean j s
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armFirstRewardsMean j s h := by
  classical
  unfold armFirstRewardsMean
  congr 1
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  have heach :
      (∑ t : Fin n,
          if ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)
                t.castSucc).1 = j ∧
              armPullCountBefore j t.castSucc
                (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) < s
            then
              ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)
                t.castSucc).2
            else 0) =
        ∑ t : Fin n,
          if (h t).1 = j ∧ armPullCountBefore j t h < s
            then (h t).2 else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [armPullCountBefore_castSucc_snoc]
    simp
  rw [heach]
  simp [armPullCountBefore_last_snoc, not_lt_of_ge hs]

private theorem armPullCount_snoc_len {k n : ℕ}
    (j : Fin k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount j
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount j h + if z.1 = j then 1 else 0 := by
  classical
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, armPullCount_eq_sum_indicator,
    armPullCount_eq_sum_indicator j h, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = j <;> simp [hz]

private theorem armPullCount_prefixLen_le {k n m : ℕ}
    (j : Fin k) (h : BanditHistory k n) (hm : m ≤ n) :
    armPullCount j (banditHistoryPrefixLen h m hm) ≤
      armPullCount j h := by
  induction n with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact le_rfl
  | succ n ih =>
      by_cases hmn : m = n + 1
      · subst m
        simp [banditHistoryPrefixLen_self]
      · have hm' : m ≤ n :=
          Nat.le_of_lt_succ (lt_of_le_of_ne hm hmn)
        let g : BanditHistory k n := Fin.init h
        let z : Fin k × ℝ := h (Fin.last n)
        have hsnoc :
            Fin.snoc (α := fun _ ↦ Fin k × ℝ) g z = h := by
          simpa [g, z] using Fin.snoc_init_self h
        have hpref :
            banditHistoryPrefixLen h m hm =
              banditHistoryPrefixLen g m hm' := by
          rw [← hsnoc]
          exact banditHistoryPrefixLen_snoc hm' g z
        rw [hpref, ← hsnoc, armPullCount_snoc_len]
        exact (ih g hm').trans (Nat.le_add_right _ _)

private theorem armFirstRewardsMean_prefixLen {k n m : ℕ}
    (j : Fin k) (h : BanditHistory k n) (hm : m ≤ n) :
    armFirstRewardsMean j
        (armPullCount j (banditHistoryPrefixLen h m hm)) h =
      armEmpiricalMean j (banditHistoryPrefixLen h m hm) := by
  induction n with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rw [banditHistoryPrefixLen_self]
      exact armFirstRewardsMean_pullCount_eq_empiricalMean j h
  | succ n ih =>
      by_cases hmn : m = n + 1
      · subst m
        simpa [banditHistoryPrefixLen_self] using
          armFirstRewardsMean_pullCount_eq_empiricalMean j h
      · have hm' : m ≤ n :=
          Nat.le_of_lt_succ (lt_of_le_of_ne hm hmn)
        let g : BanditHistory k n := Fin.init h
        let z : Fin k × ℝ := h (Fin.last n)
        have hsnoc :
            Fin.snoc (α := fun _ ↦ Fin k × ℝ) g z = h := by
          simpa [g, z] using Fin.snoc_init_self h
        have hpref :
            banditHistoryPrefixLen h m hm =
              banditHistoryPrefixLen g m hm' := by
          rw [← hsnoc]
          exact banditHistoryPrefixLen_snoc hm' g z
        rw [hpref, ← hsnoc]
        rw [armFirstRewardsMean_snoc_of_le]
        · exact ih g hm'
        · exact armPullCount_prefixLen_le j g hm'

private theorem currentGaussianTSTail_prefixLen {k n m : ℕ}
    (j : Fin k) (h : BanditHistory k n) (hm : m ≤ n) (c : ℝ) :
    currentGaussianTSTail j c
        (banditHistoryPrefixLen h m hm) =
      gaussianTSTailProb j
        (armPullCount j (banditHistoryPrefixLen h m hm)) c h := by
  unfold currentGaussianTSTail gaussianTSTailProb
  by_cases hz :
      armPullCount j (banditHistoryPrefixLen h m hm) = 0
  · simp [hz]
  · simp only [hz, if_false]
    rw [armFirstRewardsMean_prefixLen]
    rfl

private theorem armPullCount_prefixLen_eq_before {k n : ℕ}
    (j : Fin k) (t : Fin n) (h : BanditHistory k n) :
    armPullCount j
        (banditHistoryPrefixLen h t.val (Nat.le_of_lt t.isLt)) =
      armPullCountBefore j t h := by
  classical
  unfold armPullCount armPullCountBefore banditHistoryPrefixLen
  have hto :
      {u | (h (Fin.castLE (Nat.le_of_lt t.isLt) u)).1 = j}.toFinset =
        Finset.univ.filter
          (fun u : Fin t.val ↦
            (h (Fin.castLE (Nat.le_of_lt t.isLt) u)).1 = j) := by
    ext u
    simp
  rw [hto]
  symm
  refine Finset.card_bij
    (fun u hu ↦
      (⟨u.val, (Finset.mem_filter.1 hu).2.1⟩ : Fin t.val))
    ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsel := (Finset.mem_filter.1 hu).2.2
    change (h (Fin.castLE (Nat.le_of_lt t.isLt)
      ⟨u.val, (Finset.mem_filter.1 hu).2.1⟩)).1 = j
    simpa using hsel
  · intro u₁ hu₁ u₂ hu₂ heq
    apply Fin.ext
    change u₁.val = u₂.val
    exact congrArg (fun q : Fin t.val ↦ q.val) heq
  · intro v hv
    let u : Fin n := ⟨v.val, lt_trans v.isLt t.isLt⟩
    refine ⟨u, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact v.isLt
      · exact (Finset.mem_filter.1 hv).2
    · rfl

private theorem sum_selected_by_rank {k n : ℕ}
    (j : Fin k) (h : BanditHistory k n) (F : ℕ → ℝ≥0∞) :
    (∑ t : Fin n,
        if (h t).1 = j then F (armPullCountBefore j t h) else 0) =
      ∑ s ∈ Finset.range (armPullCount j h), F s := by
  classical
  induction n with
  | zero =>
      simp [armPullCount]
  | succ n ih =>
      rw [← Fin.snoc_init_self h]
      rw [Fin.sum_univ_castSucc]
      have hprev :
          (∑ t : Fin n,
              if
                  ((Fin.snoc (α := fun _ ↦ Fin k × ℝ)
                    (Fin.init h) (h (Fin.last n))) t.castSucc).1 = j
                then
                  F (armPullCountBefore j t.castSucc
                    (Fin.snoc (α := fun _ ↦ Fin k × ℝ)
                      (Fin.init h) (h (Fin.last n))))
                else 0) =
            ∑ t : Fin n,
              if ((Fin.init h) t).1 = j then
                F (armPullCountBefore j t (Fin.init h)) else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [armPullCountBefore_castSucc_snoc]
        simp
      rw [hprev, ih (Fin.init h), armPullCount_snoc_len]
      have hlast :
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ)
              (Fin.init h) (h (Fin.last n)) (Fin.last n)).1 =
            (h (Fin.last n)).1 := by simp
      rw [hlast, armPullCountBefore_last_snoc]
      by_cases hz : (h (Fin.last n)).1 = j
      · rw [if_pos hz, if_pos hz]
        rw [Finset.sum_range_succ]
      · rw [if_neg hz, if_neg hz]
        simp

private theorem currentGaussianTSTail_prefix_before {k n : ℕ}
    (j : Fin k) (t : Fin n) (h : BanditHistory k n) (c : ℝ) :
    currentGaussianTSTail j c
        (banditHistoryPrefixLen h t.val (Nat.le_of_lt t.isLt)) =
      gaussianTSTailProb j (armPullCountBefore j t h) c h := by
  rw [currentGaussianTSTail_prefixLen,
    armPullCount_prefixLen_eq_before]

private theorem stepKernel_lintegral_arm_weight {k m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k)
    (h : BanditHistory k m) (j : Fin k) (w : ℝ≥0∞) :
    (∫⁻ z, (if z.1 = j then w else 0)
        ∂banditStepKernel ν π m h) =
      ENNReal.ofReal ((π.select m h).real {j}) * w := by
  have hmap :
      Measure.map Prod.fst (banditStepKernel ν π m h) =
        π.select m h := by
    rw [← Kernel.fst_apply, banditStepKernel, Kernel.fst_compProd]
  let f : Fin k → ℝ≥0∞ := fun a ↦ if a = j then w else 0
  have hf : Measurable f := by
    apply Measurable.ite
    · exact measurableSet_singleton j
    · exact measurable_const
    · exact measurable_const
  calc
    (∫⁻ z, (if z.1 = j then w else 0)
        ∂banditStepKernel ν π m h) =
        ∫⁻ z, f z.1 ∂banditStepKernel ν π m h := by rfl
    _ = ∫⁻ a, f a ∂Measure.map Prod.fst
          (banditStepKernel ν π m h) := by
      rw [lintegral_map hf measurable_fst]
    _ = ∫⁻ a, f a ∂π.select m h := by rw [hmap]
    _ = w * (π.select m h) {j} := by
      rw [show f = Set.indicator {j} (fun _ ↦ w) by
        funext a
        by_cases ha : a = j <;> simp [f, ha]]
      rw [lintegral_indicator (measurableSet_singleton j),
        setLIntegral_const]
    _ = ENNReal.ofReal ((π.select m h).real {j}) * w := by
      rw [Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact mul_comm _ _

private theorem roundWeighted_lintegral {k n m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k)
    (hm : m < n) (j : Fin k)
    (W : BanditHistory k m → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ H : BanditHistory k n,
        (if
            (H ⟨m, hm⟩).1 = j
          then
            W (banditHistoryPrefixLen H m
              (Nat.le_of_lt hm))
          else 0)
        ∂banditMeasure ν π n) =
      ∫⁻ h : BanditHistory k m,
        ENNReal.ofReal ((π.select m h).real {j}) * W h
        ∂banditMeasure ν π m := by
  let F : BanditHistory k (m + 1) → ℝ≥0∞ :=
    fun q ↦ if (q (Fin.last m)).1 = j then W (Fin.init q) else 0
  have hF : Measurable F := by
    apply Measurable.ite
    · exact (measurableSet_singleton j).preimage
        (measurable_fst.comp (measurable_pi_apply (Fin.last m)))
    · exact hW.comp (by fun_prop :
        Measurable (fun q : BanditHistory k (m + 1) ↦ Fin.init q))
    · exact measurable_const
  have hmn : m + 1 ≤ n := hm
  have hcomp :
      (fun H : BanditHistory k n ↦
        F (banditHistoryPrefixLen H (m + 1) hmn)) =
      fun H ↦
        if (H ⟨m, hm⟩).1 = j then
          W (banditHistoryPrefixLen H m (Nat.le_of_lt hm))
        else 0 := by
    funext H
    unfold F
    have hlast :
        (banditHistoryPrefixLen H (m + 1) hmn
          (Fin.last m)) = H ⟨m, hm⟩ := by
      rfl
    rw [hlast]
    congr 1
  rw [← hcomp]
  calc
    (∫⁻ H, F (banditHistoryPrefixLen H (m + 1) hmn)
        ∂banditMeasure ν π n) =
        ∫⁻ q, F q ∂Measure.map
          (fun H : BanditHistory k n ↦
            banditHistoryPrefixLen H (m + 1) hmn)
          (banditMeasure ν π n) := by
      rw [lintegral_map hF (measurable_banditHistoryPrefixLen hmn)]
    _ = ∫⁻ q, F q ∂banditMeasure ν π (m + 1) := by
      rw [banditMeasure_map_prefixLen]
    _ = ∫⁻ p, F
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2)
          ∂((banditMeasure ν π m).compProd
            (banditStepKernel ν π m)) := by
      rw [banditMeasure]
      rw [lintegral_map hF measurable_banditHistorySnoc]
    _ = ∫⁻ h, ∫⁻ z,
          (if z.1 = j then W h else 0)
          ∂banditStepKernel ν π m h
          ∂banditMeasure ν π m := by
      change
        (∫⁻ p,
          (F ∘ fun p : BanditHistory k m × (Fin k × ℝ) ↦
            Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2) p
          ∂((banditMeasure ν π m).compProd
            (banditStepKernel ν π m))) = _
      rw [Measure.lintegral_compProd
        (hF.comp measurable_banditHistorySnoc)]
      apply lintegral_congr
      intro h
      apply lintegral_congr
      intro z
      simp [F]
    _ = ∫⁻ h,
        ENNReal.ofReal ((π.select m h).real {j}) * W h
        ∂banditMeasure ν π m := by
      apply lintegral_congr
      intro h
      exact stepKernel_lintegral_arm_weight ν π h j (W h)

private noncomputable def selectionMass {k m : ℕ}
    (π : BanditPolicy k) (j : Fin k) (h : BanditHistory k m) : ℝ≥0∞ :=
  ENNReal.ofReal ((π.select m h).real {j})

private noncomputable def tsCoeff {k m : ℕ}
    (j : Fin k) (c : ℝ) (h : BanditHistory k m) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / currentGaussianTSTail j c h - 1)

private noncomputable def tsHigh {k m : ℕ}
    (N : ℕ) (j : Fin k) (c : ℝ)
    (h : BanditHistory k m) : ℝ≥0∞ :=
  if 1 / (N : ℝ) < currentGaussianTSTail j c h then 1 else 0

private theorem measurable_selectionMass {k m : ℕ}
    (π : BanditPolicy k) (j : Fin k) :
    Measurable (selectionMass π j :
      BanditHistory k m → ℝ≥0∞) := by
  rw [show
    (selectionMass π j :
      BanditHistory k m → ℝ≥0∞) =
      fun h ↦ (π.select m h) {j} by
    funext h
    rw [selectionMass, Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]]
  exact Kernel.measurable_coe (π.select m) (measurableSet_singleton j)

private theorem measurable_tsCoeff {k m : ℕ}
    (j : Fin k) (c : ℝ) :
    Measurable (tsCoeff j c :
      BanditHistory k m → ℝ≥0∞) := by
  exact ((measurable_const.div
    (measurable_currentGaussianTSTail j c)).sub
      measurable_const).ennreal_ofReal

private theorem measurable_tsHigh {k m : ℕ}
    (N : ℕ) (j : Fin k) (c : ℝ) :
    Measurable (tsHigh N j c :
      BanditHistory k m → ℝ≥0∞) := by
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_currentGaussianTSTail j c)
  · exact measurable_const
  · exact measurable_const

private theorem gaussianTS_selectionMass_bound {k m N : ℕ}
    [NeZero k] (hN : 0 < N) (π : BanditPolicy k)
    (hπ : IsGaussianTSPolicy π)
    (h : BanditHistory k m) (i₀ i : Fin k) (hi : i ≠ i₀)
    (c : ℝ) :
    selectionMass π i h ≤
      tsCoeff i₀ c h * selectionMass π i₀ h +
        tsHigh N i c h * selectionMass π i h +
        ENNReal.ofReal (1 / (N : ℝ)) := by
  have hb := gaussianTSDistribution_selection_bound hN h i₀ i hi c
  rw [← hπ m h] at hb
  have hcoef :
      0 ≤ 1 / currentGaussianTSTail i₀ c h - 1 := by
    exact sub_nonneg.mpr (by
      simpa [one_div] using
        (one_le_inv₀ (currentGaussianTSTail_pos i₀ c h)).2
          (currentGaussianTSTail_le_one i₀ c h))
  have hp0 : 0 ≤ (π.select m h).real {i₀} := measureReal_nonneg
  have hpi : 0 ≤ (π.select m h).real {i} := measureReal_nonneg
  have hq : 0 ≤ 1 / (N : ℝ) := by positivity
  by_cases hhigh :
      1 / (N : ℝ) < currentGaussianTSTail i c h
  · rw [if_pos hhigh] at hb
    apply (ENNReal.ofReal_le_ofReal hb).trans
    simp only [selectionMass, tsCoeff, tsHigh, hhigh, if_true,
      one_mul]
    rw [ENNReal.ofReal_add (mul_nonneg hcoef hp0) hpi,
      ENNReal.ofReal_mul hcoef]
    exact le_add_of_nonneg_right bot_le
  · rw [if_neg hhigh] at hb
    apply (ENNReal.ofReal_le_ofReal hb).trans
    simp only [selectionMass, tsCoeff, tsHigh, hhigh, if_false,
      zero_mul, add_zero]
    rw [ENNReal.ofReal_add (mul_nonneg hcoef hp0) hq,
      ENNReal.ofReal_mul hcoef]

private theorem armPullCount_le_horizon {k n : ℕ}
    (j : Fin k) (h : BanditHistory k n) :
    armPullCount j h ≤ n := by
  classical
  rw [armPullCount_eq_sum_indicator]
  calc
    (∑ t : Fin n, if (h t).1 = j then 1 else 0) ≤
        ∑ _t : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro t ht
      split <;> omega
    _ = n := by simp

private theorem comparatorRoundSum_le {k n : ℕ}
    (j : Fin k) (c : ℝ) (H : BanditHistory k n) :
    (∑ t : Fin n,
        if (H t).1 = j then
          tsCoeff j c
            (banditHistoryPrefixLen H t.val
              (Nat.le_of_lt t.isLt))
        else 0) ≤
      ∑ s ∈ Finset.range (armPullCount j H),
        ENNReal.ofReal
          (1 / gaussianTSTailProb j s c H - 1) := by
  let F : ℕ → ℝ≥0∞ := fun s ↦
    ENNReal.ofReal (1 / gaussianTSTailProb j s c H - 1)
  have heq :
      (∑ t : Fin n,
          if (H t).1 = j then
            tsCoeff j c
              (banditHistoryPrefixLen H t.val
                (Nat.le_of_lt t.isLt))
          else 0) =
        ∑ t : Fin n,
          if (H t).1 = j then
            F (armPullCountBefore j t H)
          else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hj : (H t).1 = j
    · rw [if_pos hj, if_pos hj]
      unfold tsCoeff F
      rw [currentGaussianTSTail_prefix_before]
    · rw [if_neg hj, if_neg hj]
  rw [heq, sum_selected_by_rank]

private theorem highRoundSum_le {k n : ℕ}
    (N : ℕ) (j : Fin k) (c : ℝ) (H : BanditHistory k n) :
    (∑ t : Fin n,
        if (H t).1 = j then
          tsHigh N j c
            (banditHistoryPrefixLen H t.val
              (Nat.le_of_lt t.isLt))
        else 0) ≤
      ∑ s ∈ Finset.range (armPullCount j H),
        (if 1 / (N : ℝ) < gaussianTSTailProb j s c H
          then (1 : ℝ≥0∞) else 0) := by
  let F : ℕ → ℝ≥0∞ := fun s ↦
    if 1 / (N : ℝ) < gaussianTSTailProb j s c H
      then 1 else 0
  have heq :
      (∑ t : Fin n,
          if (H t).1 = j then
            tsHigh N j c
              (banditHistoryPrefixLen H t.val
                (Nat.le_of_lt t.isLt))
          else 0) =
        ∑ t : Fin n,
          if (H t).1 = j then
            F (armPullCountBefore j t H)
          else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hj : (H t).1 = j
    · rw [if_pos hj, if_pos hj]
      unfold tsHigh F
      rw [currentGaussianTSTail_prefix_before]
    · rw [if_neg hj, if_neg hj]
  rw [heq, sum_selected_by_rank]

end BanditAlgorithm

open BanditAlgorithm

theorem solution {k : ℕ} [NeZero k]
    (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsGaussianTSPolicy π)
    (i₀ : Fin k) (h₀ : banditArmMean ν i₀ = banditOptimalMean ν)
    (i : Fin k) (hi : i ≠ i₀) (ε : ℝ) (n : ℕ) :
    ∫⁻ h, (armPullCount i h : ℝ≥0∞) ∂banditMeasure ν π n ≤
      1 + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
            ENNReal.ofReal
              (1 / gaussianTSTailProb i₀ s
                (banditArmMean ν i₀ - ε) h - 1)
            ∂banditMeasure ν π n)
        + ∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
            (if 1 / (n : ℝ) <
                gaussianTSTailProb i s
                  (banditArmMean ν i₀ - ε) h
              then (1 : ℝ≥0∞) else 0)
            ∂banditMeasure ν π n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [banditMeasure, armPullCount]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let c : ℝ := banditArmMean ν i₀ - ε
  let L : Fin n → BanditHistory k n → ℝ≥0∞ :=
    fun t H ↦ if (H t).1 = i then 1 else 0
  let C : Fin n → BanditHistory k n → ℝ≥0∞ :=
    fun t H ↦ if (H t).1 = i₀ then
      tsCoeff i₀ c
        (banditHistoryPrefixLen H t.val
          (Nat.le_of_lt t.isLt))
      else 0
  let U : Fin n → BanditHistory k n → ℝ≥0∞ :=
    fun t H ↦ if (H t).1 = i then
      tsHigh n i c
        (banditHistoryPrefixLen H t.val
          (Nat.le_of_lt t.isLt))
      else 0
  have hL (t : Fin n) : Measurable (L t) := by
    apply Measurable.ite
    · exact (measurableSet_singleton i).preimage
        (measurable_fst.comp (measurable_pi_apply t))
    · exact measurable_const
    · exact measurable_const
  have hC (t : Fin n) : Measurable (C t) := by
    apply Measurable.ite
    · exact (measurableSet_singleton i₀).preimage
        (measurable_fst.comp (measurable_pi_apply t))
    · exact (measurable_tsCoeff i₀ c).comp
        (measurable_banditHistoryPrefixLen
          (Nat.le_of_lt t.isLt))
    · exact measurable_const
  have hU (t : Fin n) : Measurable (U t) := by
    apply Measurable.ite
    · exact (measurableSet_singleton i).preimage
        (measurable_fst.comp (measurable_pi_apply t))
    · exact (measurable_tsHigh n i c).comp
        (measurable_banditHistoryPrefixLen
          (Nat.le_of_lt t.isLt))
    · exact measurable_const
  have hcount (H : BanditHistory k n) :
      (armPullCount i H : ℝ≥0∞) = ∑ t : Fin n, L t H := by
    rw [armPullCount_eq_sum_indicator]
    simp [L]
  have hround (t : Fin n) :
      (∫⁻ H, L t H ∂banditMeasure ν π n) ≤
        (∫⁻ H, C t H ∂banditMeasure ν π n) +
          (∫⁻ H, U t H ∂banditMeasure ν π n) +
          ENNReal.ofReal (1 / (n : ℝ)) := by
    have hLrw := roundWeighted_lintegral ν π t.isLt i
      (fun _ : BanditHistory k t.val ↦ (1 : ℝ≥0∞))
      measurable_const
    have hCrw := roundWeighted_lintegral ν π t.isLt i₀
      (tsCoeff i₀ c) (measurable_tsCoeff i₀ c)
    have hUrw := roundWeighted_lintegral ν π t.isLt i
      (tsHigh n i c) (measurable_tsHigh n i c)
    have hA :
        Measurable (fun h : BanditHistory k t.val ↦
          tsCoeff i₀ c h * selectionMass π i₀ h) :=
      (measurable_tsCoeff i₀ c).mul
        (measurable_selectionMass π i₀)
    have hB :
        Measurable (fun h : BanditHistory k t.val ↦
          tsHigh n i c h * selectionMass π i h) :=
      (measurable_tsHigh n i c).mul
        (measurable_selectionMass π i)
    calc
      (∫⁻ H, L t H ∂banditMeasure ν π n) =
          ∫⁻ h : BanditHistory k t.val,
            selectionMass π i h ∂banditMeasure ν π t.val := by
        simpa [L, selectionMass] using hLrw
      _ ≤ ∫⁻ h : BanditHistory k t.val,
            (tsCoeff i₀ c h * selectionMass π i₀ h +
              tsHigh n i c h * selectionMass π i h) +
              ENNReal.ofReal (1 / (n : ℝ))
            ∂banditMeasure ν π t.val := by
        apply lintegral_mono
        intro h
        simpa [add_assoc] using
          gaussianTS_selectionMass_bound hn π hπ h i₀ i hi c
      _ =
          (∫⁻ h : BanditHistory k t.val,
            tsCoeff i₀ c h * selectionMass π i₀ h
            ∂banditMeasure ν π t.val) +
          (∫⁻ h : BanditHistory k t.val,
            tsHigh n i c h * selectionMass π i h
            ∂banditMeasure ν π t.val) +
          ENNReal.ofReal (1 / (n : ℝ)) := by
        have hAB : Measurable (fun h : BanditHistory k t.val ↦
            tsCoeff i₀ c h * selectionMass π i₀ h +
              tsHigh n i c h * selectionMass π i h) := hA.add hB
        rw [lintegral_add_left hAB,
          lintegral_add_left hA]
        simp
      _ =
          (∫⁻ H, C t H ∂banditMeasure ν π n) +
          (∫⁻ H, U t H ∂banditMeasure ν π n) +
          ENNReal.ofReal (1 / (n : ℝ)) := by
        rw [hCrw, hUrw]
        simp only [C, U, selectionMass]
        congr 2 <;> apply lintegral_congr <;> intro h <;>
          rw [mul_comm]
  have hconst :
      (∑ _t : Fin n, ENNReal.ofReal (1 / (n : ℝ))) = 1 := by
    rw [Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    rw [one_div, ENNReal.ofReal_inv_of_pos hnreal]
    rw [show ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) by simp]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n)
  have hsum :
      (∑ t : Fin n, ∫⁻ H, L t H ∂banditMeasure ν π n) ≤
        (∑ t : Fin n, ∫⁻ H, C t H ∂banditMeasure ν π n) +
          (∑ t : Fin n, ∫⁻ H, U t H ∂banditMeasure ν π n) + 1 := by
    calc
      (∑ t : Fin n, ∫⁻ H, L t H ∂banditMeasure ν π n) ≤
          ∑ t : Fin n,
            ((∫⁻ H, C t H ∂banditMeasure ν π n) +
              (∫⁻ H, U t H ∂banditMeasure ν π n) +
              ENNReal.ofReal (1 / (n : ℝ))) := by
        exact Finset.sum_le_sum fun t ht ↦ hround t
      _ =
          (∑ t : Fin n, ∫⁻ H, C t H ∂banditMeasure ν π n) +
          (∑ t : Fin n, ∫⁻ H, U t H ∂banditMeasure ν π n) +
          ∑ _t : Fin n, ENNReal.ofReal (1 / (n : ℝ)) := by
        simp_rw [Finset.sum_add_distrib]
      _ = _ := by rw [hconst]
  have hCsum :
      (∫⁻ H, ∑ t : Fin n, C t H ∂banditMeasure ν π n) ≤
        ∫⁻ H, ∑ s ∈ Finset.range (armPullCount i₀ H),
          ENNReal.ofReal
            (1 / gaussianTSTailProb i₀ s c H - 1)
          ∂banditMeasure ν π n :=
    lintegral_mono fun H ↦ by
      simpa [C] using comparatorRoundSum_le i₀ c H
  have hUsum :
      (∫⁻ H, ∑ t : Fin n, U t H ∂banditMeasure ν π n) ≤
        ∫⁻ H, ∑ s ∈ Finset.range (armPullCount i H),
          (if 1 / (n : ℝ) < gaussianTSTailProb i s c H
            then (1 : ℝ≥0∞) else 0)
          ∂banditMeasure ν π n :=
    lintegral_mono fun H ↦ by
      simpa [U] using highRoundSum_le n i c H
  rw [show
      (fun H : BanditHistory k n ↦ (armPullCount i H : ℝ≥0∞)) =
        fun H ↦ ∑ t : Fin n, L t H by
      funext H
      exact hcount H]
  have hsum' := hsum
  rw [← MeasureTheory.lintegral_finset_sum Finset.univ
      (fun t _ ↦ hC t),
    ← MeasureTheory.lintegral_finset_sum Finset.univ
      (fun t _ ↦ hU t)] at hsum'
  calc
    (∫⁻ H, ∑ t : Fin n, L t H ∂banditMeasure ν π n) =
        ∑ t : Fin n, ∫⁻ H, L t H ∂banditMeasure ν π n := by
      rw [MeasureTheory.lintegral_finset_sum Finset.univ
        (fun t _ ↦ hL t)]
    _ ≤
        (∫⁻ H, ∑ t : Fin n, C t H ∂banditMeasure ν π n) +
          (∫⁻ H, ∑ t : Fin n, U t H ∂banditMeasure ν π n) + 1 :=
      hsum'
    _ ≤
        (∫⁻ H, ∑ s ∈ Finset.range (armPullCount i₀ H),
          ENNReal.ofReal
            (1 / gaussianTSTailProb i₀ s c H - 1)
          ∂banditMeasure ν π n) +
        (∫⁻ H, ∑ s ∈ Finset.range (armPullCount i H),
          (if 1 / (n : ℝ) < gaussianTSTailProb i s c H
            then (1 : ℝ≥0∞) else 0)
          ∂banditMeasure ν π n) + 1 := by
      gcongr
    _ = 1 +
        (∫⁻ H, ∑ s ∈ Finset.range (armPullCount i₀ H),
          ENNReal.ofReal
            (1 / gaussianTSTailProb i₀ s
              (banditArmMean ν i₀ - ε) H - 1)
          ∂banditMeasure ν π n) +
        (∫⁻ H, ∑ s ∈ Finset.range (armPullCount i H),
          (if 1 / (n : ℝ) <
              gaussianTSTailProb i s
                (banditArmMean ν i₀ - ε) H
            then (1 : ℝ≥0∞) else 0)
          ∂banditMeasure ν π n) := by
      unfold c
      ac_rfl
