-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.property_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:25:13.812125+00:00
-- url     : https://prove2.me/submissions/d5dbd52f-f39c-4648-958d-88226a474506

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory
open FirstPriceLearning.ContextLowerBound

open InformationTheory
namespace CLBH

lemma gap_nonneg (M α T : ℕ) : 0 ≤ gap M α T := Real.sqrt_nonneg _

lemma gap_le (M α T : ℕ) (hT : (α + 1) * M ≤ T) : gap M α T ≤ 1 / 4 := by
  unfold gap
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · have hTr : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [div_le_iff₀ (by positivity)]
    have : ((((α + 1) * M : ℕ)) : ℝ) ≤ T := by exact_mod_cast hT
    linarith

lemma gap_pos (M α T : ℕ) (hM : 0 < M) (hT : (α + 1) * M ≤ T) : 0 < gap M α T := by
  unfold gap
  apply Real.sqrt_pos.mpr
  have hK : 0 < (α + 1) * M := by positivity
  have hTp : 0 < T := lt_of_lt_of_le hK hT
  have h1 : (0 : ℝ) < (((α + 1) * M : ℕ) : ℝ) := by exact_mod_cast hK
  have h2 : (0 : ℝ) < T := by exact_mod_cast hTp
  positivity

lemma hardMean_bounds (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : 0 ≤ hardMean M α T u c a ∧ hardMean M α T u c a ≤ 1 := by
  have h1 := gap_nonneg M α T
  have h2 := gap_le M α T hT
  unfold hardMean
  split_ifs <;> constructor <;> linarith

lemma bern_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (bernoulliReal p) := by
  constructor
  simp only [bernoulliReal, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

lemma integral_bern (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∫ x, x ∂(bernoulliReal p) = p := by
  unfold bernoulliReal
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [ENNReal.toReal_ofReal h0]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma hardLaw_prob (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    IsProbabilityMeasure (hardLaw M α T u) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  unfold hardLaw
  infer_instance

lemma map_coord (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) :
    (hardLaw M α T u).map (fun x => x c a) = bernoulliReal (hardMean M α T u c a) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  have h1 := (measurePreserving_eval
    (fun c => Measure.pi fun a => bernoulliReal (hardMean M α T u c a)) c).map_eq
  have h2 := (measurePreserving_eval (fun a => bernoulliReal (hardMean M α T u c a)) a).map_eq
  have : (fun x : Fin M → Act M α → ℝ => x c a) =
      (Function.eval a : (Act M α → ℝ) → ℝ) ∘ (Function.eval c : (Fin M → Act M α → ℝ) → _) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply a) (measurable_pi_apply c)]
  unfold hardLaw
  rw [h1, h2]

lemma meanReward_hard (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : meanReward (hardLaw M α T u) c a = hardMean M α T u c a := by
  unfold meanReward
  have hm : Measurable (fun x : Fin M → Act M α → ℝ => x c a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply c)
  have := integral_map (μ := hardLaw M α T u) hm.aemeasurable
    (aestronglyMeasurable_id (μ := (hardLaw M α T u).map (fun x => x c a)))
  simp only [id] at this
  rw [← this, map_coord M α T hT u c a]
  exact integral_bern _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2

end CLBH

namespace CLBP5

open InformationTheory

lemma measurable_update_fst {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (i0 : ι) :
    Measurable (fun p : X × (ι → X) => Function.update p.2 i0 p.1) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i = i0
  · subst h; simpa using measurable_fst
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply i).comp measurable_snd

lemma pi_replace {ι X : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (ν : ι → Measure X) [∀ i, IsProbabilityMeasure (ν i)] (i0 : ι) (β : Measure X)
    [IsProbabilityMeasure β] :
    (β.prod (Measure.pi ν)).map (fun p => Function.update p.2 i0 p.1) =
      Measure.pi (Function.update ν i0 β) := by
  haveI : ∀ i, SigmaFinite (Function.update ν i0 β i) := by
    intro i; by_cases h : i = i0
    · subst h; simp only [Function.update_self]; infer_instance
    · simp only [Function.update_of_ne h]; infer_instance
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_update_fst i0) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : X × (ι → X) => Function.update p.2 i0 p.1) ⁻¹' (Set.univ.pi s) =
      s i0 ×ˢ (Set.univ.pi (Function.update s i0 Set.univ)) := by
    ext ⟨z, x⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i0, fun i => ?_⟩
      by_cases hi : i = i0
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨hz, hx⟩ i
      by_cases hi : i = i0
      · subst hi; simpa using hz
      · simpa [Function.update_of_ne hi] using hx i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have h1 : (fun i => Function.update ν i0 β i (s i)) =
      Function.update (fun i => ν i (s i)) i0 (β (s i0)) := by
    funext i; by_cases hi : i = i0
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have h2 : (fun i => ν i (Function.update s i0 Set.univ i)) =
      Function.update (fun i => ν i (s i)) i0 1 := by
    funext i; by_cases hi : i = i0
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h1, h2, Finset.prod_update_of_mem (Finset.mem_univ _),
    Finset.prod_update_of_mem (Finset.mem_univ _), one_mul]

lemma klDiv_prod_left {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (β β' : Measure X) (μ : Measure Y) [IsProbabilityMeasure β] [IsProbabilityMeasure β']
    [IsProbabilityMeasure μ] :
    klDiv (β'.prod μ) (β.prod μ) = klDiv β' β := by
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  exact klDiv_compProd_left _ _ _

end CLBP5

namespace CLBP5

open InformationTheory

noncomputable def dens (p q : ℝ) (x : ℝ) : ENNReal :=
  if x = 1 then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))

lemma measurable_dens (p q : ℝ) : Measurable (dens p q) := by
  unfold dens
  exact Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const

lemma bern_withDensity (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliReal p = (bernoulliReal q).withDensity (dens p q) := by
  ext s hs
  rw [withDensity_apply _ hs]
  unfold bernoulliReal
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure]
  classical
  rw [restrict_dirac' hs, restrict_dirac' hs]
  have e0 : dens p q 0 = ENNReal.ofReal ((1 - p) / (1 - q)) := by simp [dens]
  have e1 : dens p q 1 = ENNReal.ofReal (p / q) := by simp [dens]
  have m0 : ENNReal.ofReal (1 - q) * ENNReal.ofReal ((1 - p) / (1 - q)) = ENNReal.ofReal (1 - p) := by
    have : (1 - q) ≠ 0 := by linarith
    rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; field_simp
  have m1 : ENNReal.ofReal q * ENNReal.ofReal (p / q) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; field_simp
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h0 h1 h1
  · simp [lintegral_dirac, e0, e1, m0, m1, h0, h1]
  · simp [lintegral_dirac, e0, m0, h0, h1]
  · simp [lintegral_dirac, e1, m1, h0, h1]
  · simp [h0, h1]

lemma klFun_le_sq (t : ℝ) (ht : 0 ≤ t) : klFun t ≤ (t - 1) ^ 2 := by
  rw [klFun_apply]
  rcases eq_or_lt_of_le ht with h | h
  · subst h; simp
  · have := Real.log_le_sub_one_of_pos h
    nlinarith

lemma klDiv_bern_le (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klDiv (bernoulliReal p) (bernoulliReal q) ≤
      ENNReal.ofReal ((p - q) ^ 2 / q + (p - q) ^ 2 / (1 - q)) := by
  haveI := CLBH.bern_prob p hp0 hp1
  haveI := CLBH.bern_prob q hq0.le hq1.le
  have hW := bern_withDensity p q hp0 hp1 hq0 hq1
  have hac : bernoulliReal p ≪ bernoulliReal q := by
    rw [hW]; exact withDensity_absolutelyContinuous _ _
  have hrn : (bernoulliReal p).rnDeriv (bernoulliReal q) =ᵐ[bernoulliReal q] dens p q := by
    conv_lhs => rw [hW]
    exact Measure.rnDeriv_withDensity _ (measurable_dens p q)
  have hint : Integrable (fun x => klFun ((bernoulliReal p).rnDeriv (bernoulliReal q) x).toReal)
      (bernoulliReal q) := by
    unfold bernoulliReal
    refine Integrable.add_measure ?_ ?_
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hfin : klDiv (bernoulliReal p) (bernoulliReal q) ≠ ⊤ :=
    klDiv_ne_top hac ((integrable_klFun_rnDeriv_iff hac).mp hint)
  have hval : (klDiv (bernoulliReal p) (bernoulliReal q)).toReal =
      (1 - q) * klFun ((1 - p) / (1 - q)) + q * klFun (p / q) := by
    rw [toReal_klDiv_eq_integral_klFun hac]
    rw [integral_congr_ae (g := fun x => klFun (dens p q x).toReal)
      (hrn.mono (fun x hx => by simp only; rw [hx]))]
    unfold bernoulliReal
    rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac]
    · simp [dens, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - q), ENNReal.toReal_ofReal hq0.le,
        ENNReal.toReal_ofReal (div_nonneg (by linarith : 0 ≤ 1 - p) (by linarith : 0 ≤ 1 - q)),
        ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le)]
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  rw [hval]
  have k1 := klFun_le_sq ((1 - p) / (1 - q)) (div_nonneg (by linarith) (by linarith))
  have k2 := klFun_le_sq (p / q) (div_nonneg hp0 hq0.le)
  have e1 : (1 - q) * ((1 - p) / (1 - q) - 1) ^ 2 = (p - q) ^ 2 / (1 - q) := by
    have : (1 - q) ≠ 0 := by linarith
    field_simp; ring
  have e2 : q * (p / q - 1) ^ 2 = (p - q) ^ 2 / q := by
    field_simp
  have := mul_le_mul_of_nonneg_left k1 (by linarith : (0:ℝ) ≤ 1 - q)
  have := mul_le_mul_of_nonneg_left k2 hq0.le
  linarith

end CLBP5

namespace CLBP5

open InformationTheory

noncomputable def nu (M α T : ℕ) (u : Fin M → Fin (α + 1)) : Fin M × Act M α → Measure ℝ :=
  fun q => bernoulliReal (hardMean M α T u q.1 q.2)

lemma nu_prob (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (q : Fin M × Act M α) :
    IsProbabilityMeasure (nu M α T u q) :=
  CLBH.bern_prob _ (CLBH.hardMean_bounds M α T hT u q.1 q.2).1
    (CLBH.hardMean_bounds M α T hT u q.1 q.2).2

lemma hardLaw_flat (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    hardLaw M α T u =
      (Measure.pi (nu M α T u)).map (MeasurableEquiv.curry (Fin M) (Act M α) ℝ) := by
  haveI : ∀ c b, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c b)) := fun c b =>
    nu_prob M α T hT u (c, b)
  have h := Measure.infinitePi_map_curry (fun c b => bernoulliReal (hardMean M α T u c b))
  simp_rw [Measure.infinitePi_eq_pi] at h
  unfold hardLaw nu
  exact h.symm


lemma measurable_reveal' {M α : ℕ} (a : Act M α) :
    Measurable (reveal (M := M) (feedbackGraph M α) a) := by
  classical
  refine measurable_pi_lambda _ (fun c => measurable_pi_lambda _ (fun b => ?_))
  unfold reveal
  split_ifs
  · exact (measurable_pi_apply b).comp (measurable_pi_apply c)
  · exact measurable_const

lemma revealed_iff {M α : ℕ} (u : Fin M → Fin (α + 1)) (c : Fin M) (hu : u c ≠ 0) (a : Act M α) :
    FirstPriceLearning.GraphFeedback.Revealed (feedbackGraph M α) a (c, u c) ↔
      a.1 < c ∨ a = (c, u c) := by
  unfold FirstPriceLearning.GraphFeedback.Revealed feedbackGraph
  constructor
  · rintro (h | h | ⟨_, _, h⟩)
    · exact Or.inr h.symm
    · exact Or.inl h
    · exact absurd h hu
  · rintro (h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h.symm

end CLBP5

theorem solution (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (hu : u c ≠ 0) (a : Act M α) :
    klDiv (observedLaw M α T (Function.update u c 0) a) (observedLaw M α T u a) =
        (if a.1 < c ∨ a = (c, u c) then
          klDiv (bernoulliReal (1 / 4)) (bernoulliReal (1 / 4 + 2 * gap M α T))
        else 0) ∧
      klDiv (observedLaw M α T (Function.update u c 0) a) (observedLaw M α T u a) ≤
        ENNReal.ofReal
          (64 / 3 * gap M α T ^ 2 * (if a.1 < c ∨ a = (c, u c) then 1 else 0)) := by
  classical
  have g0 := CLBH.gap_nonneg M α T
  have g1 := CLBH.gap_le M α T hT
  set u' := Function.update u c 0 with hu'
  set i0 : Fin M × Act M α := (c, (c, u c)) with hi0
  set B := bernoulliReal (1 / 4 + 2 * gap M α T) with hB
  set B' := bernoulliReal (1 / 4 : ℝ) with hB'
  haveI hBp : IsProbabilityMeasure B := CLBH.bern_prob _ (by linarith) (by linarith)
  haveI hB'p : IsProbabilityMeasure B' := CLBH.bern_prob _ (by norm_num) (by norm_num)
  haveI : ∀ q, IsProbabilityMeasure (CLBP5.nu M α T u q) := CLBP5.nu_prob M α T hT u
  set F := Measure.pi (CLBP5.nu M α T u) with hF
  -- the two families of factors
  have hnu_self : CLBP5.nu M α T u i0 = B := by
    simp only [CLBP5.nu, hi0, hB, hardMean, if_true, hu, if_false]
  have hnu' : CLBP5.nu M α T u' = Function.update (CLBP5.nu M α T u) i0 B' := by
    funext q
    obtain ⟨c', i, j⟩ := q
    by_cases hq : (c', (i, j)) = i0
    · rw [hq, Function.update_self]
      simp only [CLBP5.nu, hi0, hB', hardMean, if_true, hu, if_false, hu', Function.update_self]
      rw [if_neg (Ne.symm hu)]
    · rw [Function.update_of_ne hq]
      simp only [CLBP5.nu, hardMean, hu']
      by_cases hc' : c' = c
      · subst hc'
        simp only [Function.update_self]
        by_cases hic : i = c'
        · subst hic
          have hj : j ≠ u i := fun h => hq (by rw [h])
          simp only [if_true]
          by_cases hj0 : j = 0
          · simp [hj0]
          · simp [hj0, Ne.symm hj0, Ne.symm hj]
        · simp [hic]
      · simp [Function.update_of_ne hc']
  set R := fun p : ℝ × (Fin M × Act M α → ℝ) => Function.update p.2 i0 p.1 with hR
  have hflat : F = (B.prod F).map R := by
    rw [hR, CLBP5.pi_replace, ← hnu_self, Function.update_eq_self]
  have hflat' : Measure.pi (CLBP5.nu M α T u') = (B'.prod F).map R := by
    rw [hR, CLBP5.pi_replace, hnu']
  set G := fun p : ℝ × (Fin M × Act M α → ℝ) =>
    reveal (feedbackGraph M α) a (MeasurableEquiv.curry (Fin M) (Act M α) ℝ (R p)) with hG
  have hRm : Measurable R := CLBP5.measurable_update_fst i0
  have hGm : Measurable G :=
    (CLBP5.measurable_reveal' a).comp ((MeasurableEquiv.measurable _).comp hRm)
  have hobs : observedLaw M α T u a = (B.prod F).map G := by
    unfold observedLaw
    rw [CLBP5.hardLaw_flat M α T hT u, ← hF]
    conv_lhs => rw [hflat]
    rw [Measure.map_map (MeasurableEquiv.measurable _) hRm,
      Measure.map_map (CLBP5.measurable_reveal' a) ((MeasurableEquiv.measurable _).comp hRm)]
    rfl
  have hobs' : observedLaw M α T u' a = (B'.prod F).map G := by
    unfold observedLaw
    rw [CLBP5.hardLaw_flat M α T hT u', hflat', Measure.map_map (MeasurableEquiv.measurable _) hRm,
      Measure.map_map (CLBP5.measurable_reveal' a) ((MeasurableEquiv.measurable _).comp hRm)]
    rfl
  haveI : IsProbabilityMeasure (observedLaw M α T u a) := by
    rw [hobs]; exact Measure.isProbabilityMeasure_map hGm.aemeasurable
  haveI : IsProbabilityMeasure (observedLaw M α T u' a) := by
    rw [hobs']; exact Measure.isProbabilityMeasure_map hGm.aemeasurable
  have hupper : klDiv (observedLaw M α T u' a) (observedLaw M α T u a) ≤ klDiv B' B := by
    rw [hobs, hobs', ← CLBP5.klDiv_prod_left B B' F]
    exact klDiv_map_le _ _ hGm
  have hKLbound : klDiv B' B ≤ ENNReal.ofReal (64 / 3 * gap M α T ^ 2) := by
    refine (CLBP5.klDiv_bern_le _ _ (by norm_num) (by norm_num) (by linarith) (by linarith)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    set q := 1 / 4 + 2 * gap M α T
    have hq0 : 0 < q := by simp only [q]; linarith
    have hq1 : 0 < 1 - q := by simp only [q]; linarith
    have hqq : 3 / 16 ≤ q * (1 - q) := by simp only [q]; nlinarith
    have hsq : (1 / 4 - q) ^ 2 = 4 * gap M α T ^ 2 := by simp only [q]; ring
    rw [div_add_div _ _ (ne_of_gt hq0) (ne_of_gt hq1), div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hqq (sq_nonneg (gap M α T))
    nlinarith [this, hsq]
  by_cases hcond : a.1 < c ∨ a = (c, u c)
  · have hrev := (CLBP5.revealed_iff u c hu a).mpr hcond
    -- lower bound through the revealed coordinate
    have hcoord : ∀ v : Fin M → Fin (α + 1),
        (observedLaw M α T v a).map (fun y => y c (c, u c)) =
          bernoulliReal (hardMean M α T v c (c, u c)) := by
      intro v
      unfold observedLaw
      rw [Measure.map_map (by fun_prop) (CLBP5.measurable_reveal' a)]
      have : (fun y : Fin M → Act M α → ℝ => y c (c, u c)) ∘ reveal (feedbackGraph M α) a =
          fun x => x c (c, u c) := by
        funext x; simp [reveal, hrev]
      rw [this, CLBH.map_coord M α T hT v c (c, u c)]
    have hlower : klDiv B' B ≤ klDiv (observedLaw M α T u' a) (observedLaw M α T u a) := by
      have h1 := hcoord u
      have h2 := hcoord u'
      have hm1 : hardMean M α T u c (c, u c) = 1 / 4 + 2 * gap M α T := by
        simp [hardMean, hu]
      have hm2 : hardMean M α T u' c (c, u c) = 1 / 4 := by
        simp only [hardMean, hu', Function.update_self, if_true, hu, if_false]
        rw [if_neg (Ne.symm hu)]
      rw [hm1] at h1; rw [hm2] at h2
      rw [hB, hB', ← h1, ← h2]
      exact klDiv_map_le _ _ (by fun_prop)
    have heq := le_antisymm hupper hlower
    refine ⟨by rw [if_pos hcond, heq], ?_⟩
    rw [if_pos hcond, mul_one, heq]
    exact hKLbound
  · have hrev : ¬ FirstPriceLearning.GraphFeedback.Revealed (feedbackGraph M α) a (c, u c) :=
      fun h => hcond ((CLBP5.revealed_iff u c hu a).mp h)
    have hGsnd : G = (fun x => reveal (feedbackGraph M α) a
        (MeasurableEquiv.curry (Fin M) (Act M α) ℝ x)) ∘ Prod.snd := by
      funext p
      simp only [hG, hR, Function.comp_apply]
      funext c' b
      simp only [reveal, MeasurableEquiv.coe_curry, Function.curry_apply]
      split_ifs with hb
      · have : (c', b) ≠ i0 := by
          intro h; rw [hi0] at h
          have hb' : b = (c, u c) := (Prod.ext_iff.mp h).2
          exact hrev (hb' ▸ hb)
        rw [Function.update_of_ne this]
      · rfl
    have hHm : Measurable (fun x => reveal (feedbackGraph M α) a
        (MeasurableEquiv.curry (Fin M) (Act M α) ℝ x)) :=
      (CLBP5.measurable_reveal' a).comp (MeasurableEquiv.measurable _)
    have hsame : observedLaw M α T u' a = observedLaw M α T u a := by
      rw [hobs, hobs', hGsnd, ← Measure.map_map hHm measurable_snd,
        ← Measure.map_map hHm measurable_snd, Measure.map_snd_prod,
        Measure.map_snd_prod]
      simp
    refine ⟨by rw [if_neg hcond, hsame, klDiv_self], ?_⟩
    rw [if_neg hcond, hsame, klDiv_self]
    simp
