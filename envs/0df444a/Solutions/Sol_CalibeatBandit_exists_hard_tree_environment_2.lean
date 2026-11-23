-- Prove2me | solution 2 for CalibeatBandit.exists_hard_tree_environment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:40.218883+00:00
-- url     : https://prove2.me/submissions/923d69bc-dc22-4fe6-9ab0-12afd1d09ea7

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis
import Theorems.Thm_CalibeatBandit_expected_swapRegret_ge_proxy
import Theorems.Thm_CalibeatBandit_tree_expected_proxy

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const

end Measurability

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

theorem swapGain_le_best {K T : ℕ} (q u : ℕ → Fin K → ℝ) (i j : Fin K) :
    swapGain T q u i j ≤ bestSwapGain T q u i :=
  Finset.le_sup' (swapGain T q u i) (Finset.mem_univ j)

/-- The swap map can maximize every row independently. -/
theorem pseudoSwapRegret_eq_sum_bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) :
    pseudoSwapRegret T q u = ∑ i, bestSwapGain T q u i := by
  classical
  have score (f : Fin K → Fin K) :
      (∑ t ∈ Finset.range T, ((∑ i, q t i * u t (f i)) - q t ⬝ᵥ u t)) =
        ∑ i, swapGain T q u i (f i) := by
    unfold swapGain dotProduct
    have h (t : ℕ) : (∑ i, q t i * u t (f i)) - ∑ i, q t i * u t i =
        ∑ i, q t i * (u t (f i) - u t i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [h]
    exact Finset.sum_comm
  unfold pseudoSwapRegret
  simp_rw [score]
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => Finset.sum_le_sum fun i _ => swapGain_le_best q u i (f i)
  · have exists_best (i : Fin K) : ∃ j, bestSwapGain T q u i = swapGain T q u i j := by
      obtain ⟨j, _, h⟩ := Finset.exists_mem_eq_sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)
      exact ⟨j, h⟩
    choose f hf using exists_best
    calc
      _ = ∑ i, swapGain T q u i (f i) := Finset.sum_congr rfl fun i _ => hf i
      _ ≤ _ := Finset.le_sup' (fun f : Fin K → Fin K => ∑ i, swapGain T q u i (f i))
        (Finset.mem_univ f)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set MeasureTheory

theorem treeBonusProb_mem {h M U : ℕ} (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) (a : TreeAction h M U) :
    treeBonusProb leaf coin leafCoin selected a ∈ Icc (0 : ℝ) 1 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  rcases a with ⟨v, side⟩ | (j | j)
  · have hdepth : (v.1 : ℕ) ≤ h := Nat.le_of_lt_succ v.1.isLt
    have hd : ((v.1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hdepth
    have hh : 0 < treeHeight h := by unfold treeHeight; positivity
    have hfrac : (((v.1 : ℕ) + 1 : ℝ) / (2 * treeHeight h)) ∈ Icc 0 1 := by
      refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
      unfold treeHeight
      linarith
    simp only [treeBonusProb]
    split_ifs <;> assumption
  · simp only [treeBonusProb]
    split <;> assumption
  · exact hz

/-- Extract a single oblivious environment from a randomized construction.
The two independent seeds describe the environment and the learner. -/
theorem exists_environment_of_seedwise_lower_bound {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] (μ : Measure Ω) (ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (regret : Ω × S → ℝ)
    (hi : Integrable regret (μ.prod ν)) {b : ℝ}
    (h : ∀ s, b ≤ ∫ ω, regret (ω, s) ∂μ) :
    ∃ ω, b ≤ ∫ s, regret (ω, s) ∂ν := by
  let g (ω : Ω) := ∫ s, regret (ω, s) ∂ν
  have hgi : Integrable g μ := hi.integral_prod_left
  have hmean : b ≤ ∫ ω, g ω ∂μ := by
    rw [← integral_prod regret hi, integral_prod_symm regret hi]
    simpa using integral_mono (integrable_const b) hi.swap.integral_prod_left h
  by_contra! hs
  have hp (ω : Ω) : 0 < b - g ω := sub_pos.mpr (hs ω)
  have hfull : Function.support (fun ω => b - g ω) = Set.univ := by
    ext ω
    simp [Function.mem_support, (hp ω).ne']
  have hpos := (integral_pos_iff_support_of_nonneg (fun ω => (hp ω).le)
    ((integrable_const b).sub hgi)).mpr (by rw [hfull, measure_univ]; exact (zero_lt_one : (0 : ENNReal) < 1))
  rw [integral_sub (integrable_const _) hgi] at hpos
  simp only [integral_const, probReal_univ, one_smul] at hpos
  linarith

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The normalized observation uses the bonus transform exactly when the
independent threshold draw falls below the current bonus probability. -/
noncomputable def observationLaw (η u : ℝ) : Measure ℝ :=
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  ENNReal.ofReal (1 - u) • Q + ENNReal.ofReal u • Q.map (bonusTransform η)

theorem map_threshold_observation (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let V : Measure ℝ := volume.restrict (Ico 0 1)
    (V.prod Q).map (fun p : ℝ × ℝ => if p.1 < u then bonusTransform η p.2 else p.2) =
      observationLaw η u := by
  intro Q V
  let f (p : ℝ × ℝ) := if p.1 < u then bonusTransform η p.2 else p.2
  have hb : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (hb.comp measurable_snd) measurable_snd
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have hlow : V (Iio u) = ENNReal.ofReal u := by
    rw [show V = volume.restrict (Ico 0 1) from rfl, Measure.restrict_apply measurableSet_Iio]
    have he : Iio u ∩ Ico (0 : ℝ) 1 = Ico 0 u := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ico]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_le hu.2⟩⟩
    rw [he, Real.volume_Ico, sub_zero]
  have hhigh : V (Ici u) = ENNReal.ofReal (1 - u) := by
    rw [show V = volume.restrict (Ico 0 1) from rfl, Measure.restrict_apply measurableSet_Ici]
    have he : Ici u ∩ Ico (0 : ℝ) 1 = Ico u 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ico]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hu.1.trans h.1, h.2⟩⟩
    rw [he, Real.volume_Ico]
  ext s hs
  change ((V.prod Q).map f) s = _
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  let F := (Iio u).indicator (fun _ : ℝ => Q (bonusTransform η ⁻¹' s))
  let G := (Ici u).indicator (fun _ : ℝ => Q s)
  have he (w : ℝ) : Q (Prod.mk w ⁻¹' (f ⁻¹' s)) = F w + G w := by
    by_cases hw : w < u
    · have heq : Prod.mk w ⁻¹' (f ⁻¹' s) = bonusTransform η ⁻¹' s := by
        ext z
        simp [f, hw]
      simp [heq, F, G, hw, not_le_of_gt hw]
    · have heq : Prod.mk w ⁻¹' (f ⁻¹' s) = s := by
        ext z
        simp [f, hw]
      simp [heq, F, G, hw, le_of_not_gt hw]
  rw [lintegral_congr he, lintegral_add_left (measurable_const.indicator measurableSet_Iio)]
  change (∫⁻ w, F w ∂V) + (∫⁻ w, G w ∂V) = _
  rw [lintegral_indicator_const measurableSet_Iio, lintegral_indicator_const measurableSet_Ici,
    hlow, hhigh]
  simp only [observationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hb hs]
  change _ = ENNReal.ofReal (1 - u) * Q s + ENNReal.ofReal u * Q (bonusTransform η ⁻¹' s)
  ac_rfl

/-- A round uses one common base draw and an independent threshold draw
for each action. This is the normalized reward for one action. -/
noncomputable def observedReward {N : ℕ} (η u : ℝ) (i : Fin N)
    (p : ℝ × (Fin N → ℝ)) : ℝ :=
  if p.2 i < u then bonusTransform η p.1 else p.1

theorem measurable_observedReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (observedReward η u i) := by
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  exact Measurable.ite (measurableSet_lt ((measurable_pi_apply i).comp measurable_snd) measurable_const)
    (hm.comp measurable_fst) measurable_fst

theorem map_observedReward {N : ℕ} (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) (i : Fin N) :
    let Q : Measure ℝ := volume.restrict (Icc 0 1)
    let V : Measure ℝ := volume.restrict (Ico 0 1)
    let tape := Q.prod (Measure.pi fun _ : Fin N => V)
    tape.map (observedReward η u i) = observationLaw η u := by
  intro Q V tape
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  let get (r : Fin N → ℝ) := r i
  have hg : Measurable get := measurable_pi_apply i
  have hmap : τ.map get = V := (measurePreserving_eval (fun _ : Fin N => V) i).map_eq
  have hp : (Q.prod τ).map (Prod.map id get) = Q.prod V := by
    rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id, hmap]
  let f (p : ℝ × ℝ) := if p.1 < u then bonusTransform η p.2 else p.2
  have hb : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hf : Measurable f := Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (hb.comp measurable_snd) measurable_snd
  change (Q.prod τ).map ((f ∘ Prod.swap) ∘ Prod.map id get) = _
  rw [← Measure.map_map (hf.comp measurable_swap) (measurable_id.prodMap hg), hp,
    ← Measure.map_map hf measurable_swap, Measure.prod_swap]
  exact map_threshold_observation η hu

open scoped Interval in
/-- The normalized observation has mean one half plus ηu/6. -/
theorem integral_observationLaw (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    (∫ x, x ∂observationLaw η u) = 1 / 2 + η * u / 6 := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  have hm : Measurable (bonusTransform η) := by unfold bonusTransform; fun_prop
  have hrest : Q = volume.restrict (Ioc 0 1) := (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm
  have hbase : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  have hquad : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hb : Continuous (bonusTransform η) := by unfold bonusTransform; fun_prop
  have ht : IntervalIntegrable (bonusTransform η) volume 0 1 := hb.intervalIntegrable _ _
  have hi : Integrable (fun x : ℝ => x) Q := by rw [hrest]; exact hbase.1
  have ht' : Integrable (bonusTransform η) Q := by rw [hrest]; exact ht.1
  have hmi : Integrable (fun x : ℝ => x) (Q.map (bonusTransform η)) :=
    (integrable_map_measure continuous_id.stronglyMeasurable.aestronglyMeasurable hm.aemeasurable).mpr ht'
  have hbaseval : (∫ x, x ∂Q) = (1 / 2 : ℝ) := by
    rw [hrest, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
    norm_num
  have htrans : (∫ x, x ∂Q.map (bonusTransform η)) = 1 / 2 + η / 6 := by
    rw [integral_map (f := fun x : ℝ => x) hm.aemeasurable continuous_id.stronglyMeasurable.aestronglyMeasurable,
      hrest, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [show bonusTransform η = fun x => x + η * (x - x ^ 2) by
      funext x; unfold bonusTransform; ring]
    rw [intervalIntegral.integral_add hbase ((hbase.sub hquad).const_mul η),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hbase hquad,
      integral_id, integral_pow]
    norm_num
    ring
  change (∫ x, x ∂(ENNReal.ofReal (1 - u) • Q +
    ENNReal.ofReal u • Q.map (bonusTransform η))) = _
  rw [integral_add_measure (hi.smul_measure ENNReal.ofReal_ne_top) (hmi.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, hbaseval, htrans]
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr hu.2), ENNReal.toReal_ofReal hu.1, smul_eq_mul]
  ring

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

@[simp] theorem rewardTapePrefix_refl (N r : ℕ) :
    rewardTapePrefix N (le_refl r) = id := by simp [rewardTapePrefix]

@[simp] theorem rewardTapePrefix_succ (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    rewardTapePrefix N (Nat.le_succ_of_le h) = rewardTapePrefix N h ∘ Prod.fst := by
  unfold rewardTapePrefix
  exact Nat.leRec_succ _ _ h

theorem measurable_rewardTapePrefix (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    Measurable (rewardTapePrefix N h) := by
  induction h with
  | refl => rw [rewardTapePrefix_refl]; exact measurable_id
  | step h ih => rw [rewardTapePrefix_succ N h]; exact ih.comp measurable_fst

theorem rewardTapePrefix_comp (N : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    rewardTapePrefix N hrs ∘ rewardTapePrefix N hst = rewardTapePrefix N (hrs.trans hst) := by
  induction hst with
  | refl => simp
  | step hs ih =>
    rw [rewardTapePrefix_succ N hs, rewardTapePrefix_succ N (hrs.trans hs)]
    funext tape
    exact congrFun ih tape.1

theorem rewardTapePrefix_map (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    (rewardTapeLaw N t).map (rewardTapePrefix N h) = rewardTapeLaw N r := by
  induction h with
  | refl => rw [rewardTapePrefix_refl, Measure.map_id]
  | step h ih =>
    rw [rewardTapePrefix_succ N h]
    change ((rewardTapeLaw N _).prod (roundDrawLaw N)).map
      (rewardTapePrefix N h ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_rewardTapePrefix N h) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, ih]

/-- Information supplied by the reward tape before each round. Past the
horizon the information stays the full tape. -/
def rewardTapeFiltration (N T : ℕ) : Filtration ℕ (rewardTapeMeasurable N T) where
  seq t := MeasurableSpace.comap (rewardTapePrefix N (min_le_right t T))
    (rewardTapeMeasurable N (min t T))
  mono' := by
    intro r s hrs
    have h := min_le_min hrs (le_refl T)
    change MeasurableSpace.comap (rewardTapePrefix N (min_le_right r T))
        (rewardTapeMeasurable N (min r T)) ≤
      MeasurableSpace.comap (rewardTapePrefix N (min_le_right s T))
        (rewardTapeMeasurable N (min s T))
    rw [← rewardTapePrefix_comp N h (min_le_right s T), ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((measurable_rewardTapePrefix N h).comap_le)
  le' := fun t => (measurable_rewardTapePrefix N (min_le_right t T)).comap_le

/-- Conditional expectation over a fresh independent draw, with the past
as the first coordinate of the product sample space. -/
theorem condExp_product_past {A B : Type*} [mA : MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (hf : Measurable f) (hi : Integrable f (μ.prod ν)) :
    condExp (mA.comap (Prod.fst : A × B → A)) (μ.prod ν) f =ᵐ[μ.prod ν]
      fun p => ∫ b, f (p.1, b) ∂ν := by
  let g (a : A) := ∫ b, f (a, b) ∂ν
  have hm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hg : Integrable g μ := hi.integral_prod_left
  have hfst : Measurable[mA.comap (Prod.fst : A × B → A)] (Prod.fst : A × B → A) :=
    measurable_iff_comap_le.mpr le_rfl
  have hGi : Integrable (g ∘ Prod.fst) (μ.prod ν) := by
    have he : (μ.prod ν).map Prod.fst = μ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    have he' : Integrable g ((μ.prod ν).map Prod.fst) := by rw [he]; exact hg
    exact (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp he'
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hi
    (fun _ _ _ => hGi.integrableOn) ?_ (hm.comp hfst).aestronglyMeasurable
  rintro s ⟨t, ht, rfl⟩ _
  have hset : (Prod.fst : A × B → A) ⁻¹' t = t ×ˢ (univ : Set B) := by ext p; simp
  change (∫ p in Prod.fst ⁻¹' t, (g ∘ Prod.fst) p ∂μ.prod ν) = ∫ p in Prod.fst ⁻¹' t, f p ∂μ.prod ν
  rw [hset, setIntegral_prod _ hGi.integrableOn, setIntegral_prod _ hi.integrableOn]
  simp only [Measure.restrict_univ]
  congr 1
  funext a
  change (∫ _ : B, g a ∂ν) = g a
  simp

set_option linter.style.haveILetI false in
/-- A conditional expectation can be pulled back through a measure-preserving
map when the information is pulled back through the same map. -/
theorem condExp_pullback {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (p : A → B) (hp : MeasurePreserving p μ ν)
    (m : MeasurableSpace B) (hm : m ≤ mB)
    (f : B → ℝ) (hf : Integrable f ν) :
    μ[f ∘ p | m.comap p] =ᵐ[μ] (ν[f | m]) ∘ p := by
  letI : MeasurableSpace B := mB
  let g := ν[f | m]
  have hmg : StronglyMeasurable[m] g := stronglyMeasurable_condExp
  have hgi : Integrable g ν := integrable_condExp
  have hmapped {k : B → ℝ} (hk : Integrable k ν) : Integrable k (μ.map p) := by
    rw [hp.map_eq]
    exact hk
  have hgp : Integrable (g ∘ p) μ := (hmapped hgi).comp_measurable hp.measurable
  have hfp : Integrable (f ∘ p) μ := (hmapped hf).comp_measurable hp.measurable
  have hmp : m.comap p ≤ mA := (MeasurableSpace.comap_mono hm).trans hp.measurable.comap_le
  have hpg : Measurable[m.comap p, m] p := measurable_iff_comap_le.mpr le_rfl
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hmp hfp
    (fun _ _ _ => hgp.integrableOn) ?_ (hmg.comp_measurable hpg).aestronglyMeasurable
  rintro _ ⟨s, hs, rfl⟩ _
  have hs' : MeasurableSet s := hm s hs
  have hg' : AEStronglyMeasurable g (μ.map p) := hp.map_eq ▸ hgi.aestronglyMeasurable
  have hf' : AEStronglyMeasurable f (μ.map p) := hp.map_eq ▸ hf.aestronglyMeasurable
  change (∫ x in p ⁻¹' s, g (p x) ∂μ) = ∫ x in p ⁻¹' s, f (p x) ∂μ
  rw [← setIntegral_map hs' hg' hp.measurable.aemeasurable,
      ← setIntegral_map hs' hf' hp.measurable.aemeasurable, hp.map_eq]
  exact setIntegral_condExp hm hf hs

private theorem comap_prefix_congr (N T : ℕ) {r s : ℕ} (h : r = s) (hr : r ≤ T) (hs : s ≤ T) :
    (rewardTapeMeasurable N r).comap (rewardTapePrefix N hr) =
      (rewardTapeMeasurable N s).comap (rewardTapePrefix N hs) := by
  subst s
  rfl

/-- On the full tape, the information at round t is the pullback of
the past coordinate of the tape truncated just after round t. -/
theorem rewardTapeFiltration_eq_comap {N T t : ℕ} (ht : t < T) :
    rewardTapeFiltration N T t =
      ((rewardTapeMeasurable N t).comap
        (Prod.fst : RewardTape N (t + 1) → RewardTape N t)).comap
        (rewardTapePrefix N (Nat.succ_le_of_lt ht)) := by
  have he : rewardTapeFiltration N T t =
      (rewardTapeMeasurable N t).comap (rewardTapePrefix N ht.le) := by
    change (rewardTapeMeasurable N (min t T)).comap
      (rewardTapePrefix N (min_le_right t T)) = _
    exact comap_prefix_congr N T (min_eq_left ht.le) _ _
  rw [he]
  let fst : RewardTape N (t + 1) → RewardTape N t := Prod.fst
  have hf : rewardTapePrefix N (Nat.le_succ t) = fst := by
    rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
  have hc := rewardTapePrefix_comp N (Nat.le_succ t) (Nat.succ_le_of_lt ht)
  rw [hf] at hc
  calc
    _ = (rewardTapeMeasurable N t).comap (fst ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht)) :=
      congrArg (fun (g : RewardTape N T → RewardTape N t) =>
        (rewardTapeMeasurable N t).comap g) hc.symm
    _ = _ := MeasurableSpace.comap_comp.symm

/-- The one-step conditional mean on the full reward tape is the integral
over that step's independent draw, with the observed past held fixed. -/
theorem condExp_rewardTape_step {N T t : ℕ} (ht : t < T)
    (f : RewardTape N (t + 1) → ℝ) (hf : Measurable f)
    (hi : Integrable f (rewardTapeLaw N (t + 1))) :
    let pre := rewardTapePrefix N (Nat.succ_le_of_lt ht)
    (rewardTapeLaw N T)[f ∘ pre | rewardTapeFiltration N T t] =ᵐ[rewardTapeLaw N T]
      fun x => ∫ d, f ((pre x).1, d) ∂roundDrawLaw N := by
  intro pre
  let μ := rewardTapeLaw N T
  let ν := rewardTapeLaw N (t + 1)
  let m := (rewardTapeMeasurable N t).comap
    (Prod.fst : RewardTape N (t + 1) → RewardTape N t)
  have hp : MeasurePreserving pre μ ν :=
    ⟨measurable_rewardTapePrefix N _, rewardTapePrefix_map N _⟩
  have hm : m ≤ rewardTapeMeasurable N (t + 1) := measurable_fst.comap_le
  rw [rewardTapeFiltration_eq_comap ht]
  have h := condExp_pullback μ ν pre hp m hm f hi
  refine h.trans ?_
  have hv := condExp_product_past (rewardTapeLaw N t) (roundDrawLaw N) f hf hi
  change (ν[f | m]) =ᵐ[ν] (fun p => ∫ d, f (p.1, d) ∂roundDrawLaw N) at hv
  refine ae_of_ae_map hp.aemeasurable
    (p := fun p => (ν[f | m]) p = ∫ d, f (p.1, d) ∂roundDrawLaw N) ?_
  rw [hp.map_eq]
  exact hv

/-- Every function of the truncated tape through round t is measurable
at t + 1 in the full tape filtration. -/
theorem measurable_rewardTape_step {N T t : ℕ} (ht : t < T)
    (f : RewardTape N (t + 1) → ℝ) (hf : Measurable f) :
    Measurable[rewardTapeFiltration N T (t + 1)]
      (f ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht)) := by
  have he : rewardTapeFiltration N T (t + 1) =
      (rewardTapeMeasurable N (t + 1)).comap (rewardTapePrefix N (Nat.succ_le_of_lt ht)) := by
    change (rewardTapeMeasurable N (min (t + 1) T)).comap
      (rewardTapePrefix N (min_le_right (t + 1) T)) = _
    exact comap_prefix_congr N T (min_eq_left (Nat.succ_le_of_lt ht)) _ _
  rw [he]
  exact hf.comp (measurable_iff_comap_le.mpr le_rfl)

open scoped ENNReal

theorem measurable_supportedBase : Measurable fun x => (supportedBase x : ℝ) := by
  have he : (fun x => (supportedBase x : ℝ)) = fun x => if x ∈ Icc (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [supportedBase, hx]
  rw [he]
  exact Measurable.ite measurableSet_Icc measurable_id measurable_const

theorem measurable_supportedThreshold : Measurable fun x => (supportedThreshold x : ℝ) := by
  have he : (fun x => (supportedThreshold x : ℝ)) = fun x => if x ∈ Ico (0 : ℝ) 1 then x else 0 := by
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1 <;> simp [supportedThreshold, hx]
  rw [he]
  exact Measurable.ite measurableSet_Ico measurable_id measurable_const

theorem measurable_boundedRoundReward {N : ℕ} (η u : ℝ) (i : Fin N) :
    Measurable (boundedRoundReward η u i) := by
  let z (d : ℝ × (Fin N → ℝ)) : ℝ := supportedBase d.1
  have hz : Measurable z := measurable_supportedBase.comp measurable_fst
  have hth := measurable_supportedThreshold.comp ((measurable_pi_apply i).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × (Fin N → ℝ) → (Fin N → ℝ))))
  unfold boundedRoundReward bonusReward
  simp only [decide_eq_true_eq]
  exact (measurable_const.add (hz.div_const _)).add
    (((hz.const_mul _).mul (measurable_const.sub hz)).mul
      (Measurable.ite (measurableSet_lt hth measurable_const) measurable_const measurable_const))

/-- Clipping on the null complement of the support does not change the mean. -/
theorem integral_boundedRoundReward {N : ℕ} (η : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) (i : Fin N)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) :
    (∫ d, boundedRoundReward η u i d ∂roundDrawLaw N) = 3 / 16 + η * u / 48 := by
  let Q : Measure ℝ := volume.restrict (Icc 0 1)
  let V : Measure ℝ := volume.restrict (Ico 0 1)
  have _ : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure V := ⟨by simp [V, Real.volume_Ico]⟩
  let τ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => V
  have hdraw : (roundDrawLaw N).map Prod.fst = Q := by
    change (Q.prod τ).map Prod.fst = Q
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hthreshold : (roundDrawLaw N).map (fun d => d.2 i) = V := by
    change (Q.prod τ).map ((fun r => r i) ∘ Prod.snd) = V
    rw [← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, (measurePreserving_eval (fun _ : Fin N => V) i).map_eq]
  have hbase : ∀ᵐ d ∂roundDrawLaw N, d.1 ∈ Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hdraw]
    exact ae_restrict_mem measurableSet_Icc
  have hth : ∀ᵐ d ∂roundDrawLaw N, d.2 i ∈ Ico (0 : ℝ) 1 := by
    apply ae_of_ae_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    change ∀ᵐ x ∂(roundDrawLaw N).map (fun d => d.2 i), x ∈ Ico (0 : ℝ) 1
    rw [hthreshold]
    exact ae_restrict_mem measurableSet_Ico
  have heq : boundedRoundReward η u i =ᵐ[roundDrawLaw N]
      fun d => 1 / 8 + observedReward η u i d / 8 := by
    filter_upwards [hbase, hth] with d hz hd
    unfold boundedRoundReward bonusReward observedReward bonusTransform
    simp only [supportedBase, supportedThreshold, dif_pos hz, dif_pos hd, decide_eq_true_eq]
    split <;> ring
  have hb : Integrable (observedReward η u i) (roundDrawLaw N) := by
    refine Integrable.of_bound ((measurable_observedReward η u i).aestronglyMeasurable) 1 ?_
    filter_upwards [hbase] with d hz
    unfold observedReward bonusTransform
    rcases hz with ⟨hz0,hz1⟩
    rw [Real.norm_eq_abs, abs_le]
    by_cases hh : d.2 i < u
    · rw [if_pos hh]
      have hn : 0 ≤ η * d.1 * (1 - d.1) := by positivity
      have hp : 0 ≤ (1 - η * d.1) * (1 - d.1) :=
        mul_nonneg (sub_nonneg.mpr (mul_le_one₀ hη₁ hz0 hz1)) (sub_nonneg.mpr hz1)
      constructor <;> nlinarith
    · rw [if_neg hh]
      constructor <;> linarith
  have hi :
      (∫ d, observedReward η u i d ∂roundDrawLaw N) = 1 / 2 + η * u / 6 := by
    have hmap : (roundDrawLaw N).map (observedReward η u i) = observationLaw η u :=
      map_observedReward η hu i
    have he := integral_map (measurable_observedReward η u i).aemeasurable
      (measurable_id.aestronglyMeasurable :
        AEStronglyMeasurable (id : ℝ → ℝ) ((roundDrawLaw N).map (observedReward η u i)))
    rw [hmap] at he
    exact he.symm.trans (integral_observationLaw η hu)
  rw [integral_congr_ae heq, integral_add (integrable_const _) (hb.div_const _),
    integral_const, probReal_univ, one_smul, integral_div, hi]
  ring

theorem boundedRoundReward_mem {N : ℕ} {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (u : ℝ) (i : Fin N) (d : ℝ × (Fin N → ℝ)) :
    boundedRoundReward η u i d ∈ Icc (0 : ℝ) 1 := by
  let z := (supportedBase d.1 : ℝ)
  have hz₀ : 0 ≤ z := (supportedBase d.1).property.1
  have hz₁ : z ≤ 1 := (supportedBase d.1).property.2
  have hsub : 0 ≤ 1 - z := sub_nonneg.mpr hz₁
  have hprod : 0 ≤ η / 8 * z * (1 - z) := by positivity
  have hηz : η / 8 * z ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 8 : ℝ) * z := mul_le_mul_of_nonneg_right (by linarith) hz₀
      _ ≤ 1 / 8 := mul_le_of_le_one_right (by positivity) hz₁
  have hp : η / 8 * z * (1 - z) ≤ 1 / 8 := by
    exact (mul_le_mul_of_nonneg_right hηz hsub).trans
      (mul_le_of_le_one_right (by positivity) (by linarith))
  unfold boundedRoundReward bonusReward
  change (1 / 8 + z / 8 + η / 8 * z * (1 - z) * (if _ then 1 else 0) : ℝ) ∈ Icc 0 1
  split <;> simp only [mul_one, mul_zero] <;> exact ⟨by linarith, by linarith⟩

/-- A policy's one-round swap gain minus its predicted gain. The prediction
uses the bonus probabilities, and the policy depends only on the past. -/
noncomputable def centeredTreeStep {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : RewardTape N t → Fin N) (i j : Fin N) (x : RewardTape N (t + 1)) : ℝ :=
  if pick x.1 = i then
    boundedRoundReward η (u j) j x.2 - boundedRoundReward η (u i) i x.2 -
      (η / 48) * (u j - u i)
  else 0

theorem measurable_centeredTreeStep {N t : ℕ} (η : ℝ) (u : Fin N → ℝ)
    (pick : RewardTape N t → Fin N) (hp : Measurable pick) (i j : Fin N) :
    Measurable (centeredTreeStep η u pick i j) := by
  exact Measurable.ite (measurableSet_eq_fun (hp.comp measurable_fst) measurable_const)
    ((((measurable_boundedRoundReward η (u j) j).comp measurable_snd).sub
      ((measurable_boundedRoundReward η (u i) i).comp measurable_snd)).sub measurable_const)
    measurable_const

theorem abs_centeredTreeStep {N t : ℕ} {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (u : Fin N → ℝ) (hu : ∀ i, u i ∈ Icc 0 1)
    (pick : RewardTape N t → Fin N) (i j : Fin N) (x : RewardTape N (t + 1)) :
    |centeredTreeStep η u pick i j x| ≤ 2 := by
  unfold centeredTreeStep
  split
  · obtain ⟨hi₀, hi₁⟩ := boundedRoundReward_mem hη hη₁ (u i) i x.2
    obtain ⟨hj₀, hj₁⟩ := boundedRoundReward_mem hη hη₁ (u j) j x.2
    have h₀ : (-1 : ℝ) ≤ u j - u i := by linarith only [(hu j).1, (hu i).2]
    have h₁ : u j - u i ≤ 1 := by linarith only [(hu j).2, (hu i).1]
    have hη' : 0 ≤ η / 48 := by positivity
    rw [abs_le]
    constructor
    · linarith only [mul_le_mul_of_nonneg_left h₁ hη', hj₀, hi₁, hη₁]
    · linarith only [mul_le_mul_of_nonneg_left h₀ hη', hj₁, hi₀, hη₁]
  · norm_num

/-- Realized swap gain minus predicted gain is a martingale difference
for the reward tape of the tree construction. -/
theorem condExp_centeredTreeStep {N T t : ℕ} (ht : t < T) {η : ℝ}
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (u : Fin N → ℝ) (hu : ∀ i, u i ∈ Icc 0 1)
    (pick : RewardTape N t → Fin N) (hp : Measurable pick) (i j : Fin N) :
    let d := centeredTreeStep η u pick i j ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht)
    (rewardTapeLaw N T)[d | rewardTapeFiltration N T t] =ᵐ[rewardTapeLaw N T] 0 := by
  intro d
  let f := centeredTreeStep η u pick i j
  have hm := measurable_centeredTreeStep η u pick hp i j
  have hi : Integrable f (rewardTapeLaw N (t + 1)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 2 (Filter.Eventually.of_forall fun x => ?_)
    exact Real.norm_eq_abs _ ▸ abs_centeredTreeStep hη hη₁ u hu pick i j x
  refine (condExp_rewardTape_step ht f hm hi).trans ?_
  refine Filter.Eventually.of_forall fun x => ?_
  let p := rewardTapePrefix N (Nat.succ_le_of_lt ht) x
  change (∫ w, f (p.1, w) ∂roundDrawLaw N) = 0
  by_cases ha : pick p.1 = i
  · have hr (k : Fin N) : Integrable (boundedRoundReward η (u k) k) (roundDrawLaw N) := by
      refine Integrable.of_bound (measurable_boundedRoundReward η (u k) k).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun w => ?_)
      obtain ⟨hl, hh⟩ := boundedRoundReward_mem hη hη₁ (u k) k w
      rwa [Real.norm_eq_abs, abs_of_nonneg hl]
    simp only [f, centeredTreeStep, ha, if_true]
    let ν := roundDrawLaw N
    let a := η / 48 * (u j - u i)
    calc
      _ = (∫ w, boundedRoundReward η (u j) j w - boundedRoundReward η (u i) i w ∂ν) -
          (∫ _w, a ∂ν) := integral_sub ((hr j).sub (hr i)) (integrable_const a)
      _ = 0 := by
        change (∫ w, boundedRoundReward η (u j) j w - boundedRoundReward η (u i) i w ∂roundDrawLaw N) -
          (∫ _w, a ∂roundDrawLaw N) = 0
        rw [integral_sub (hr j) (hr i), integral_boundedRoundReward η (hu j) j hη hη₁,
          integral_boundedRoundReward η (hu i) i hη hη₁, integral_const, probReal_univ, one_smul]
        dsimp [a]
        ring
  · simp [f, centeredTreeStep, ha]

/-- The common base reward cancels in a swap comparison. The resulting
martingale increment has the manuscript's bound η/16. -/
theorem abs_centeredTreeStep_sharp {N t : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (u : Fin N → ℝ) (hu : ∀ i, u i ∈ Icc 0 1)
    (pick : RewardTape N t → Fin N) (i j : Fin N) (x : RewardTape N (t + 1)) :
    |centeredTreeStep η u pick i j x| ≤ η / 16 := by
  unfold centeredTreeStep
  split
  · let z := (supportedBase x.2.1 : ℝ)
    have hz₀ : 0 ≤ z := (supportedBase x.2.1).property.1
    have hz₁ : z ≤ 1 := (supportedBase x.2.1).property.2
    let b := η / 8 * z * (1 - z)
    have hb₀ : 0 ≤ b := by dsimp [b]; positivity
    have hb₁ : b ≤ η / 32 := by
      have h : z * (1 - z) ≤ 1 / 4 := by nlinarith only [sq_nonneg (z - 1 / 2)]
      have hl := mul_le_mul_of_nonneg_left h (div_nonneg hη (by norm_num : (0 : ℝ) ≤ 8))
      dsimp [b]
      linarith only [hl]
    have h₀ : (-1 : ℝ) ≤ u j - u i := by linarith only [(hu j).1, (hu i).2]
    have h₁ : u j - u i ≤ 1 := by linarith only [(hu j).2, (hu i).1]
    have hη' : 0 ≤ η / 48 := by positivity
    have he₀ := mul_le_mul_of_nonneg_left h₀ hη'
    have he₁ := mul_le_mul_of_nonneg_left h₁ hη'
    unfold boundedRoundReward bonusReward
    change |1 / 8 + z / 8 + b * (if _ then 1 else 0) -
      (1 / 8 + z / 8 + b * (if _ then 1 else 0)) - η / 48 * (u j - u i)| ≤ η / 16
    rw [abs_le]
    split_ifs <;> constructor <;> linarith only [hb₀, hb₁, he₀, he₁, hη]
  · rw [abs_zero]
    positivity

/-- From a deterministic policy on the observed past of the reward tape,
obtain the realized swap-regret lower bound with the exact martingale
error used in Theorem 4.1. The bonus probabilities are fixed in this step. -/
theorem expected_tape_swap_lower {N T : ℕ} (anchor : Fin N) {η : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1) (u : ℕ → Fin N → ℝ)
    (hu : ∀ t < T, ∀ i, u t i ∈ Icc 0 1)
    (pick : (t : ℕ) → RewardTape N t → Fin N) (hp : ∀ t < T, Measurable (pick t)) :
    let I (ω : RewardTape N T) (t : ℕ) : Fin N :=
      if h : t < T then pick t (rewardTapePrefix N h.le ω) else anchor
    let q (ω : RewardTape N T) (t : ℕ) : Fin N → ℝ := Pi.single (I ω t) 1
    let y (ω : RewardTape N T) (t : ℕ) (i : Fin N) : ℝ :=
      if h : t < T then boundedRoundReward η (u t i) i (rewardTapePrefix N (Nat.succ_le_of_lt h) ω).2
      else 0
    η / 48 * (∫ ω, pseudoSwapRegret T (q ω) u ∂rewardTapeLaw N T) -
        N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N))) ≤
      ∫ ω, swapRegret T (y ω) (I ω) ∂rewardTapeLaw N T := by
  classical
  intro I q y
  have hy (t : ℕ) (ht : t < T) (ω : RewardTape N T) (j : Fin N) :
      y ω t j ∈ Icc 0 1 := by
    simpa only [y, dif_pos ht] using
      boundedRoundReward_mem hη.le hη₁ (u t j) j (rewardTapePrefix N (Nat.succ_le_of_lt ht) ω).2
  have hym (t : ℕ) (ht : t < T) (j : Fin N) : Measurable fun ω => y ω t j := by
    simp only [y, dif_pos ht]
    exact ((measurable_boundedRoundReward η (u t j) j).comp
        (measurable_snd : Measurable (Prod.snd : RewardTape N (t + 1) → ℝ × (Fin N → ℝ)))).comp
          (measurable_rewardTapePrefix N (Nat.succ_le_of_lt ht))
  have hIm (t : ℕ) (ht : t < T) : Measurable fun ω => I ω t := by
    simp only [I, dif_pos ht]
    exact (hp t ht).comp (measurable_rewardTapePrefix N ht.le)
  have hq (t : ℕ) (_ht : t < T) (ω : RewardTape N T) : IsProbVec (q ω t) := by
    dsimp [q]
    constructor
    · intro j
      rw [Pi.single_apply]
      split <;> norm_num
    · simp
  have hqm (t : ℕ) (ht : t < T) (j : Fin N) : Measurable fun ω => q ω t j := by
    exact (Measurable.of_discrete (f := fun a : Fin N => (Pi.single a (1 : ℝ) : Fin N → ℝ) j)).comp (hIm t ht)
  let d (i : Fin N) (t : ℕ) (j : Fin N) (ω : RewardTape N T) :=
    (Pi.single (I ω t) (1 : ℝ) : Fin N → ℝ) i * (y ω t j - y ω t i) -
      η / 48 * (q ω t i * (u t j - u t i))
  have he (t : ℕ) (ht : t < T) (i j : Fin N) :
      d i t j = centeredTreeStep η (u t) (pick t) i j ∘ rewardTapePrefix N (Nat.succ_le_of_lt ht) := by
    funext ω
    let pre := rewardTapePrefix N (Nat.succ_le_of_lt ht)
    have hpre : (pre ω).1 = rewardTapePrefix N ht.le ω := by
      have hf : rewardTapePrefix N (Nat.le_succ t) = (Prod.fst : RewardTape N (t + 1) → RewardTape N t) := by
        rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
      have h := congrFun (rewardTapePrefix_comp N (Nat.le_succ t) (Nat.succ_le_of_lt ht)) ω
      rw [hf] at h
      exact h
    simp only [d, q, centeredTreeStep, Function.comp_apply, I, y, dif_pos ht, Pi.single_apply]
    change (if i = pick t (rewardTapePrefix N ht.le ω) then (1 : ℝ) else 0) * _ -
      η / 48 * ((if i = pick t (rewardTapePrefix N ht.le ω) then (1 : ℝ) else 0) * _) =
        (if pick t (pre ω).1 = i then _ else 0)
    rw [hpre]
    by_cases h : pick t (rewardTapePrefix N ht.le ω) = i
    · simp [h]
    · have hn : i ≠ pick t (rewardTapePrefix N ht.le ω) := Ne.symm h
      simp [h, hn]
  refine expected_swapRegret_ge_proxy (rewardTapeLaw N T) (rewardTapeFiltration N T)
    anchor (η / 48) (η / 16) (by positivity) q (fun _ => u) y I hy hym hIm hq
    (fun t ht _ j => hu t ht j) hqm (fun _ _ _ => measurable_const) ?_ ?_ ?_
  · intro t ht i j
    change Measurable[rewardTapeFiltration N T (t + 1)] (d i t j)
    rw [he t ht i j]
    exact measurable_rewardTape_step ht _ (measurable_centeredTreeStep η (u t) (pick t) (hp t ht) i j)
  · intro t ht i j ω
    change |d i t j ω| ≤ η / 16
    rw [he t ht i j]
    exact abs_centeredTreeStep_sharp hη.le (u t) (hu t ht) (pick t) i j _
  · intro t ht i j
    change (rewardTapeLaw N T)[d i t j | rewardTapeFiltration N T t] =ᵐ[rewardTapeLaw N T] 0
    rw [he t ht i j]
    exact condExp_centeredTreeStep ht hη.le hη₁ (u t) (hu t ht) (pick t) (hp t ht) i j

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem measurable_rawTapeHistory {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (r : ℕ) : Measurable (rawTapeHistory η u pick r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    change Measurable (fun p : RewardTape N r × (ℝ × (Fin N → ℝ)) =>
      (rawTapeHistory η u pick r p.1,
        boundedRoundReward η (u r (pick r (rawTapeHistory η u pick r p.1)))
          (pick r (rawTapeHistory η u pick r p.1)) p.2))
    exact (ih.comp measurable_fst).prodMk
      (measurable_select ((hm r).comp (ih.comp measurable_fst)) fun i =>
        (measurable_boundedRoundReward η (u r i) i).comp measurable_snd)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem measurable_tapeDraw {N T : ℕ} (t : ℕ) : Measurable (fun tape : RewardTape N T => tapeDraw tape t) := by
  by_cases ht : t < T
  · simp only [tapeDraw, dif_pos ht]
    exact measurable_snd.comp (measurable_rewardTapePrefix N (Nat.succ_le_of_lt ht))
  · simp only [tapeDraw, dif_neg ht]
    exact measurable_const

theorem measurable_with_fixed_table {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Fintype A] [MeasurableSingletonClass A] {f : A × B → C}
    (hf : ∀ a, Measurable (fun b => f (a, b))) : Measurable f := by
  intro S hS
  have he : f ⁻¹' S = ⋃ a, {a} ×ˢ ((fun b => f (a, b)) ⁻¹' S) := by
    ext ⟨a, b⟩
    simp
  rw [he]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hS)

theorem measurable_treeEnvironmentReward {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (t : ℕ) (i : Fin N) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentReward e active η env t i) := by
  apply measurable_with_fixed_table
  intro table
  exact (measurable_boundedRoundReward η (tableBonuses e active table t i) i).comp (measurable_tapeDraw t)

theorem measurable_treeEnvironmentAction {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) (t : ℕ) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentAction e active η pick anchor env t) := by
  apply measurable_with_fixed_table
  intro table
  by_cases ht : t < T
  · simp only [treeEnvironmentAction, dif_pos ht]
    exact (hm t).comp ((measurable_rawTapeHistory η (tableBonuses e active table) pick hm t).comp
      (measurable_rewardTapePrefix N ht.le))
  · simp only [treeEnvironmentAction, dif_neg ht]
    exact measurable_const

theorem measurable_treeEnvironmentPlay {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) (t : ℕ) (i : Fin N) :
    Measurable (fun env : TreeEnvironment h M N T => treeEnvironmentPlay e active η pick anchor env t i) :=
  (Measurable.of_discrete (f := fun a : Fin N => (Pi.single a (1 : ℝ) : Fin N → ℝ) i)).comp
    (measurable_treeEnvironmentAction e active η pick hm anchor t)

theorem rawTapeHistory_eq_feedbackHistory {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (tape : RewardTape N T) (t : ℕ) (ht : t ≤ T) :
    rawTapeHistory η u pick t (rewardTapePrefix N ht tape) =
      feedbackHistory pick (fun s i => boundedRoundReward η (u s i) i (tapeDraw tape s)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : (rewardTapePrefix N ht tape).1 = rewardTapePrefix N ((Nat.le_succ t).trans ht) tape := by
      have hf : rewardTapePrefix N (Nat.le_succ t) = (Prod.fst : RewardTape N (t + 1) → RewardTape N t) := by
        rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
      have hc := congrFun (rewardTapePrefix_comp N (Nat.le_succ t) ht) tape
      rw [hf] at hc
      exact hc
    have hdraw : tapeDraw tape t = (rewardTapePrefix N ht tape).2 := by
      simp only [tapeDraw, dif_pos (Nat.lt_of_succ_le ht)]
    have hhist := ih ((Nat.le_succ t).trans ht)
    simp only [rawTapeHistory, feedbackHistory, he, hhist, hdraw]
    rfl

theorem integrable_treeEnvironmentBestGain {h M U N T : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor i : Fin N) :
    Integrable (fun env : TreeEnvironment h M N T =>
      bestSwapGain T (treeEnvironmentPlay e active η pick anchor env) (tableBonuses e active env.1) i)
      (treeEnvironmentLaw h M N T) := by
  classical
  let q := treeEnvironmentPlay (T := T) e active η pick anchor
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  have hu (env : TreeEnvironment h M N T) (t : ℕ) (j : Fin N) : u env t j ∈ Icc 0 1 :=
    treeBonusProb_mem _ _ _ _ _
  have hqm (t : ℕ) (k : Fin N) : Measurable (fun env => q env t k) :=
    measurable_treeEnvironmentPlay e active η pick hm anchor t k
  have hum (t : ℕ) (j : Fin N) : Measurable (fun env => u env t j) := by
    apply measurable_with_fixed_table
    intro table
    change Measurable (fun _ : RewardTape N T => tableBonuses e active table t j)
    exact measurable_const
  let _ : Nonempty (Fin N) := ⟨anchor⟩
  unfold bestSwapGain
  apply integrable_finset_max (B := (T : ℝ))
  · intro j
    exact Finset.measurable_sum _ fun t _ => (hqm t i).mul ((hum t j).sub (hum t i))
  · intro j env
    unfold swapGain
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t _ => by
        have hd : |u env t j - u env t i| ≤ 1 := abs_le.mpr
          ⟨by linarith only [(hu env t j).1, (hu env t i).2],
            by linarith only [(hu env t j).2, (hu env t i).1]⟩
        have hq : |q env t i| ≤ 1 := by
          unfold q treeEnvironmentPlay
          rw [Pi.single_apply]
          split <;> norm_num
        rw [abs_mul]
        exact mul_le_one₀ hq (abs_nonneg _) hd
      _ = _ := by simp

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem swapRegret_congr_before {N T : ℕ} {y y' : ℕ → Fin N → ℝ}
    {I I' : ℕ → Fin N}
    (hy : ∀ t < T, ∀ i, y t i = y' t i) (hI : ∀ t < T, I t = I' t) :
    swapRegret T y I = swapRegret T y' I' := by
  unfold swapRegret
  congr 1
  funext f
  exact Finset.sum_congr rfl fun t ht => by
    have ht' := Finset.mem_range.mp ht
    rw [hI t ht', hy t ht', hy t ht']

theorem integrable_swapRegret_of_bounded {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] {N T : ℕ} (y : X → ℕ → Fin N → ℝ) (I : X → ℕ → Fin N)
    (hy : ∀ t < T, ∀ i x, y x t i ∈ Icc 0 1)
    (hym : ∀ t < T, ∀ i, Measurable fun x => y x t i)
    (hIm : ∀ t < T, Measurable fun x => I x t) :
    Integrable (fun x => swapRegret T (y x) (I x)) P := by
  classical
  unfold swapRegret
  apply integrable_finset_max ⟨id, Finset.mem_univ _⟩ _ (B := T)
  · intro f
    exact Finset.measurable_sum _ fun t ht =>
      (measurable_select (hIm t (Finset.mem_range.mp ht)) (fun j => hym t (Finset.mem_range.mp ht) (f j))).sub
        (measurable_select (hIm t (Finset.mem_range.mp ht)) (hym t (Finset.mem_range.mp ht)))
  · intro f x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
        have h₁ := hy t (Finset.mem_range.mp ht) (f (I x t)) x
        have h₂ := hy t (Finset.mem_range.mp ht) (I x t) x
        exact abs_le.mpr ⟨by linarith only [h₁.1, h₂.2], by linarith only [h₁.2, h₂.1]⟩
      _ = _ := by simp

/-- A jointly measurable policy and reward sequence induce measurable
actions and observation histories. -/
theorem measurable_feedbackHistory_of_measurable {S X : Type*}
    [MeasurableSpace S] [MeasurableSpace X] {N : ℕ}
    (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hp : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2))
    (seed : X → S) (hs : Measurable seed) (y : X → ℕ → Fin N → ℝ)
    (hy : ∀ t i, Measurable (fun x => y x t i)) (t : ℕ) :
    Measurable (fun x => feedbackHistory (fun n => pick n (seed x)) (y x) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun x =>
      (feedbackHistory (fun n => pick n (seed x)) (y x) t,
        y x t (pick t (seed x) (feedbackHistory (fun n => pick n (seed x)) (y x) t))))
    apply ih.prodMk
    exact measurable_select ((hp t).comp (hs.prodMk ih)) (hy t)

set_option maxHeartbeats 900000 in
/-- Average the realized regret over the construction. The martingale
bound is used conditionally on the three finite tables. -/
theorem tree_environment_expected_regret {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    η / 48 * ((T : ℝ) / (368 * treeHeight h ^ 5)) -
      N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N))) ≤
      ∫ env, swapRegret T (treeEnvironmentReward e active η env)
        (treeEnvironmentAction e active η pick anchor env) ∂P := by
  classical
  intro T active P
  let C := TreeTables h M T
  let μ := finiteTableLaw C
  let ν := rewardTapeLaw N T
  let q := treeEnvironmentPlay (T := T) e active η pick anchor
  let y := treeEnvironmentReward (T := T) e active η
  let I := treeEnvironmentAction (T := T) e active η pick anchor
  let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
  let G (env : C × RewardTape N T) := pseudoSwapRegret T (q env) (u env)
  let R (env : C × RewardTape N T) := swapRegret T (y env) (I env)
  let err := N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))
  have hG : Integrable G (μ.prod ν) := by
    unfold G
    simp only [pseudoSwapRegret_eq_sum_bestSwapGain]
    exact integrable_finsetSum _ (fun i _ => integrable_treeEnvironmentBestGain e active η pick hm anchor i)
  have hR : Integrable R (μ.prod ν) :=
    integrable_swapRegret_of_bounded (μ.prod ν) y I
      (fun t _ i env => boundedRoundReward_mem hη.le hη₁.le (u env t i) i (tapeDraw env.2 t))
      (fun t _ i => measurable_treeEnvironmentReward e active η t i)
      (fun t _ => measurable_treeEnvironmentAction e active η pick hm anchor t)
  have hpoint (c : C) :
      η / 48 * (∫ tape, G (c, tape) ∂ν) - err ≤ ∫ tape, R (c, tape) ∂ν := by
    let u' := tableBonuses e active c
    let pick' (t : ℕ) (pre : RewardTape N t) := pick t (rawTapeHistory η u' pick t pre)
    have hu' (t : ℕ) (_ht : t < T) (i : Fin N) : u' t i ∈ Icc 0 1 := treeBonusProb_mem _ _ _ _ _
    have hp' (t : ℕ) (_ht : t < T) : Measurable (pick' t) :=
      (hm t).comp (measurable_rawTapeHistory η u' pick hm t)
    have hb := expected_tape_swap_lower anchor hη hη₁.le u' hu' pick' hp'
    let y' (ω : RewardTape N T) (t : ℕ) (i : Fin N) : ℝ :=
      if ht : t < T then boundedRoundReward η (u' t i) i (rewardTapePrefix N (Nat.succ_le_of_lt ht) ω).2
      else 0
    have hy (tape : RewardTape N T) (t : ℕ) (ht : t < T) (i : Fin N) : y' tape t i = y (c, tape) t i := by
      simp only [y', y, treeEnvironmentReward, tapeDraw, dif_pos ht]
      rfl
    have hrewrite (tape : RewardTape N T) :
        swapRegret T (y' tape) (I (c, tape)) = R (c, tape) :=
      swapRegret_congr_before (hy tape) (fun _ _ => rfl)
    change η / 48 * (∫ tape, G (c, tape) ∂ν) - err ≤
      ∫ tape, swapRegret T (y' tape) (I (c, tape)) ∂ν at hb
    simpa only [hrewrite] using hb
  have hs := integral_mono ((hG.integral_prod_left.const_mul (η / 48)).sub (integrable_const err))
    hR.integral_prod_left hpoint
  change (∫ c, η / 48 * (∫ tape, G (c, tape) ∂ν) - err ∂μ) ≤
    ∫ c, (∫ tape, R (c, tape) ∂ν) ∂μ at hs
  rw [integral_sub (hG.integral_prod_left.const_mul (η / 48)) (integrable_const err),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    ← integral_prod G hG, ← integral_prod R hR] at hs
  have hproxy : (T : ℝ) / (368 * treeHeight h ^ 5) ≤ ∫ env, G env ∂μ.prod ν :=
    tree_expected_proxy hh e η hη.le hη₁ pick hm anchor hbudget
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hproxy (by positivity)) _).trans hs

/-- For a randomized learner, the lower bound yields a single fixed choice
of the tables and tape, hence an oblivious deterministic reward sequence. -/
theorem exists_tree_environment {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsProbabilityMeasure P]
    {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    ∃ env : TreeEnvironment h M N T,
      η / 48 * ((T : ℝ) / (368 * treeHeight h ^ 5)) -
        N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N))) ≤
        ∫ s, swapRegret T (treeEnvironmentReward e active η env)
          (treeEnvironmentAction e active η (fun t => pick t s) anchor env) ∂P := by
  intro T active
  let C := TreeEnvironment h M N T
  let μ := treeEnvironmentLaw h M N T
  let y := treeEnvironmentReward (T := T) e active η
  let I (p : C × S) (t : ℕ) := treeEnvironmentAction e active η (fun n => pick n p.2) anchor p.1 t
  have hIm (t : ℕ) (ht : t < T) : Measurable (fun p => I p t) := by
    have hhist := measurable_feedbackHistory_of_measurable pick hm Prod.snd measurable_snd
      (fun p : C × S => y p.1)
      (fun t i => (measurable_treeEnvironmentReward e active η t i).comp measurable_fst) t
    have he : (fun p => I p t) =
        fun p : C × S => pick t p.2 (feedbackHistory (fun n => pick n p.2) (y p.1) t) := by
      funext p
      simp only [I, treeEnvironmentAction, dif_pos ht]
      rw [rawTapeHistory_eq_feedbackHistory]
      rfl
    rw [he]
    exact (hm t).comp (measurable_snd.prodMk hhist)
  let R (p : C × S) := swapRegret T (y p.1) (I p)
  have hR : Integrable R (μ.prod P) :=
    integrable_swapRegret_of_bounded (μ.prod P) (fun p : C × S => y p.1) I
      (fun t _ i p => boundedRoundReward_mem hη.le hη₁.le (tableBonuses e active p.1.1 t i) i (tapeDraw p.1.2 t))
      (fun t _ i => (measurable_treeEnvironmentReward e active η t i).comp measurable_fst) hIm
  refine exists_environment_of_seedwise_lower_bound μ P R hR (fun s => ?_)
  exact tree_environment_expected_regret hh e η hη hη₁ (fun t => pick t s)
    (fun t => (hm t).comp measurable_prodMk_left) anchor hbudget

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem treeBonusScale_pos (h : ℕ) : 0 < treeBonusScale h := by unfold treeBonusScale treeActionBudget treeHeight; positivity

theorem treeBonusScale_lt_one (h : ℕ) : treeBonusScale h < 1 := by
  unfold treeBonusScale
  have hk : (16 : ℝ) ≤ treeActionBudget h := by
    unfold treeActionBudget
    have hpow : 0 < (2 : ℕ) ^ h := by positivity
    exact_mod_cast (show 16 ≤ 16 * 2 ^ h by omega)
  have hh : 1 ≤ treeHeight h := by unfold treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  apply (div_lt_one (by positivity)).mpr
  nlinarith only [hk, hh, mul_nonneg (show 0 ≤ (treeActionBudget h : ℝ) by positivity) (sub_nonneg.mpr hh)]

/-- A hard environment at the dyadic horizon, also allowing extra unnamed
actions in the learner's action space. -/
theorem exists_hard_tree_environment {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsProbabilityMeasure P]
    {K₀ h N U : ℕ} (hh : 0 < h) (hKN : treeActionBudget h ≤ N) (hNK : N ≤ 2 * treeActionBudget h)
    (hK₀ : K₀ ≤ treeActionBudget h)
    (hscale : ∀ h N : ℕ,
      K₀ ≤ treeActionBudget h → treeActionBudget h ≤ N → N ≤ 2 * treeActionBudget h →
      let L := 2 ^ h
      let M : ℕ := 8 * L
      let r := treePeriodLength h
      let T := L * r
      let H := treeHeight h
      let η := treeBonusScale h
      ((L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
        (T : ℝ) / (64 * H)) ∧
      ((N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        η / 48 * ((T : ℝ) / (368 * H ^ 5)) -
          N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))))
    (e : Fin N ≃ TreeAction h (8 * 2 ^ h) U) (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) (anchor : Fin N) :
    let r := treePeriodLength h
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let η := treeBonusScale h
    ∃ env : TreeEnvironment h (8 * 2 ^ h) N T,
      (N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        ∫ s, swapRegret T (treeEnvironmentReward e active η env)
          (treeEnvironmentAction e active η (fun t => pick t s) anchor env) ∂P := by
  intro r T active η
  have _ : Nonempty (Fin (8 * 2 ^ h)) := ⟨⟨0, by positivity⟩⟩
  obtain ⟨hb, hr⟩ := hscale h N hK₀ hKN hNK
  obtain ⟨env, he⟩ := exists_tree_environment (r := r) P hh e η (treeBonusScale_pos h)
    (treeBonusScale_lt_one h) pick hm anchor hb
  exact ⟨env, hr.trans he⟩

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.exists_hard_tree_environment := @CalibeatBandit.exists_hard_tree_environment
