-- Prove2me | solution 1 for ContextualAuctions.PoA.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:36:12.688227+00:00
-- url     : https://prove2.me/submissions/73fa1ce0-99d3-405c-b152-4e9b64222a89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_SecondPrice
import Theorems.Thm_ContextualAuctions_PoA_lemma_13
import Theorems.Thm_ContextualAuctions_PoA_price_le_liquid_value

open MeasureTheory
open ContextualAuctions.PoA

namespace PoA3Aux

variable (M : Model)

lemma meas_val : Measurable (fun q : Buyer M × Context M => val M q.1 q.2) := by
  unfold val; fun_prop

lemma meas_paced {μ : Buyer M → ℝ} (hμ : Measurable μ) :
    Measurable (fun q : Buyer M × Context M => paced M μ q.1 q.2) := by
  unfold paced
  exact (meas_val M).div (measurable_const.add (hμ.comp measurable_fst))

lemma meas_H (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : Measurable μ) :
    Measurable (fun q : Context M × ℝ => H M μ q.1 q.2) := by
  haveI := hM.probG
  unfold H
  have hs : MeasurableSet {z : (Context M × ℝ) × Buyer M | paced M μ z.2 z.1.1 ≤ z.1.2} := by
    apply measurableSet_le
    · exact (meas_paced M hμ).comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    · exact measurable_snd.comp measurable_fst
  have := measurable_measure_prodMk_left (ν := M.G) hs
  exact (this.ennreal_toReal).pow_const _

lemma meas_intH (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : Measurable μ) :
    Measurable (fun q : Context M × ℝ => ∫ s in (M.r q.1)..q.2, H M μ q.1 s) := by
  have hH := meas_H M hM hμ
  have hr := hM.measurableR
  have key : ∀ (a b : Context M × ℝ → ℝ), Measurable a → Measurable b →
      Measurable (fun q : Context M × ℝ => ∫ s in Set.Ioc (a q) (b q), H M μ q.1 s) := by
    intro a b ha hb
    have e : (fun q : Context M × ℝ => ∫ s in Set.Ioc (a q) (b q), H M μ q.1 s) =
        fun q => ∫ s, (if a q < s ∧ s ≤ b q then H M μ q.1 s else 0) := by
      funext q
      rw [← integral_indicator measurableSet_Ioc]
      congr 1; funext s
      simp [Set.indicator, Set.mem_Ioc]
    rw [e]
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right (f := fun q s =>
      if a q < s ∧ s ≤ b q then H M μ q.1 s else 0)
    apply Measurable.stronglyMeasurable
    apply Measurable.ite
    · apply MeasurableSet.inter
      · exact measurableSet_lt (ha.comp measurable_fst) measurable_snd
      · exact measurableSet_le measurable_snd (hb.comp measurable_fst)
    · exact hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact measurable_const
  simp only [intervalIntegral]
  exact (key _ _ (hr.comp measurable_fst) measurable_snd).sub
    (key _ _ measurable_snd (hr.comp measurable_fst))

lemma meas_sigma (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : Measurable μ) :
    Measurable (fun q : Context M × ℝ => sigma M μ q.1 q.2) := by
  have hH := meas_H M hM hμ
  have hI := meas_intH M hM hμ
  have hr := hM.measurableR
  unfold sigma
  apply Measurable.ite
  · exact measurableSet_lt measurable_snd (hr.comp measurable_fst)
  · exact measurable_snd
  apply Measurable.ite
  · exact hH (measurableSet_singleton 0)
  · exact measurable_const
  · exact measurable_snd.sub (hI.div hH)

lemma meas_beta (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : Measurable μ) :
    Measurable (fun q : Buyer M × Context M => beta M μ q.1 q.2) := by
  unfold beta
  exact (meas_sigma M hM hμ).comp (measurable_snd.prodMk (meas_paced M hμ))

lemma meas_xmu (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : Measurable μ) (i : Fin M.n) :
    Measurable (fun q : Context M × Profile M => xmu M μ q.1 q.2 i) := by
  have hb := meas_beta M hM hμ
  have hbj : ∀ j : Fin M.n, Measurable (fun q : Context M × Profile M => beta M μ (q.2 j) q.1) := by
    intro j
    have hm : Measurable (fun q : Context M × Profile M => (q.2 j, q.1)) := by fun_prop
    exact hb.comp hm
  have hset : ∀ j : Fin M.n, MeasurableSet {q : Context M × Profile M |
      ∀ k : Fin M.n, beta M μ (q.2 k) q.1 ≤ beta M μ (q.2 j) q.1} := by
    intro j
    have : {q : Context M × Profile M | ∀ k : Fin M.n, beta M μ (q.2 k) q.1 ≤ beta M μ (q.2 j) q.1}
        = ⋂ k, {q | beta M μ (q.2 k) q.1 ≤ beta M μ (q.2 j) q.1} := by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun k => measurableSet_le (hbj k) (hbj j)
  set c : Context M × Profile M → ℝ := fun q => ∑ j : Fin M.n,
    Set.indicator {q : Context M × Profile M |
      ∀ k : Fin M.n, beta M μ (q.2 k) q.1 ≤ beta M μ (q.2 j) q.1} (fun _ => (1 : ℝ)) q with hc
  have hcm : Measurable c := Finset.measurable_sum _ fun j _ => measurable_const.indicator (hset j)
  have e : (fun q : Context M × Profile M => xmu M μ q.1 q.2 i) =
      Set.indicator {q : Context M × Profile M |
      ∀ k : Fin M.n, beta M μ (q.2 k) q.1 ≤ beta M μ (q.2 i) q.1} (fun q => 1 / c q) := by
    funext q
    simp only [xmu, Set.indicator, hc, Set.mem_setOf_eq, Finset.card_filter]
    push_cast
    rfl
  rw [e]
  exact (measurable_const.div hcm).indicator (hset i)

section Marg

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
  (G : Measure X) [IsProbabilityMeasure G] (F : Measure Y) [IsProbabilityMeasure F]

lemma meas_upd (i : Fin n) : Measurable (fun z : X × (Fin n → X) => Function.update z.2 i z.1) := by
  fun_prop

lemma mp_upd (i : Fin n) :
    MeasurePreserving (fun z : X × (Fin n → X) => Function.update z.2 i z.1)
      (G.prod (Measure.pi fun _ : Fin n => G)) (Measure.pi fun _ : Fin n => G) := by
  refine ⟨meas_upd i, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (meas_upd i) (MeasurableSet.univ_pi hs)]
  have e : (fun z : X × (Fin n → X) => Function.update z.2 i z.1) ⁻¹' (Set.univ.pi s) =
      s i ×ˢ Set.univ.pi (Function.update s i Set.univ) := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j; simp [Function.update_of_ne hj] at this; simp [Function.update_of_ne hj, this]
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h1
      · have := h2 j; simp [Function.update_of_ne hj] at this; simp [Function.update_of_ne hj, this]
  rw [e, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => G (s j)) (Finset.mem_univ i)]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma meas_Phi (i : Fin n) : Measurable (fun z : X × (Y × (Fin n → X)) =>
    (z.2.1, Function.update z.2.2 i z.1)) := by fun_prop

lemma map_Phi (i : Fin n) :
    Measure.map (fun z : X × (Y × (Fin n → X)) => (z.2.1, Function.update z.2.2 i z.1))
      (G.prod (F.prod (Measure.pi fun _ : Fin n => G))) =
      F.prod (Measure.pi fun _ : Fin n => G) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply (meas_Phi i) (hs.prod ht)]
  rw [Measure.prod_apply ((meas_Phi i) (hs.prod ht))]
  have hslice : ∀ a : X, Prod.mk a ⁻¹' ((fun z : X × (Y × (Fin n → X)) =>
      (z.2.1, Function.update z.2.2 i z.1)) ⁻¹' (s ×ˢ t)) =
      s ×ˢ ((fun b : Fin n → X => Function.update b i a) ⁻¹' t) := by
    intro a; ext ⟨y, b⟩; simp
  simp_rw [hslice, Measure.prod_prod]
  rw [lintegral_const_mul _ ?_]
  · congr 1
    have hmp := mp_upd G i
    rw [← hmp.measure_preimage ht.nullMeasurableSet]
    rw [Measure.prod_apply ((meas_upd i) ht)]
    rfl
  · exact measurable_measure_prodMk_left ((meas_upd i) ht)

lemma integral_Phi (i : Fin n) (g : Y × (Fin n → X) → ℝ)
    (hg : Integrable g (F.prod (Measure.pi fun _ : Fin n => G))) :
    Integrable (fun a : X => ∫ p, g (p.1, Function.update p.2 i a)
        ∂(F.prod (Measure.pi fun _ : Fin n => G))) G ∧
    ∫ a, ∫ p, g (p.1, Function.update p.2 i a) ∂(F.prod (Measure.pi fun _ : Fin n => G)) ∂G =
      ∫ p, g p ∂(F.prod (Measure.pi fun _ : Fin n => G)) := by
  have hmap := map_Phi G F i
  have hint : Integrable (g ∘ fun z : X × (Y × (Fin n → X)) =>
      (z.2.1, Function.update z.2.2 i z.1)) (G.prod (F.prod (Measure.pi fun _ : Fin n => G))) := by
    apply Integrable.comp_measurable _ (meas_Phi i)
    rw [hmap]; exact hg
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [show (∫ a, ∫ p, g (p.1, Function.update p.2 i a)
      ∂(F.prod (Measure.pi fun _ : Fin n => G)) ∂G) = _ from (integral_prod _ hint).symm]
  conv_rhs => rw [← hmap]
  rw [integral_map (meas_Phi i).aemeasurable]
  · rfl
  · rw [hmap]; exact hg.aestronglyMeasurable

end Marg

section Dom
variable (M : Model)

lemma meas_Theta : MeasurableSet (Theta M) := by
  have : Theta M = (⋂ i, {θ : Buyer M | 0 < θ.1 i} ∩ {θ | θ.1 i < M.U}) ∩
      ({θ : Buyer M | M.Bmin < θ.2} ∩ {θ | θ.2 < M.U}) := by
    ext θ; simp only [Theta, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, forall_and]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
  · exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  · exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)

lemma ae_Theta (hM : M.Standing) : ∀ᵐ θ ∂M.G, θ ∈ Theta M := by
  rw [ae_iff]
  have := hM.supportedG
  simpa [Set.compl_def] using this

lemma ae_dom (hM : M.Standing) :
    ∀ᵐ p ∂(M.F.prod (Measure.pi fun _ : Fin M.n => M.G)), p.1 ∈ M.A ∧ ∀ j, p.2 j ∈ Theta M := by
  haveI := hM.probG
  haveI := hM.probF
  haveI : ∀ i : Fin M.n, SigmaFinite ((fun _ : Fin M.n => M.G) i) := fun _ => inferInstance
  rw [Filter.eventually_and, ae_all_iff]
  constructor
  · rw [ae_iff]
    have e : {a : Context M × Profile M | ¬ a.1 ∈ M.A} = (M.A)ᶜ ×ˢ Set.univ := by ext; simp
    rw [e, Measure.prod_prod, hM.supportedF, zero_mul]
  · intro j
    rw [ae_iff]
    have e : {a : Context M × Profile M | ¬ a.2 j ∈ Theta M} =
        Set.univ ×ˢ Set.univ.pi (Function.update (fun _ => Set.univ) j (Theta M)ᶜ) := by
      ext ⟨a, b⟩
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi]
      constructor
      · intro h k
        by_cases hk : k = j
        · subst hk; simpa using h
        · simp [Function.update_of_ne hk]
      · intro h; simpa using h j
    rw [e, Measure.prod_prod, Measure.pi_pi]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp [hM.supportedG]

lemma val_bound (hM : M.Standing) : ∃ C : ℝ, ∀ θ ∈ Theta M, ∀ α ∈ M.A,
    0 ≤ val M θ α ∧ val M θ α ≤ C := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hM.boundedA
  refine ⟨M.d * (M.U * R), fun θ hθ α hα => ⟨?_, ?_⟩⟩
  · unfold val
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i).1.le (hM.positiveA hα i).le
  · unfold val
    have : ∀ i ∈ Finset.univ, θ.1 i * α i ≤ M.U * R := by
      intro i _
      have h1 : α i ≤ R := le_trans (le_abs_self _) (le_trans (norm_le_pi_norm α i) (hR α hα))
      exact mul_le_mul (hθ.1 i).2.le h1 (hM.positiveA hα i).le
        (le_trans (hθ.1 i).1.le (hθ.1 i).2.le)
    calc ∑ i, θ.1 i * α i ≤ ∑ _i : Fin M.d, M.U * R := Finset.sum_le_sum this
      _ = M.d * (M.U * R) := by simp

lemma xmu_nonneg (μ : Buyer M → ℝ) (α : Context M) (θs : Profile M) (i : Fin M.n) :
    0 ≤ xmu M μ α θs i := by
  unfold xmu; split_ifs <;> positivity

lemma xmu_sum (hn : 0 < M.n) (μ : Buyer M → ℝ) (α : Context M) (θs : Profile M) :
    ∑ i, xmu M μ α θs i = 1 := by
  classical
  set b : Fin M.n → ℝ := fun j => beta M μ (θs j) α
  set S := Finset.univ.filter fun j : Fin M.n => ∀ k : Fin M.n, b k ≤ b j with hS
  have hne : S.Nonempty := by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ b ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    exact ⟨j, by simp [hS, fun k => hj k (Finset.mem_univ k)]⟩
  have e : ∀ i, xmu M μ α θs i = if i ∈ S then 1 / (S.card : ℝ) else 0 := by
    intro i
    simp only [xmu, hS, Finset.mem_filter, Finset.mem_univ, true_and, b]
  simp_rw [e]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  field_simp

lemma meas_secondPaced {μ : Buyer M → ℝ} (hμ : Measurable μ) :
    Measurable (fun q : Context M × Profile M => secondPaced M μ q.1 q.2) := by
  have hp := meas_paced M hμ
  have hij : ∀ ij : {ij : Fin M.n × Fin M.n // ij.1 ≠ ij.2},
      Measurable (fun q : Context M × Profile M =>
        min (paced M μ (q.2 ij.1.1) q.1) (paced M μ (q.2 ij.1.2) q.1)) := by
    intro ij
    have m1 : Measurable (fun q : Context M × Profile M => (q.2 ij.1.1, q.1)) := by fun_prop
    have m2 : Measurable (fun q : Context M × Profile M => (q.2 ij.1.2, q.1)) := by fun_prop
    exact (hp.comp m1).min (hp.comp m2)
  exact Measurable.iSup hij

lemma secondPaced_bound (hM : M.Standing) {μ : Buyer M → ℝ}
    (hμ0 : ∀ θ ∈ Theta M, 0 ≤ μ θ) {C : ℝ}
    (hC : ∀ θ ∈ Theta M, ∀ α ∈ M.A, 0 ≤ val M θ α ∧ val M θ α ≤ C)
    (α : Context M) (hα : α ∈ M.A) (θs : Profile M) (hθs : ∀ j, θs j ∈ Theta M) :
    0 ≤ secondPaced M μ α θs ∧ secondPaced M μ α θs ≤ C := by
  have hpc : ∀ j, 0 ≤ paced M μ (θs j) α ∧ paced M μ (θs j) α ≤ C := by
    intro j
    obtain ⟨h0, h1⟩ := hC _ (hθs j) α hα
    have hm := hμ0 _ (hθs j)
    unfold paced
    refine ⟨div_nonneg h0 (by linarith), ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hn : 2 ≤ M.n := hM.buyers
  haveI : Nonempty {ij : Fin M.n × Fin M.n // ij.1 ≠ ij.2} :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
  unfold secondPaced
  constructor
  · obtain ij := Classical.arbitrary {ij : Fin M.n × Fin M.n // ij.1 ≠ ij.2}
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove ij)
    exact le_min (hpc _).1 (hpc _).1
  · exact ciSup_le fun ij => le_trans (min_le_left _ _) (hpc _).2

/-- Regularity of an allocation used in the welfare bookkeeping. -/
def GoodAlloc (y : Allocation M) : Prop :=
  (∀ i, Measurable (fun q : Context M × Profile M => y q.1 q.2 i)) ∧
  ∀ α ∈ M.A, ∀ θs : Profile M, (∀ j, θs j ∈ Theta M) →
    (∀ i, 0 ≤ y α θs i) ∧ ∑ i, y α θs i = 1

lemma good_of_isAllocation {x : Allocation M} (hx : IsAllocation M x) : GoodAlloc M x := by
  refine ⟨fun i => ?_, fun α hα θs hθs => hx.2 α hα θs hθs⟩
  have : Measurable (fun q : Context M × Profile M => x q.1 q.2) := hx.1
  exact (measurable_pi_apply i).comp this

lemma good_xmu (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : Measurable μ) : GoodAlloc M (xmu M μ) :=
  ⟨fun i => meas_xmu M hM hμ i, fun α _ θs _ =>
    ⟨fun i => xmu_nonneg M μ α θs i, xmu_sum M (by have := hM.buyers; omega) μ α θs⟩⟩

lemma upd_mem {θs : Profile M} (hθs : ∀ j, θs j ∈ Theta M) (i : Fin M.n) {θ : Buyer M}
    (hθ : θ ∈ Theta M) : ∀ j, Function.update θs i θ j ∈ Theta M := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hθ
  · rw [Function.update_of_ne hj]; exact hθs j

lemma lw_integrable (hM : M.Standing) {y : Allocation M} (hy : GoodAlloc M y) (i : Fin M.n) :
    Integrable (fun θ : Buyer M => min (ContextualAuctions.PoA.inner M y i θ) θ.2) M.G := by
  haveI := hM.probG
  haveI := hM.probF
  haveI : ∀ i : Fin M.n, SigmaFinite ((fun _ : Fin M.n => M.G) i) := fun _ => inferInstance
  obtain ⟨C, hC⟩ := val_bound M hM
  have hmeas : Measurable (fun θ : Buyer M => ContextualAuctions.PoA.inner M y i θ) := by
    unfold ContextualAuctions.PoA.inner
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right (f := fun (θ : Buyer M) (p : Context M × Profile M) =>
      val M θ p.1 * y p.1 (Function.update p.2 i θ) i)
    apply Measurable.stronglyMeasurable
    have h1 : Measurable (fun z : Buyer M × (Context M × Profile M) => val M z.1 z.2.1) :=
      (meas_val M).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable (fun z : Buyer M × (Context M × Profile M) =>
        y z.2.1 (Function.update z.2.2 i z.1) i) :=
      (hy.1 i).comp (meas_Phi (Y := Context M) i)
    exact h1.mul h2
  refine Integrable.of_bound (hmeas.min (by fun_prop)).aestronglyMeasurable M.U ?_
  filter_upwards [ae_Theta M hM] with θ hθ
  have h0 : 0 ≤ ContextualAuctions.PoA.inner M y i θ := by
    unfold ContextualAuctions.PoA.inner
    apply integral_nonneg_of_ae
    filter_upwards [ae_dom M hM] with p hp
    have hu := upd_mem M hp.2 i hθ
    exact mul_nonneg (hC θ hθ p.1 hp.1).1 ((hy.2 p.1 hp.1 _ hu).1 i)
  have hB : 0 < θ.2 := lt_trans hM.budget_pos hθ.2.1
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min h0 hB.le)]
  exact le_trans (min_le_right _ _) hθ.2.2.le

lemma price_integrable (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : IsPacing M μ)
    {y : Allocation M} (hy : GoodAlloc M y) (i : Fin M.n) :
    Integrable (fun q : Context M × Profile M => secondPaced M μ q.1 q.2 * y q.1 q.2 i)
      (M.F.prod (Measure.pi fun _ : Fin M.n => M.G)) := by
  haveI := hM.probG
  haveI := hM.probF
  haveI : ∀ i : Fin M.n, SigmaFinite ((fun _ : Fin M.n => M.G) i) := fun _ => inferInstance
  obtain ⟨C, hC⟩ := val_bound M hM
  refine Integrable.of_bound (((meas_secondPaced M hμ.1).mul (hy.1 i)).aestronglyMeasurable) C ?_
  filter_upwards [ae_dom M hM] with p hp
  obtain ⟨s0, s1⟩ := secondPaced_bound M hM hμ.2 hC p.1 hp.1 p.2 hp.2
  obtain ⟨y0, y1⟩ := hy.2 p.1 hp.1 p.2 hp.2
  have hyle : y p.1 p.2 i ≤ 1 := by
    rw [← y1]
    exact Finset.single_le_sum (fun j _ => y0 j) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg s0 (y0 i))]
  calc secondPaced M μ p.1 p.2 * y p.1 p.2 i ≤ C * 1 :=
        mul_le_mul s1 hyle (y0 i) (le_trans s0 s1)
    _ = C := mul_one C

lemma price_sum (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : IsPacing M μ)
    {y : Allocation M} (hy : GoodAlloc M y) :
    (∀ i, Integrable (fun θ => interimPrice M μ y i θ) M.G) ∧
    ∑ i, ∫ θ, interimPrice M μ y i θ ∂M.G =
      ∫ q, secondPaced M μ q.1 q.2 ∂(M.F.prod (Measure.pi fun _ : Fin M.n => M.G)) := by
  haveI := hM.probG
  haveI := hM.probF
  haveI : ∀ i : Fin M.n, SigmaFinite ((fun _ : Fin M.n => M.G) i) := fun _ => inferInstance
  have key := fun i => integral_Phi M.G M.F i _ (price_integrable M hM hμ hy i)
  refine ⟨fun i => (key i).1, ?_⟩
  have e : ∀ i, ∫ θ, interimPrice M μ y i θ ∂M.G =
      ∫ q, secondPaced M μ q.1 q.2 * y q.1 q.2 i ∂(M.F.prod (Measure.pi fun _ : Fin M.n => M.G)) :=
    fun i => (key i).2
  simp_rw [e]
  rw [← integral_finset_sum _ (fun i _ => price_integrable M hM hμ hy i)]
  apply integral_congr_ae
  filter_upwards [ae_dom M hM] with p hp
  rw [← Finset.mul_sum, (hy.2 p.1 hp.1 p.2 hp.2).2, mul_one]

lemma assemble (hM : M.Standing) {μ : Buyer M → ℝ} (hμ : IsPacing M μ)
    {x : Allocation M} (hx : IsAllocation M x)
    (h13 : ∀ i : Fin M.n, ∀ᵐ θi ∂M.G,
      min (ContextualAuctions.PoA.inner M x i θi) θi.2 - interimPrice M μ x i θi ≤
        min (ContextualAuctions.PoA.inner M (xmu M μ) i θi) θi.2)
    (hpb : ∀ i : Fin M.n, ∀ᵐ θi ∂M.G,
      interimPrice M μ (xmu M μ) i θi ≤
        min (ContextualAuctions.PoA.inner M (xmu M μ) i θi) θi.2) :
    LW M x / 2 ≤ LW M (xmu M μ) := by
  have gx := good_of_isAllocation M hx
  have gm := good_xmu M hM hμ.1
  obtain ⟨cx, sx⟩ := price_sum M hM hμ gx
  obtain ⟨cm, sm⟩ := price_sum M hM hμ gm
  have ax := lw_integrable M hM gx
  have am := lw_integrable M hM gm
  set P := ∫ q, secondPaced M μ q.1 q.2 ∂(M.F.prod (Measure.pi fun _ : Fin M.n => M.G))
  have i1 : ∀ i, (∫ θ, min (ContextualAuctions.PoA.inner M x i θ) θ.2 ∂M.G) -
      ∫ θ, interimPrice M μ x i θ ∂M.G ≤
      ∫ θ, min (ContextualAuctions.PoA.inner M (xmu M μ) i θ) θ.2 ∂M.G := by
    intro i
    rw [← integral_sub (ax i) (cx i)]
    exact integral_mono_ae ((ax i).sub (cx i)) (am i) (h13 i)
  have i2 : ∀ i, ∫ θ, interimPrice M μ (xmu M μ) i θ ∂M.G ≤
      ∫ θ, min (ContextualAuctions.PoA.inner M (xmu M μ) i θ) θ.2 ∂M.G :=
    fun i => integral_mono_ae (cm i) (am i) (hpb i)
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => i1 i
  have s2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => i2 i
  rw [Finset.sum_sub_distrib, sx] at s1
  rw [sm] at s2
  unfold LW
  linarith

end Dom

end PoA3Aux

theorem solution (M : ContextualAuctions.PoA.Model) (hM : M.Standing)
    (hr : ∀ α ∈ M.A, M.r α = 0)
    (μ : ContextualAuctions.PoA.Buyer M → ℝ) (hμ : μ ∈ ContextualAuctions.PoA.X0 M)
    (hfix : μ ∈ ContextualAuctions.PoA.C0star M μ)
    (x : ContextualAuctions.PoA.Allocation M) (hx : ContextualAuctions.PoA.IsAllocation M x) :
    ContextualAuctions.PoA.LW M x / 2 ≤
      ContextualAuctions.PoA.LW M (ContextualAuctions.PoA.xmu M μ) :=
  PoA3Aux.assemble M hM hμ.1.1 hx
    (fun i => ContextualAuctions.PoA.lemma_13 M hM hr μ hμ hfix x hx i)
    (fun i => ContextualAuctions.PoA.price_le_liquid_value M hM hr μ hμ hfix i)
