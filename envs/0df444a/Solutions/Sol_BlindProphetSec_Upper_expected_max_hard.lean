-- Prove2me | solution 1 for BlindProphetSec.Upper.expected_max_hard
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:26:53.329133+00:00
-- url     : https://prove2.me/submissions/b931773f-5d73-4448-9655-992b04ce674f

import Mathlib
import Definitions.Def_BlindProphetSec_Upper_Setting

open MeasureTheory Filter Topology

open BlindProphetSec.Upper

namespace BPS2Aux

/-- Single-coordinate independence for a product of probability measures. -/
lemma lintegral_mul_indicator_coord {N : ℕ} (μ : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin N) (f : (Fin N → ℝ) → ENNReal)
    (hf : Measurable f) (hfi : ∀ x y, f (Function.update x i y) = f x)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ v, f v * S.indicator 1 (v i) ∂(Measure.pi μ) = μ i S * ∫⁻ v, f v ∂(Measure.pi μ) := by
  classical
  have hU : (Finset.univ : Finset (Fin N)) = insert i (Finset.univ.erase i) := by
    simp
  have hmeas : Measurable (fun v : Fin N → ℝ => f v * S.indicator 1 (v i)) :=
    hf.mul ((measurable_one.indicator hS).comp (measurable_pi_apply i))
  rw [lintegral_eq_lmarginal_univ (0 : Fin N → ℝ), lintegral_eq_lmarginal_univ (0 : Fin N → ℝ),
    hU, lmarginal_insert' _ hmeas (Finset.notMem_erase i _),
    lmarginal_insert' _ hf (Finset.notMem_erase i _)]
  have h1 : (fun x : Fin N → ℝ => ∫⁻ y, f (Function.update x i y) *
      S.indicator 1 (Function.update x i y i) ∂μ i) = fun x => f x * μ i S := by
    funext x
    simp only [hfi, Function.update_self]
    rw [lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS]
  have h2 : (fun x : Fin N → ℝ => ∫⁻ y, f (Function.update x i y) ∂μ i) = f := by
    funext x
    simp [hfi]
  rw [h1, h2]
  simp only [lmarginal]
  exact (lintegral_mul_const (μ i S) (hf.comp measurable_updateFinset)).trans (mul_comm _ _)

lemma val_lt_of_ne_last {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : i.val < n := by
  have := Fin.lt_last_iff_ne_last.mpr hi
  exact this

lemma hard_prob {n : ℕ} (hn : 1 ≤ n) (a : ℝ) (i : Fin (n + 1)) :
    IsProbabilityMeasure (hardLaw n a i) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  unfold hardLaw
  split_ifs
  · constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
    simp
  · infer_instance

lemma hard_singleton {n : ℕ} (hn : 1 ≤ n) (a : ℝ) (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    hardLaw n a i {(n : ℝ)} = ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (0 : ℝ) ∉ ({(n : ℝ)} : Set ℝ) := by
    simp only [Set.mem_singleton_iff]; intro h; linarith
  unfold hardLaw
  rw [if_pos (val_lt_of_ne_last i hi)]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [Set.indicator_of_mem (Set.mem_singleton _), Set.indicator_of_notMem hne]
  simp

lemma hard_compl_singleton {n : ℕ} (hn : 1 ≤ n) (a : ℝ) (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    hardLaw n a i ({(n : ℝ)}ᶜ) = ENNReal.ofReal (1 - 1 / (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (0 : ℝ) ∈ ({(n : ℝ)}ᶜ : Set ℝ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; intro h; linarith
  unfold hardLaw
  rw [if_pos (val_lt_of_ne_last i hi)]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _).compl,
    Measure.dirac_apply' _ (measurableSet_singleton _).compl]
  rw [Set.indicator_of_notMem (by simp), Set.indicator_of_mem hne]
  simp

lemma hard_ae_coord {n : ℕ} (a : ℝ) (i : Fin (n + 1)) :
    ∀ᵐ x ∂(hardLaw n a i), (i = Fin.last n → x = a) ∧ (i ≠ Fin.last n → x = 0 ∨ x = n) := by
  unfold hardLaw
  split_ifs with h
  · have hne : i ≠ Fin.last n := by
      intro e; subst e; simp at h
    rw [ae_iff]
    have hset : {x : ℝ | ¬((i = Fin.last n → x = a) ∧ (i ≠ Fin.last n → x = 0 ∨ x = n))}
        ⊆ ({(n : ℝ), 0} : Set ℝ)ᶜ := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro hx2; apply hx
      exact ⟨fun e => absurd e hne, fun _ => hx2.elim Or.inr Or.inl⟩
    refine measure_mono_null hset ?_
    have hm : MeasurableSet (({(n : ℝ), 0} : Set ℝ)ᶜ) :=
      (Set.toFinite _).measurableSet.compl
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ hm, Measure.dirac_apply' _ hm]
    simp
  · have he : i = Fin.last n := by
      ext; have := i.isLt; simp at h ⊢; omega
    rw [ae_iff]
    have hset : {x : ℝ | ¬((i = Fin.last n → x = a) ∧ (i ≠ Fin.last n → x = 0 ∨ x = n))}
        ⊆ ({a} : Set ℝ)ᶜ := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx2; apply hx
      exact ⟨fun _ => hx2, fun h' => absurd he h'⟩
    refine measure_mono_null hset ?_
    rw [Measure.dirac_apply' _ (measurableSet_singleton a).compl]
    simp

lemma hard_ae_pi {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    ∀ᵐ v ∂(Measure.pi (hardLaw n a)), ∀ i : Fin (n + 1),
      (i = Fin.last n → v i = a) ∧ (i ≠ Fin.last n → v i = 0 ∨ v i = (n : ℝ)) := by
  have : ∀ i, IsProbabilityMeasure (hardLaw n a i) := hard_prob hn a
  rw [ae_all_iff]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := hardLaw n a) (i := i)).eventually (hard_ae_coord a i)

instance unif_prob : IsProbabilityMeasure BlindProphetSec.Blind.unif01 := by
  constructor
  simp [BlindProphetSec.Blind.unif01]

lemma lintegral_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite ν] [IsProbabilityMeasure ν] (f : α → ENNReal) (hf : Measurable f) :
    ∫⁻ p, f p.1 ∂(μ.prod ν) = ∫⁻ x, f x ∂μ := by
  rw [lintegral_prod (fun p : α × β => f p.1) (hf.comp measurable_fst).aemeasurable]
  simp

lemma measurable_history {N : ℕ} (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    Measurable (fun v : Fin N → ℝ => history v σ k) := by
  unfold history
  exact measurable_pi_lambda _ (fun l => measurable_const.prodMk (measurable_pi_apply _))

lemma history_update {N : ℕ} (σ : Equiv.Perm (Fin N)) (k l : Fin N) (hkl : k < l)
    (v : Fin N → ℝ) (y : ℝ) : history (Function.update v (σ l) y) σ k = history v σ k := by
  funext l'
  simp only [history]
  congr 1
  apply Function.update_of_ne
  intro e
  have := σ.injective e
  have h1 : l'.val < k.val + 1 := l'.isLt
  rw [Fin.ext_iff] at this
  simp at this
  have : l.val ≤ k.val := by omega
  exact absurd hkl (not_lt.mpr (Fin.le_iff_val_le_val.mpr this))

lemma mem_stopSet {N : ℕ} (s : Strategy N) (v : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (ω : ℝ)
    (j : Fin N) : j ∈ stopSet s v σ ω ↔ s.stop j (history v σ j) ω = true := by
  simp [stopSet]

/-- Pointwise bound on the reward. -/
lemma reward_le {n : ℕ} (a : ℝ) (s : Strategy (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (v : Fin (n + 1) → ℝ) (ω : ℝ)
    (hv : ∀ i : Fin (n + 1), (i = Fin.last n → v i = a) ∧ (i ≠ Fin.last n → v i = 0 ∨ v i = n)) :
    ENNReal.ofReal (reward s v σ ω) ≤
      (∑ l ∈ Finset.Iio (σ.symm (Fin.last n)),
          ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l))) +
        ENNReal.ofReal a *
          (if s.stop (σ.symm (Fin.last n)) (history v σ (σ.symm (Fin.last n))) ω then 1 else 0) +
        ∑ l ∈ Finset.Ioi (σ.symm (Fin.last n)),
          ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l)) *
            (if s.stop (σ.symm (Fin.last n)) (history v σ (σ.symm (Fin.last n))) ω then 0 else 1) := by
  set k := σ.symm (Fin.last n) with hkdef
  have hk : σ k = Fin.last n := by simp [k]
  unfold reward
  by_cases hne : (stopSet s v σ ω).Nonempty
  swap
  · rw [dif_neg hne]; simp
  rw [dif_pos hne]
  set T := (stopSet s v σ ω).min' hne with hTdef
  have hT : T ∈ stopSet s v σ ω := Finset.min'_mem _ _
  have hTmin : ∀ j ∈ stopSet s v σ ω, T ≤ j := fun j hj => Finset.min'_le _ _ hj
  have hTk : T ≠ k → σ T ≠ Fin.last n := by
    intro h e; apply h; rw [← hk] at e; exact σ.injective e
  rcases lt_trichotomy T k with h | h | h
  · rcases (hv (σ T)).2 (hTk h.ne) with h0 | h0
    · rw [h0]; simp
    · have h1 : ENNReal.ofReal (v (σ T)) =
          ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ T)) := by
        rw [h0]; simp
      rw [h1]
      refine le_trans ?_ (le_add_right (le_add_right le_rfl))
      exact Finset.single_le_sum
        (f := fun l => ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l)))
        (fun _ _ => bot_le) (Finset.mem_Iio.2 h)
  · have hD : s.stop k (history v σ k) ω = true := by
      rw [← h]; exact (mem_stopSet _ _ _ _ _).1 hT
    rw [h, hk, (hv (Fin.last n)).1 rfl, hD]
    refine le_trans ?_ (le_add_right (le_add_left le_rfl))
    simp
  · have hD : s.stop k (history v σ k) ω = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      have := hTmin k ((mem_stopSet _ _ _ _ _).2 hc)
      exact absurd h (not_lt.mpr this)
    rcases (hv (σ T)).2 (hTk h.ne') with h0 | h0
    · rw [h0]; simp
    · have h1 : ENNReal.ofReal (v (σ T)) =
          ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ T)) *
            (if s.stop k (history v σ k) ω then 0 else 1) := by
        rw [h0, hD]; simp
      rw [h1]
      refine le_trans ?_ (le_add_left le_rfl)
      exact Finset.single_le_sum
        (f := fun l => ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l)) *
            (if s.stop k (history v σ k) ω then 0 else 1))
        (fun _ _ => bot_le) (Finset.mem_Ioi.2 h)

lemma lintegral_indicator_coord {N : ℕ} (μ : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin N) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ v, S.indicator 1 (v i) ∂(Measure.pi μ) = μ i S := by
  have := lintegral_mul_indicator_coord μ i (fun _ => 1) measurable_const (fun _ _ => rfl) S hS
  simpa using this

lemma per_sigma {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (s : Strategy (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    ∫⁻ p, ENNReal.ofReal (reward s p.1 σ p.2)
        ∂((Measure.pi (hardLaw n a)).prod BlindProphetSec.Blind.unif01) ≤
      ENNReal.ofReal (((σ.symm (Fin.last n)).val : ℝ) / n +
        max a (((n : ℝ) - (σ.symm (Fin.last n)).val) / n)) := by
  have hprob : ∀ i, IsProbabilityMeasure (hardLaw n a i) := hard_prob hn a
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set k := σ.symm (Fin.last n) with hkdef
  have hk : σ k = Fin.last n := by simp [k]
  set P := (Measure.pi (hardLaw n a)).prod BlindProphetSec.Blind.unif01 with hP
  have hind : Measurable (({(n : ℝ)} : Set ℝ).indicator (1 : ℝ → ENNReal)) :=
    measurable_one.indicator (measurableSet_singleton _)
  have hmi : ∀ i : Fin (n + 1), Measurable (fun v : Fin (n + 1) → ℝ =>
      ({(n : ℝ)} : Set ℝ).indicator (1 : ℝ → ENNReal) (v i)) :=
    fun i => hind.comp (measurable_pi_apply i)
  have hB : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => s.stop k (history p.1 σ k) p.2) :=
    (s.measurable_stop k).comp
      (((measurable_history σ k).comp measurable_fst).prodMk measurable_snd)
  have hDm : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      if s.stop k (history p.1 σ k) p.2 then (1 : ENNReal) else 0) :=
    (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ENNReal) else 0)).comp hB
  have hDn : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1) :=
    (Measurable.of_discrete (f := fun b : Bool => if b then (0 : ENNReal) else 1)).comp hB
  have hae := (Measure.quasiMeasurePreserving_fst (μ := Measure.pi (hardLaw n a))
    (ν := BlindProphetSec.Blind.unif01)).ae (hard_ae_pi hn a)
  have hcoord : ∀ l : Fin (n + 1), l ≠ k →
      hardLaw n a (σ l) {(n : ℝ)} = ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    intro l hl
    apply hard_singleton hn a
    intro e; apply hl; rw [← hk] at e; exact σ.injective e
  -- the three pieces
  have hT1 : ∀ l ∈ Finset.Iio k, ∫⁻ p, ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l)) ∂P
      = ENNReal.ofReal n * ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    intro l hl
    rw [hP, lintegral_fst _ _ (fun v : Fin (n + 1) → ℝ =>
      ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l)))
      (measurable_const.mul (hmi _)),
      lintegral_const_mul _ (hmi _),
      lintegral_indicator_coord _ _ _ (measurableSet_singleton _),
      hcoord l (ne_of_lt (Finset.mem_Iio.1 hl))]
  have hT3 : ∀ l ∈ Finset.Ioi k, ∫⁻ p, ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l)) *
      (if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1) ∂P
      = ENNReal.ofReal n * ENNReal.ofReal (1 / (n : ℝ) ^ 2) *
        ∫⁻ p, (if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1) ∂P := by
    intro l hl
    have hl' : k < l := Finset.mem_Ioi.1 hl
    have hm3 : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => ENNReal.ofReal n *
        ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l)) *
        (if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1)) :=
      (measurable_const.mul ((hmi _).comp measurable_fst)).mul hDn
    rw [hP, lintegral_prod _ hm3.aemeasurable, lintegral_prod _ hDn.aemeasurable]
    have hG : Measurable (fun v : Fin (n + 1) → ℝ => ∫⁻ ω, (if s.stop k (history v σ k) ω
        then (0 : ENNReal) else 1) ∂BlindProphetSec.Blind.unif01) :=
      hDn.lintegral_prod_right'
    have hinner : ∀ v : Fin (n + 1) → ℝ, ∫⁻ ω, ENNReal.ofReal n *
        ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l)) *
        (if s.stop k (history v σ k) ω then (0 : ENNReal) else 1) ∂BlindProphetSec.Blind.unif01
        = ENNReal.ofReal n * ((∫⁻ ω, (if s.stop k (history v σ k) ω
        then (0 : ENNReal) else 1) ∂BlindProphetSec.Blind.unif01) *
        ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l))) := by
      intro v
      have hm : Measurable (fun ω : ℝ => if s.stop k (history v σ k) ω then (0 : ENNReal) else 1) :=
        hDn.comp measurable_prodMk_left
      rw [lintegral_const_mul _ hm]
      ring
    simp_rw [hinner]
    have hm4 : Measurable (fun v : Fin (n + 1) → ℝ => (∫⁻ ω, (if s.stop k (history v σ k) ω
        then (0 : ENNReal) else 1) ∂BlindProphetSec.Blind.unif01) *
        ({(n : ℝ)} : Set ℝ).indicator 1 (v (σ l))) := hG.mul (hmi _)
    rw [lintegral_const_mul _ hm4,
      lintegral_mul_indicator_coord _ _ _ hG _ _ (measurableSet_singleton _),
      hcoord l (ne_of_gt hl')]
    · ring
    · intro x y
      simp only [history_update σ k l hl' x y]
  have hXY : ∫⁻ p, (if s.stop k (history p.1 σ k) p.2 then (1 : ENNReal) else 0) ∂P +
      ∫⁻ p, (if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1) ∂P = 1 := by
    rw [← lintegral_add_left hDm]
    have : ∀ p : (Fin (n + 1) → ℝ) × ℝ, ((if s.stop k (history p.1 σ k) p.2 then (1 : ENNReal) else 0) +
      if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1) = 1 := by
      intro p; split_ifs <;> simp
    simp_rw [this]
    simp [hP]
  have hm1 : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => ∑ l ∈ Finset.Iio k,
      ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l))) :=
    Finset.measurable_sum _ (fun l _ => measurable_const.mul ((hmi _).comp measurable_fst))
  have hm2 : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => ENNReal.ofReal a *
      (if s.stop k (history p.1 σ k) p.2 then (1 : ENNReal) else 0)) :=
    measurable_const.mul hDm
  have hm12 : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ => (∑ l ∈ Finset.Iio k,
      ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l))) + ENNReal.ofReal a *
      (if s.stop k (history p.1 σ k) p.2 then (1 : ENNReal) else 0)) := hm1.add hm2
  have hm1l : ∀ l ∈ Finset.Iio k, Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l))) :=
    fun l _ => measurable_const.mul ((hmi _).comp measurable_fst)
  have hm3l : ∀ l ∈ Finset.Ioi k, Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l)) *
        (if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1)) :=
    fun l _ => (measurable_const.mul ((hmi _).comp measurable_fst)).mul hDn
  set X := ∫⁻ p, (if s.stop k (history p.1 σ k) p.2 then (1 : ENNReal) else 0) ∂P
  set Y := ∫⁻ p, (if s.stop k (history p.1 σ k) p.2 then (0 : ENNReal) else 1) ∂P
  have hkn : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  have e1 : ENNReal.ofReal n * ENNReal.ofReal (1 / (n : ℝ) ^ 2) = ENNReal.ofReal (1 / n) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
  have e2 : ((k.val : ℕ) : ENNReal) * ENNReal.ofReal (1 / n) = ENNReal.ofReal ((k.val : ℝ) / n) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have e3 : ((n + 1 - 1 - k.val : ℕ) : ENNReal) * ENNReal.ofReal (1 / n) =
      ENNReal.ofReal (((n : ℝ) - k.val) / n) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]; congr 1
    rw [show n + 1 - 1 - k.val = n - k.val by omega, Nat.cast_sub hkn]; ring
  have hM1 : 0 ≤ max a (((n : ℝ) - k.val) / n) := le_trans ha0 (le_max_left _ _)
  calc ∫⁻ p, ENNReal.ofReal (reward s p.1 σ p.2) ∂P
      ≤ ∫⁻ p, ((∑ l ∈ Finset.Iio k,
          ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l))) +
        ENNReal.ofReal a * (if s.stop k (history p.1 σ k) p.2 then 1 else 0) +
        ∑ l ∈ Finset.Ioi k,
          ENNReal.ofReal n * ({(n : ℝ)} : Set ℝ).indicator 1 (p.1 (σ l)) *
            (if s.stop k (history p.1 σ k) p.2 then 0 else 1)) ∂P :=
        lintegral_mono_ae (hae.mono fun p hp => reward_le a s σ p.1 p.2 hp)
    _ = (∑ l ∈ Finset.Iio k, ENNReal.ofReal n * ENNReal.ofReal (1 / (n : ℝ) ^ 2)) +
        ENNReal.ofReal a * X +
        ∑ l ∈ Finset.Ioi k, ENNReal.ofReal n * ENNReal.ofReal (1 / (n : ℝ) ^ 2) * Y := by
        rw [lintegral_add_left hm12, lintegral_add_left hm1,
          lintegral_finset_sum _ hm1l, lintegral_finset_sum _ hm3l,
          lintegral_const_mul _ hDm, Finset.sum_congr rfl hT1, Finset.sum_congr rfl hT3]
    _ = ENNReal.ofReal ((k.val : ℝ) / n) + (ENNReal.ofReal a * X +
        ENNReal.ofReal (((n : ℝ) - k.val) / n) * Y) := by
        rw [Finset.sum_const, Finset.sum_const, Fin.card_Iio, Fin.card_Ioi, nsmul_eq_mul,
          nsmul_eq_mul, e1, e2, ← mul_assoc, e3, add_assoc]
    _ ≤ ENNReal.ofReal ((k.val : ℝ) / n) + (ENNReal.ofReal (max a (((n : ℝ) - k.val) / n)) * X +
        ENNReal.ofReal (max a (((n : ℝ) - k.val) / n)) * Y) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = ENNReal.ofReal (((σ.symm (Fin.last n)).val : ℝ) / n +
        max a (((n : ℝ) - (σ.symm (Fin.last n)).val) / n)) := by
        rw [← mul_add, hXY, mul_one, ENNReal.ofReal_add (by positivity) hM1]

lemma sum_perm_symm {N : ℕ} (g : Fin N → ℝ) (x : Fin N) :
    (N : ℝ) * ∑ σ : Equiv.Perm (Fin N), g (σ.symm x) = (N.factorial : ℝ) * ∑ i, g i := by
  classical
  have hy : ∀ y : Fin N, ∑ σ : Equiv.Perm (Fin N), g (σ.symm x) =
      ∑ σ : Equiv.Perm (Fin N), g (σ.symm y) := by
    intro y
    rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap x y))]
    apply Finset.sum_congr rfl
    intro τ _
    simp [Equiv.Perm.mul_def]
  calc (N : ℝ) * ∑ σ : Equiv.Perm (Fin N), g (σ.symm x)
      = ∑ y : Fin N, ∑ σ : Equiv.Perm (Fin N), g (σ.symm y) := by
        rw [Finset.sum_congr rfl (fun y _ => (hy y).symm)]; simp
    _ = ∑ σ : Equiv.Perm (Fin N), ∑ i, g i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro σ _
        exact Equiv.sum_comp σ.symm g
    _ = (N.factorial : ℝ) * ∑ i, g i := by
        simp [Fintype.card_perm]

lemma telescope_step {a x h : ℝ} (hh : 0 ≤ h) :
    max a x * h ≤ (if x + h ≤ a then a * (x + h) else ((x + h) ^ 2 + a ^ 2) / 2) -
      (if x ≤ a then a * x else (x ^ 2 + a ^ 2) / 2) := by
  split_ifs with h1 h2 h2
  · rw [max_eq_left h2]; ring_nf; rfl
  · linarith
  · rw [max_eq_left h2]; nlinarith [sq_nonneg (x + h - a)]
  · push_neg at h2
    rw [max_eq_right h2.le]; nlinarith

lemma sum_max_le {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∑ k ∈ Finset.range (n + 1), max a ((k : ℝ) / n) ≤
      n * ((((n : ℝ) + 1) / n) ^ 2 + a ^ 2) / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let F : ℝ → ℝ := fun x => if x ≤ a then a * x else (x ^ 2 + a ^ 2) / 2
  have hstep : ∀ k ∈ Finset.range (n + 1), max a ((k : ℝ) / n) * (1 / n) ≤
      F (((k + 1 : ℕ) : ℝ) / n) - F ((k : ℝ) / n) := by
    intro k _
    have := telescope_step (a := a) (x := (k : ℝ) / n) (h := 1 / n) (by positivity)
    simp only [F]
    have e : ((k + 1 : ℕ) : ℝ) / n = (k : ℝ) / n + 1 / n := by push_cast; ring
    rw [e]; exact this
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub (fun k => F ((k : ℝ) / n)), ← Finset.sum_mul] at hsum
  have hF0 : F (((0 : ℕ) : ℝ) / n) = 0 := by simp [F, ha0]
  have hF1 : F (((n + 1 : ℕ) : ℝ) / n) = ((((n : ℝ) + 1) / n) ^ 2 + a ^ 2) / 2 := by
    have : ¬ (((n + 1 : ℕ) : ℝ) / n ≤ a) := by
      rw [not_le, lt_div_iff₀ hn']; push_cast; nlinarith
    simp only [F, if_neg this]; push_cast; ring
  rw [hF0, hF1, sub_zero] at hsum
  have := mul_le_mul_of_nonneg_left hsum hn'.le
  rw [show (n : ℝ) * ((∑ k ∈ Finset.range (n + 1), max a ((k : ℝ) / n)) * (1 / n)) =
    ∑ k ∈ Finset.range (n + 1), max a ((k : ℝ) / n) by field_simp] at this
  linarith

lemma sum_bound {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∑ i : Fin (n + 1), (((i.val : ℝ)) / n + max a (((n : ℝ) - i.val) / n)) ≤
      ((n : ℝ) + 1) / 2 + n * ((((n : ℝ) + 1) / n) ^ 2 + a ^ 2) / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ)) / n + max a (((n : ℝ) - k) / n)) (n + 1),
    Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.range (n + 1), ((k : ℝ)) / n = ((n : ℝ) + 1) / 2 := by
    rw [← Finset.sum_div]
    have := Finset.sum_range_id_mul_two (n + 1)
    have hnat : (∑ k ∈ Finset.range (n + 1), k) * 2 = (n + 1) * n := by rw [this]; simp
    have h' := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at h'
    field_simp; linarith
  have h2 : ∑ k ∈ Finset.range (n + 1), max a (((n : ℝ) - k) / n) =
      ∑ k ∈ Finset.range (n + 1), max a ((k : ℝ) / n) := by
    rw [← Finset.sum_range_reflect (fun k => max a ((k : ℝ) / n)) (n + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show n + 1 - 1 - k = n - k by omega, Nat.cast_sub hk']
  rw [h1, h2]
  linarith [sum_max_le hn ha0 ha1]

lemma value_le {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : Strategy (n + 1)) :
    value s (hardLaw n a) ≤ ENNReal.ofReal ((1 / ((n : ℝ) + 1)) *
      (((n : ℝ) + 1) / 2 + n * ((((n : ℝ) + 1) / n) ^ 2 + a ^ 2) / 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set g : Fin (n + 1) → ℝ := fun i => ((i.val : ℝ)) / n + max a (((n : ℝ) - i.val) / n) with hg
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [g]; have := le_max_left a (((n : ℝ) - i.val) / n); positivity
  unfold value
  calc (1 / ((n + 1).factorial : ENNReal)) * ∑ σ : Equiv.Perm (Fin (n + 1)),
        ∫⁻ p, ENNReal.ofReal (reward s p.1 σ p.2)
          ∂((Measure.pi (hardLaw n a)).prod BlindProphetSec.Blind.unif01)
      ≤ (1 / ((n + 1).factorial : ENNReal)) * ∑ σ : Equiv.Perm (Fin (n + 1)),
          ENNReal.ofReal (g (σ.symm (Fin.last n))) := by
        gcongr with σ
        exact per_sigma hn ha0 ha1 s σ
    _ = ENNReal.ofReal ((1 / ((n + 1).factorial : ℝ)) *
          ∑ σ : Equiv.Perm (Fin (n + 1)), g (σ.symm (Fin.last n))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun σ _ => hg0 _)]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by positivity)]
        simp
    _ = ENNReal.ofReal ((1 / ((n : ℝ) + 1)) * ∑ i, g i) := by
        congr 1
        have h := sum_perm_symm g (Fin.last n)
        have hf : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hf0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
        rw [hf] at h ⊢
        push_cast at h
        field_simp
        nlinarith [h]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left (sum_bound hn ha0 ha1) (by positivity)

lemma emax_le {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha1 : a ≤ 1) :
    BlindProphetSec.Blind.Emax (hardLaw n a) ≤ ENNReal.ofReal n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ∀ i, IsProbabilityMeasure (hardLaw n a i) := hard_prob hn a
  unfold BlindProphetSec.Blind.Emax
  calc ∫⁻ v, ENNReal.ofReal (⨆ i, v i) ∂(Measure.pi (hardLaw n a))
      ≤ ∫⁻ v, ENNReal.ofReal n ∂(Measure.pi (hardLaw n a)) := by
        apply lintegral_mono_ae
        filter_upwards [hard_ae_pi hn a] with v hv
        apply ENNReal.ofReal_le_ofReal
        apply ciSup_le
        intro i
        by_cases hi : i = Fin.last n
        · rw [(hv i).1 hi]; linarith
        · rcases (hv i).2 hi with h | h <;> rw [h]; linarith
    _ = ENNReal.ofReal n := by simp

lemma pow_bound {n : ℕ} (hn : 1 ≤ n) :
    (1 - 1 / (n : ℝ) ^ 2) ^ n ≤ n / ((n : ℝ) + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := 1 / (n : ℝ) ^ 2 with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; nlinarith
  have h1 : (1 - p) ^ n * (1 + p) ^ n ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h2 : 1 + (n : ℝ) * p ≤ (1 + p) ^ n := one_add_mul_le_pow (by linarith) n
  have h3 : (n : ℝ) * p = 1 / n := by rw [hp]; field_simp
  have hq0 : 0 ≤ (1 - p) ^ n := pow_nonneg (by linarith) n
  have h4 : (1 - p) ^ n * (1 + 1 / (n : ℝ)) ≤ 1 := by
    rw [← h3]; nlinarith [mul_le_mul_of_nonneg_left h2 hq0]
  rw [le_div_iff₀ (by positivity)]
  have : (1 - p) ^ n * (1 + 1 / (n : ℝ)) * n = (1 - p) ^ n * (n + 1) := by field_simp
  nlinarith

lemma emax_ge {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ENNReal.ofReal ((n : ℝ) * (1 + a) / (n + 1)) ≤ BlindProphetSec.Blind.Emax (hardLaw n a) := by
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ∀ i, IsProbabilityMeasure (hardLaw n a i) := hard_prob hn a
  set Fb : Set (Fin (n + 1) → ℝ) := Set.pi Set.univ
    (fun i => if i = Fin.last n then Set.univ else ({(n : ℝ)} : Set ℝ)ᶜ) with hFb
  have hFm : MeasurableSet Fb := by
    apply MeasurableSet.univ_pi
    intro i; split_ifs
    · exact MeasurableSet.univ
    · exact (measurableSet_singleton _).compl
  have hFmeas : (Measure.pi (hardLaw n a)) Fb = ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 2) ^ n) := by
    rw [hFb, Measure.pi_pi, Fin.prod_univ_castSucc, if_pos rfl, measure_univ, mul_one]
    rw [ENNReal.ofReal_pow (by
      have : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      linarith)]
    rw [← Fin.prod_const]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_neg (Fin.castSucc_lt_last i).ne]
    exact hard_compl_singleton hn a _ (Fin.castSucc_lt_last i).ne
  have hq := pow_bound hn
  set q := (1 - 1 / (n : ℝ) ^ 2) ^ n with hqdef
  have hq0 : 0 ≤ q := by
    rw [hqdef]; apply pow_nonneg
    have : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hq1 : q ≤ 1 := le_trans hq (by rw [div_le_one (by positivity)]; linarith)
  unfold BlindProphetSec.Blind.Emax
  calc ENNReal.ofReal ((n : ℝ) * (1 + a) / (n + 1))
      ≤ ENNReal.ofReal (a + (n - a) * (1 - q)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ (by positivity)]
        have h5 : (1 - q) * (n + 1) ≥ 1 := by
          have := (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).1 hq
          linarith
        have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ n - a)
        nlinarith
    _ = ∫⁻ v, (ENNReal.ofReal a + ENNReal.ofReal (n - a) * Fbᶜ.indicator 1 v)
          ∂(Measure.pi (hardLaw n a)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (measurable_one.indicator hFm.compl),
          lintegral_indicator_one hFm.compl, prob_compl_eq_one_sub hFm, hFmeas,
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add ha0 (by nlinarith)]
    _ ≤ ∫⁻ v, ENNReal.ofReal (⨆ i, v i) ∂(Measure.pi (hardLaw n a)) := by
        apply lintegral_mono_ae
        filter_upwards [hard_ae_pi hn a] with v hv
        have hbdd : BddAbove (Set.range v) := Set.finite_range v |>.bddAbove
        by_cases hvF : v ∈ Fb
        · rw [Set.indicator_of_notMem (by simpa using hvF)]
          simp only [mul_zero, add_zero]
          apply ENNReal.ofReal_le_ofReal
          rw [← (hv (Fin.last n)).1 rfl]
          exact le_ciSup hbdd _
        · rw [Set.indicator_of_mem hvF]
          simp only [Pi.one_apply, mul_one]
          rw [← ENNReal.ofReal_add ha0 (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          rw [hFb] at hvF
          simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hvF
          obtain ⟨i, hi⟩ := hvF
          by_cases hil : i = Fin.last n
          · simp [hil] at hi
          · simp only [if_neg hil, Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hi
            rw [← hi]
            have := le_ciSup hbdd i
            linarith

lemma hard_Iio {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (i : Fin (n + 1)) :
    hardLaw n a i (Set.Iio 0) = 0 := by
  unfold hardLaw
  split_ifs
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ measurableSet_Iio, Measure.dirac_apply' _ measurableSet_Iio]
    rw [Set.indicator_of_notMem (by simp), Set.indicator_of_notMem (by simp)]
    simp
  · rw [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator_of_notMem (by simpa using ha0)]


lemma emax_eq {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    BlindProphetSec.Blind.Emax (hardLaw n a) = ENNReal.ofReal
      ((n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ n) + (1 - 1 / (n : ℝ) ^ 2) ^ n * a) := by
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ∀ i, IsProbabilityMeasure (hardLaw n a i) := hard_prob hn a
  set Fb : Set (Fin (n + 1) → ℝ) := Set.pi Set.univ
    (fun i => if i = Fin.last n then Set.univ else ({(n : ℝ)} : Set ℝ)ᶜ) with hFb
  have hFm : MeasurableSet Fb := by
    apply MeasurableSet.univ_pi
    intro i; split_ifs
    · exact MeasurableSet.univ
    · exact (measurableSet_singleton _).compl
  have hFmeas : (Measure.pi (hardLaw n a)) Fb = ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 2) ^ n) := by
    rw [hFb, Measure.pi_pi, Fin.prod_univ_castSucc, if_pos rfl, measure_univ, mul_one]
    rw [ENNReal.ofReal_pow (by
      have : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      linarith)]
    rw [← Fin.prod_const]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_neg (Fin.castSucc_lt_last i).ne]
    exact hard_compl_singleton hn a _ (Fin.castSucc_lt_last i).ne
  set q := (1 - 1 / (n : ℝ) ^ 2) ^ n with hqdef
  have hq0 : 0 ≤ q := by
    rw [hqdef]; apply pow_nonneg
    have : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hq1 : q ≤ 1 := le_trans (pow_bound hn) (by rw [div_le_one (by positivity)]; linarith)
  unfold BlindProphetSec.Blind.Emax
  calc ∫⁻ v, ENNReal.ofReal (⨆ i, v i) ∂(Measure.pi (hardLaw n a))
      = ∫⁻ v, (ENNReal.ofReal a + ENNReal.ofReal (n - a) * Fbᶜ.indicator 1 v)
          ∂(Measure.pi (hardLaw n a)) := by
        apply lintegral_congr_ae
        filter_upwards [hard_ae_pi hn a] with v hv
        have hbdd : BddAbove (Set.range v) := Set.finite_range v |>.bddAbove
        by_cases hvF : v ∈ Fb
        · rw [Set.indicator_of_notMem (by simpa using hvF)]
          simp only [mul_zero, add_zero]
          congr 1
          apply le_antisymm
          · apply ciSup_le
            intro i
            by_cases hil : i = Fin.last n
            · rw [(hv i).1 hil]
            · have hi := hvF i (Set.mem_univ _)
              simp only [hFb, if_neg hil, Set.mem_compl_iff, Set.mem_singleton_iff] at hi
              rcases (hv i).2 hil with h | h
              · rw [h]; exact ha0
              · exact absurd h hi
          · rw [← (hv (Fin.last n)).1 rfl]
            exact le_ciSup hbdd _
        · rw [Set.indicator_of_mem hvF]
          simp only [Pi.one_apply, mul_one]
          rw [← ENNReal.ofReal_add ha0 (by linarith)]
          congr 1
          rw [hFb] at hvF
          simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hvF
          obtain ⟨i, hi⟩ := hvF
          by_cases hil : i = Fin.last n
          · simp [hil] at hi
          · simp only [if_neg hil, Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at hi
            apply le_antisymm
            · apply ciSup_le
              intro j
              by_cases hjl : j = Fin.last n
              · rw [(hv j).1 hjl]; linarith
              · rcases (hv j).2 hjl with h | h <;> rw [h] <;> linarith
            · rw [← hi]
              have := le_ciSup hbdd i
              linarith
    _ = ENNReal.ofReal (a + (n - a) * (1 - q)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (measurable_one.indicator hFm.compl),
          lintegral_indicator_one hFm.compl, prob_compl_eq_one_sub hFm, hFmeas,
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add ha0 (by nlinarith)]
    _ = _ := by congr 1; ring

end BPS2Aux

open BPS2Aux in
theorem solution (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∀ n : ℕ, 1 ≤ n →
      BlindProphetSec.Blind.Emax (hardLaw n a) =
        ENNReal.ofReal ((n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ n) +
          (1 - 1 / (n : ℝ) ^ 2) ^ n * a)) ∧
    Tendsto (fun n : ℕ => (BlindProphetSec.Blind.Emax (hardLaw n a)).toReal) atTop (𝓝 (1 + a)) := by
  refine ⟨fun n hn => emax_eq hn ha0 ha1, ?_⟩
  have hev : ∀ᶠ n : ℕ in atTop, (BlindProphetSec.Blind.Emax (hardLaw n a)).toReal =
      (n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ n) + (1 - 1 / (n : ℝ) ^ 2) ^ n * a := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have hq0 : 0 ≤ (1 - 1 / (n : ℝ) ^ 2) ^ n := pow_nonneg (by linarith) n
    have hq1 : (1 - 1 / (n : ℝ) ^ 2) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by
      have : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
      linarith)
    rw [emax_eq hn ha0 ha1, ENNReal.toReal_ofReal (by nlinarith)]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  -- bounds on q_n = (1 - 1/n^2)^n
  have hlow : ∀ᶠ n : ℕ in atTop, 1 - 1 / (n : ℝ) ≤ (1 - 1 / (n : ℝ) ^ 2) ^ n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have := one_add_mul_le_pow (a := -(1 / (n : ℝ) ^ 2)) (by linarith) n
    have e : (n : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / n := by field_simp
    have e2 : 1 + -(1 / (n : ℝ) ^ 2) = 1 - 1 / (n : ℝ) ^ 2 := by ring
    rw [e2] at this; nlinarith
  have hup : ∀ᶠ n : ℕ in atTop, (1 - 1 / (n : ℝ) ^ 2) ^ n ≤ n / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pow_bound hn
  have hq_t : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ) ^ 2) ^ n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop (1 : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 hlow hup
  have hnq_t : Tendsto (fun n : ℕ => (n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ n)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop (1 : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 tendsto_const_nhds ?_ ?_
    · filter_upwards [hup, eventually_ge_atTop 1] with n hn hn1
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by field_simp; ring
      have h3 : (n : ℝ) * (1 / (n + 1)) = n / (n + 1) := by ring
      nlinarith
    · filter_upwards [hlow, eventually_ge_atTop 1] with n hn hn1
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have : (n : ℝ) * (1 / n) = 1 := by field_simp
      nlinarith
  have := hnq_t.add (hq_t.mul_const a)
  simpa using this
