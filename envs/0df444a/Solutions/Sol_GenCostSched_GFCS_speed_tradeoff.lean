-- Prove2me | solution 1 for GenCostSched.GFCS.speed_tradeoff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:44:39.706265+00:00
-- url     : https://prove2.me/submissions/062fc375-74fd-4a7d-ad9d-f2d4372ad305
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model
import Theorems.Thm_GenCostSched_GFCS_dual_attainment
import Theorems.Thm_GenCostSched_GFCS_lemma_6
import Theorems.Thm_GenCostSched_GFCS_betahat_dual_feasible
import Theorems.Thm_GenCostSched_GFCS_beta_increment_le
import Theorems.Thm_GenCostSched_GFCS_weak_duality_21

open MeasureTheory Set
open scoped ENNReal

namespace GFCSSpeedAux
open GenCostSched.GFCS

variable {n : ℕ}

theorem mem_aliveOld {I : Instance n} {y : Fin n → ℝ → ℝ} {k j : Fin n} :
    j ∈ I.aliveOld y k ↔ j < k ∧ 0 < I.residual y k j := by
  simp [Instance.aliveOld]

theorem tailFrom_of_le {m : ℕ} {s t : ℝ} (x : Fin m → ℝ → ℝ) (j : Fin m) (h : s ≤ t) :
    tailFrom s x j t = x j t := by
  simp [tailFrom, indicator_of_mem (mem_Ici.2 h)]

theorem tailFrom_of_lt {m : ℕ} {s t : ℝ} (x : Fin m → ℝ → ℝ) (j : Fin m) (h : t < s) :
    tailFrom s x j t = 0 := by
  simp [tailFrom, indicator_of_notMem (show t ∉ Ici s from fun h' => absurd (mem_Ici.1 h') (not_le.2 h))]

/-- Basic invariants of a run of Algorithm 2. -/
theorem run_inv (I : Instance n) (hI : I.Standing) (X : ℕ → Fin n → ℝ → ℝ)
    (hX : I.IsAlg2Run X) : ∀ i, i ≤ n →
    (∀ j, Measurable (X i j)) ∧ (∀ j t, X i j t = 0 ∨ X i j t = 1) ∧
    (∀ t, ∑ j, X i j t ≤ 1) ∧ (∀ j t, t < I.r j → X i j t = 0) ∧
    (∀ j : Fin n, i ≤ j.val → ∀ t, X i j t = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hX.1]
    refine ⟨fun j => measurable_const, fun j t => Or.inl rfl, fun t => by simp,
      fun j t _ => rfl, fun j _ t => rfl⟩
    -- unreachable
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih (by omega)
    set k : Fin n := ⟨i, by omega⟩ with hk
    obtain ⟨hbef, hopt, _⟩ := hX.2 k
    have hkv : k.val = i := rfl
    rw [hkv] at hbef hopt
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hopt.1
    have hrep : ∀ j t, X (i+1) j t =
        if t < I.r k then X i j t else tailFrom (I.r k) (X (i+1)) j t := by
      intro j t
      split_ifs with h
      · exact hbef j t h
      · exact (tailFrom_of_le _ _ (le_of_not_gt h)).symm
    have hout : ∀ j : Fin n, j ∉ insert k (I.aliveOld (X i) k) → ∀ t,
        tailFrom (I.r k) (X (i+1)) j t = 0 := fun j hj t => o4 j hj t
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      have : X (i+1) j = (Iio (I.r k)).piecewise (X i j) (tailFrom (I.r k) (X (i+1)) j) := by
        funext t
        rw [hrep j t]
        by_cases h : t < I.r k
        · simp [h, Set.piecewise, mem_Iio]
        · simp [h, Set.piecewise, mem_Iio]
      rw [this]
      exact Measurable.piecewise measurableSet_Iio (ih1 j) (o1 j)
    · intro j t
      rw [hrep j t]; split_ifs
      · exact ih2 j t
      · exact o2 j t
    · intro t
      by_cases h : t < I.r k
      · simp only [hrep _ t, h, if_true]; exact ih3 t
      · simp only [hrep _ t, h, if_false]; exact o5 t
    · intro j t ht
      rw [hrep j t]; split_ifs with h
      · exact ih4 j t ht
      · apply hout j _ t
        intro hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact h ht
        · have hjk := (mem_aliveOld.1 hj).1
          exact h (lt_of_lt_of_le ht (hI.2 hjk.le))
    · intro j hj t
      rw [hrep j t]; split_ifs with h
      · exact ih5 j (by omega) t
      · apply hout j _ t
        intro hj'
        rcases Finset.mem_insert.1 hj' with h' | h'
        · rw [h'] at hj; simp [k] at hj
        · have := (mem_aliveOld.1 h').1
          have : j.val < i := this
          omega

theorem X_intOn (I : Instance n) (hI : I.Standing) (X : ℕ → Fin n → ℝ → ℝ)
    (hX : I.IsAlg2Run X) (i : ℕ) (hi : i ≤ n) (j : Fin n) (b : ℝ) (S : Set ℝ)
    (hS : S ⊆ Iio b) : IntegrableOn (X i j) S := by
  obtain ⟨h1, h2, _, h4, _⟩ := run_inv I hI X hX i hi
  have hr0 : 0 ≤ I.r j := (hI.1 j).2.1
  have hb : IntegrableOn (X i j) (Ico 0 b) := by
    refine Measure.integrableOn_of_bounded (M := 1) (by simp) (h1 j).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    rcases h2 j t with h | h <;> simp [h]
  have hI' : IntegrableOn (X i j) (Iio b) := by
    refine hb.of_forall_sdiff_eq_zero measurableSet_Iio ?_
    intro t ht
    have ht0 : t < 0 := by
      by_contra hc
      exact ht.2 ⟨le_of_not_gt hc, ht.1⟩
    exact h4 j t (lt_of_lt_of_le ht0 hr0)
  exact hI'.mono_set hS

theorem lint_tail {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (x : Fin m → ℝ → ℝ) (j : Fin m) :
    ∫⁻ t, ENNReal.ofReal (G j t * tailFrom s x j t) =
      ∫⁻ t in Ici s, ENNReal.ofReal (G j t * x j t) := by
  rw [← lintegral_indicator measurableSet_Ici]
  congr 1
  funext t
  by_cases h : s ≤ t
  · rw [tailFrom_of_le _ _ h, indicator_of_mem (mem_Ici.2 h)]
  · rw [tailFrom_of_lt _ _ (lt_of_not_ge h),
      indicator_of_notMem (fun h' => h (mem_Ici.1 h'))]; simp

theorem lint_tail' {m : ℕ} (s : ℝ) (x : Fin m → ℝ → ℝ) (j : Fin m) :
    ∫⁻ t, ENNReal.ofReal (tailFrom s x j t) = ∫⁻ t in Ici s, ENNReal.ofReal (x j t) := by
  have := lint_tail (fun _ _ => (1:ℝ)) s x j
  simpa using this

theorem lint_split (f : ℝ → ℝ≥0∞) (a : ℝ) :
    ∫⁻ t, f t = (∫⁻ t in Iio a, f t) + ∫⁻ t in Ici a, f t := by
  rw [← lintegral_add_compl f (measurableSet_Iio (a := a)), compl_Iio]

noncomputable def xo (I : Instance n) (X : ℕ → Fin n → ℝ → ℝ) (k : Fin n) :
    Fin n → ℝ → ℝ := tailFrom (I.r k) (X k.val)

noncomputable def xn (I : Instance n) (X : ℕ → Fin n → ℝ → ℝ) (k : Fin n) :
    Fin n → ℝ → ℝ := tailFrom (I.r k) (X (k.val + 1))

noncomputable def xt (I : Instance n) (X : ℕ → Fin n → ℝ → ℝ) (k : Fin n) :
    Fin n → ℝ → ℝ := fun j t => if j ∈ I.aliveOld (X k.val) k then xo I X k j t else 0

theorem ofReal_ae_zero {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ t, 0 ≤ f t)
    (h : ∫⁻ t, ENNReal.ofReal (f t) = 0) : f =ᵐ[volume] 0 := by
  rw [lintegral_eq_zero_iff hf.ennreal_ofReal] at h
  filter_upwards [h] with t ht
  have : f t ≤ 0 := ENNReal.ofReal_eq_zero.1 ht
  simp [le_antisymm this (hnn t)]

/-- Principle of optimality for a run of Algorithm 2: the continuing schedule at the arrival of
job `k` (cleaned of finished jobs) is an optimal integral schedule of the residual instance. -/
theorem old_opt (I : Instance n) (hI : I.Standing) (X : ℕ → Fin n → ℝ → ℝ)
    (hX : I.IsAlg2Run X) (hfin : ∀ k : Fin n, offCost I.g (xn I X k) ≠ ⊤) (k : Fin n) :
    IsOptIntegral I.g (I.r k) (I.aliveOld (X k.val) k) (I.residual (X k.val) k) (xt I X k) ∧
      (∀ j, j ∉ I.aliveOld (X k.val) k → xo I X k j =ᵐ[volume] 0) := by
  rcases Nat.eq_zero_or_eq_succ_pred k.val with hk0 | hk
  · -- first arrival
    have hAl : I.aliveOld (X k.val) k = ∅ := by
      ext j; simp only [mem_aliveOld, Finset.notMem_empty, iff_false, not_and]
      intro h; exact absurd h (by rw [Fin.lt_def, hk0]; omega)
    have hxo : xo I X k = 0 := by
      funext j t; simp [xo, tailFrom, hk0, hX.1]
    have hxt : xt I X k = 0 := by
      funext j t; simp [xt, hAl]
    rw [hAl, hxt]
    refine ⟨⟨⟨fun j => measurable_const, fun j t => Or.inl rfl, fun j t _ => rfl,
      fun j _ t => rfl, fun t => by simp, fun j hj => absurd hj (Finset.notMem_empty _),
      ⟨0, fun j t _ => rfl⟩⟩, fun y _ => by simp [offCost]⟩, fun j _ => by rw [hxo]; rfl⟩
  · set p := k.val - 1 with hp
    have hpn : p < n := by omega
    set pf : Fin n := ⟨p, hpn⟩ with hpf
    have hkp : k.val = pf.val + 1 := by simp [pf]; omega
    obtain ⟨hbef, hopt, _⟩ := hX.2 pf
    have hpfv : pf.val = p := rfl
    obtain ⟨y1, y2, y3, y4, y5⟩ := run_inv I hI X hX (pf.val + 1) (by omega)
    set Y := X (pf.val + 1) with hY
    have hXk : X k.val = Y := by rw [hkp]
    have hlt : pf < k := by rw [Fin.lt_def]; omega
    have hss : I.r pf ≤ I.r k := hI.2 hlt.le
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hopt.1
    set s := I.r pf
    set s' := I.r k
    set Alp := I.aliveOld (X pf.val) pf
    set ρp := I.residual (X pf.val) pf
    have hxoY : xo I X k = tailFrom s' Y := by simp only [xo, hXk]; rfl
    have hxtY : ∀ j t, xt I X k j t =
        if j ∈ I.aliveOld Y k then tailFrom s' Y j t else 0 := by
      intro j t; simp only [xt, hxoY, hXk]
    rw [hXk]
    -- residual relation
    set Ij : Fin n → ℝ := fun j => ∫ t in Ico s s', Y j t with hIj
    have hIj0 : ∀ j, 0 ≤ Ij j := fun j => by
      apply setIntegral_nonneg measurableSet_Ico
      intro t _; rcases y2 j t with h | h <;> simp [h]
    have hR1 : ∀ j, I.residual Y k j = ρp j - Ij j := by
      intro j
      simp only [Instance.residual, ρp, Ij]
      have hU : Iio s' = Iio s ∪ Ico s s' := by
        ext t; simp only [mem_Iio, mem_union, mem_Ico]
        constructor
        · intro h; by_cases h' : t < s
          · exact Or.inl h'
          · exact Or.inr ⟨le_of_not_gt h', h⟩
        · rintro (h | h)
          · exact lt_of_lt_of_le h hss
          · exact h.2
      rw [hU, setIntegral_union (by
          rw [Set.disjoint_left]; intro t h1 h2; exact absurd h2.1 (not_le.2 h1))
        measurableSet_Ico (X_intOn I hI X hX _ (by omega) j s' _ (by intro t ht; exact lt_of_lt_of_le ht hss))
        (X_intOn I hI X hX _ (by omega) j s' _ (fun t ht => ht.2))]
      rw [setIntegral_congr_fun measurableSet_Iio (fun t ht => hbef j t ht)]
      ring
    -- lintegral over [s, s')
    have hIco : ∀ j, ∫⁻ t in Iio s', ENNReal.ofReal (tailFrom s Y j t) = ENNReal.ofReal (Ij j) := by
      intro j
      have : ∫⁻ t in Iio s', ENNReal.ofReal (tailFrom s Y j t) =
          ∫⁻ t in Ico s s', ENNReal.ofReal (Y j t) := by
        have hfun : (fun t => ENNReal.ofReal (tailFrom s Y j t)) =
            (Ici s).indicator (fun t => ENNReal.ofReal (Y j t)) := by
          funext t
          by_cases h : s ≤ t
          · rw [tailFrom_of_le _ _ h, indicator_of_mem (mem_Ici.2 h)]
          · rw [tailFrom_of_lt _ _ (lt_of_not_ge h),
              indicator_of_notMem (fun h' => h (mem_Ici.1 h'))]; simp
        rw [hfun, setLIntegral_indicator measurableSet_Ici]
        congr 2
      rw [this, ofReal_integral_eq_lintegral_ofReal]
      · exact X_intOn I hI X hX _ (by omega) j s' _ (fun t ht => ht.2)
      · refine Filter.Eventually.of_forall (fun t => ?_)
        rcases y2 j t with h | h <;> simp [h]
    -- R2
    have hR2 : ∀ j ∈ insert pf Alp,
        ∫⁻ t, ENNReal.ofReal (tailFrom s' Y j t) = ENNReal.ofReal (I.residual Y k j) := by
      intro j hj
      have h6 := o6 j hj
      rw [lint_split _ s', hIco j] at h6
      have hL : ∫⁻ t in Ici s', ENNReal.ofReal (tailFrom s Y j t) =
          ∫⁻ t, ENNReal.ofReal (tailFrom s' Y j t) := by
        rw [lint_tail']
        apply setLIntegral_congr_fun measurableSet_Ici
        intro t ht
        dsimp only
        rw [tailFrom_of_le _ _ (hss.trans (mem_Ici.1 ht))]
      rw [hL] at h6
      rw [hR1 j, ENNReal.ofReal_sub _ (hIj0 j), ← h6]
      rw [ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
    have hM : ∀ j ∈ I.aliveOld Y k, j ∈ insert pf Alp := by
      intro j hj
      obtain ⟨hjk, hjr⟩ := mem_aliveOld.1 hj
      by_cases hjp : j = pf
      · rw [hjp]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have hjlt : j < pf := by
          rw [Fin.lt_def] at hjk ⊢
          have : j.val ≠ pf.val := fun h => hjp (Fin.ext h)
          omega
        refine mem_aliveOld.2 ⟨hjlt, ?_⟩
        have := hR1 j
        have := hIj0 j
        show 0 < ρp j
        linarith
    have hN : ∀ j, j ∉ insert pf Alp → ∀ t, tailFrom s' Y j t = 0 := by
      intro j hj t
      by_cases h : s' ≤ t
      · rw [tailFrom_of_le _ _ h, ← tailFrom_of_le Y j (hss.trans h)]
        exact o4 j hj t
      · exact tailFrom_of_lt _ _ (lt_of_not_ge h)
    have hjlt_of : ∀ j ∈ insert pf Alp, j < k := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hlt
      · exact lt_trans (mem_aliveOld.1 hj).1 hlt
    have hZ : ∀ j, j ∉ I.aliveOld Y k → tailFrom s' Y j =ᵐ[volume] 0 := by
      intro j hj
      by_cases hji : j ∈ insert pf Alp
      · apply ofReal_ae_zero
        · exact (y1 j).indicator measurableSet_Ici
        · intro t; by_cases h : s' ≤ t
          · rw [tailFrom_of_le _ _ h]; rcases y2 j t with h | h <;> simp [h]
          · rw [tailFrom_of_lt _ _ (lt_of_not_ge h)]
        · rw [hR2 j hji]
          apply ENNReal.ofReal_eq_zero.2
          by_contra hc
          exact hj (mem_aliveOld.2 ⟨hjlt_of j hji, lt_of_not_ge hc⟩)
      · exact Filter.Eventually.of_forall (fun t => hN j hji t)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- integral schedule
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        by_cases h : j ∈ I.aliveOld Y k
        · have : xt I X k j = tailFrom s' Y j := by funext t; rw [hxtY]; simp [h]
          rw [this]; exact (y1 j).indicator measurableSet_Ici
        · have : xt I X k j = fun _ => 0 := by funext t; rw [hxtY]; simp [h]
          rw [this]; exact measurable_const
      · intro j t
        rw [hxtY]; split_ifs
        · by_cases h : s' ≤ t
          · rw [tailFrom_of_le _ _ h]; exact y2 j t
          · rw [tailFrom_of_lt _ _ (lt_of_not_ge h)]; exact Or.inl rfl
        · exact Or.inl rfl
      · intro j t ht
        rw [hxtY]; split_ifs
        · exact tailFrom_of_lt _ _ ht
        · rfl
      · intro j hj t
        rw [hxtY]; simp [hj]
      · intro t
        refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (y3 t)
        rw [hxtY]; split_ifs
        · by_cases h : s' ≤ t
          · rw [tailFrom_of_le _ _ h]
          · rw [tailFrom_of_lt _ _ (lt_of_not_ge h)]; rcases y2 j t with h | h <;> simp [h]
        · rcases y2 j t with h | h <;> simp [h]
      · intro j hj
        have : xt I X k j = tailFrom s' Y j := by funext t; rw [hxtY]; simp [hj]
        rw [this, hR2 j (hM j hj)]
      · obtain ⟨T, hT⟩ := o7
        refine ⟨max T s', fun j t ht => ?_⟩
        rw [hxtY]; split_ifs
        · rw [tailFrom_of_le _ _ (le_trans (le_max_right _ _) ht.le),
            ← tailFrom_of_le Y j (hss.trans (le_trans (le_max_right _ _) ht.le))]
          exact hT j t (lt_of_le_of_lt (le_max_left _ _) ht)
        · rfl
    · -- optimality
      intro y hy
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hy
      set z : Fin n → ℝ → ℝ := fun j t => if t < s' then tailFrom s Y j t else y j t with hz
      have hzf : IsOffFracSched s (insert pf Alp) ρp z := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          have : z j = (Iio s').piecewise (tailFrom s Y j) (y j) := by
            funext t; by_cases h : t < s' <;> simp [hz, h, Set.piecewise]
          rw [this]; exact Measurable.piecewise measurableSet_Iio (o1 j) (z1 j)
        · intro j t; simp only [hz]; split_ifs
          · rcases o2 j t with h | h <;> simp [h]
          · exact z2 j t
        · intro j t ht; simp only [hz]
          rw [if_pos (lt_of_lt_of_le ht hss)]; exact tailFrom_of_lt _ _ ht
        · intro j hj t; simp only [hz]; split_ifs
          · exact o4 j hj t
          · exact z4 j (fun h => hj (hM j h)) t
        · intro t; by_cases h : t < s'
          · simp only [hz, h, if_true]; exact o5 t
          · simp only [hz, h, if_false]; exact z5 t
        · intro j hj
          have hsplit : ∫⁻ t, ENNReal.ofReal (z j t) =
              ENNReal.ofReal (Ij j) + ∫⁻ t, ENNReal.ofReal (y j t) := by
            rw [lint_split _ s', ← hIco j]
            congr 1
            · apply setLIntegral_congr_fun measurableSet_Iio
              intro t ht; simp [hz, mem_Iio.1 ht]
            · rw [lint_split (fun t => ENNReal.ofReal (y j t)) s']
              have h0 : ∫⁻ t in Iio s', ENNReal.ofReal (y j t) = 0 := by
                rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
                  (fun t ht => by simp [z3 j t (mem_Iio.1 ht)])]
                simp
              rw [h0, zero_add]
              apply setLIntegral_congr_fun measurableSet_Ici
              intro t ht; simp [hz, not_lt.2 (mem_Ici.1 ht)]
          rw [hsplit]
          by_cases hja : j ∈ I.aliveOld Y k
          · calc ENNReal.ofReal (ρp j) = ENNReal.ofReal (Ij j + I.residual Y k j) := by
                  rw [hR1 j]; ring_nf
              _ ≤ ENNReal.ofReal (Ij j) + ENNReal.ofReal (I.residual Y k j) := ENNReal.ofReal_add_le
              _ ≤ _ := by gcongr; exact z6 j hja
          · have hres : I.residual Y k j ≤ 0 := by
              by_contra hc
              exact hja (mem_aliveOld.2 ⟨hjlt_of j hj, lt_of_not_ge hc⟩)
            calc ENNReal.ofReal (ρp j) ≤ ENNReal.ofReal (Ij j) := by
                  apply ENNReal.ofReal_le_ofReal; have := hR1 j; linarith
              _ ≤ _ := le_self_add
      have hle := hopt.2 z hzf
      -- decompose costs
      set P : ℝ≥0∞ := ∑ j, ∫⁻ t in Iio s', ENNReal.ofReal (I.g j t * tailFrom s Y j t) with hP
      have hc1 : offCost I.g (tailFrom s Y) = P + offCost I.g (xt I X k) := by
        simp only [offCost, hP, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        rw [lint_split _ s']
        congr 1
        have e1 : ∫⁻ t in Ici s', ENNReal.ofReal (I.g j t * tailFrom s Y j t) =
            ∫⁻ t, ENNReal.ofReal (I.g j t * tailFrom s' Y j t) := by
          rw [lint_tail]
          apply setLIntegral_congr_fun measurableSet_Ici
          intro t ht; dsimp only; rw [tailFrom_of_le _ _ (hss.trans (mem_Ici.1 ht))]
        rw [e1]
        by_cases hja : j ∈ I.aliveOld Y k
        · congr 1; funext t; rw [hxtY]; simp [hja]
        · apply lintegral_congr_ae
          filter_upwards [hZ j hja] with t ht
          rw [hxtY]; simp [hja, ht]
      have hc2 : offCost I.g z = P + offCost I.g y := by
        simp only [offCost, hP, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        rw [lint_split _ s']
        congr 1
        · apply setLIntegral_congr_fun measurableSet_Iio
          intro t ht; simp [hz, mem_Iio.1 ht]
        · rw [lint_split (fun t => ENNReal.ofReal (I.g j t * y j t)) s']
          have h0 : ∫⁻ t in Iio s', ENNReal.ofReal (I.g j t * y j t) = 0 := by
            rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
              (fun t ht => by simp [z3 j t (mem_Iio.1 ht)])]
            simp
          rw [h0, zero_add]
          apply setLIntegral_congr_fun measurableSet_Ici
          intro t ht; simp [hz, not_lt.2 (mem_Ici.1 ht)]
      have hPfin : P ≠ ⊤ := by
        have h1 : P ≤ offCost I.g (tailFrom s Y) := by rw [hc1]; exact le_self_add
        exact ne_top_of_le_ne_top (hfin pf) h1
      rw [hc1, hc2] at hle
      exact (ENNReal.add_le_add_iff_left hPfin).1 hle
    · intro j hj
      rw [hxoY]; exact hZ j hj

theorem gp_nonneg {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j) (t : ℝ)
    (ht : I.r j ≤ t) : 0 ≤ I.g' j t := by
  have hd := hj.2.2.2.2.2 t ht
  have hmono := hj.2.2.2.1
  have := hmono.derivWithin_nonneg (x := t)
  rwa [hd.derivWithin (uniqueDiffOn_Ici _ t (mem_Ici.2 ht))] at this

theorem gp_int {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j) (a b : ℝ)
    (ha : I.r j ≤ a) : IntegrableOn (I.g' j) (Icc a b) := by
  have hd := hj.2.2.2.2.2
  have hcont : ContinuousOn (I.g j) (Icc a b) := by
    intro t ht
    exact ((hd t (ha.trans ht.1)).continuousWithinAt).mono
      (fun u hu => mem_Ici.2 (ha.trans hu.1))
  have h1 : IntegrableOn (I.g' j) (Ioc a b) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg hcont
    · intro t ht
      exact (hd t (ha.trans ht.1.le)).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt ha ht.1))
    · intro t ht
      exact gp_nonneg I j hj t (ha.trans ht.1.le)
  exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h1

/-- Integrability and nonnegativity of `β̂` for an integral schedule. -/
theorem BH_int {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (x : Fin m → ℝ → ℝ) (hx : IsOffIntSched s A ρ x) :
    IntegrableOn (betaHat I.g' x) (Ici s) ∧ (∀ t, 0 ≤ betaHat I.g' x t) ∧
      (∀ ℓ, Integrable (fun τ => I.g' ℓ τ * x ℓ τ)) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, ⟨T0, hT0⟩⟩ := hx
  set T := max T0 s
  have hT : ∀ j t, T < t → x j t = 0 := fun j t ht => hT0 j t (lt_of_le_of_lt (le_max_left _ _) ht)
  have hfnn : ∀ ℓ τ, 0 ≤ I.g' ℓ τ * x ℓ τ := by
    intro ℓ τ
    rcases x2 ℓ τ with h | h
    · simp [h]
    · rw [h, mul_one]
      have hℓ : ℓ ∈ A := by
        by_contra hc; rw [x4 ℓ hc τ] at h; exact zero_ne_one h
      have hτ : s ≤ τ := by
        by_contra hc; rw [x3 ℓ τ (lt_of_not_ge hc)] at h; exact zero_ne_one h
      exact gp_nonneg I ℓ (hI ℓ) τ ((hA ℓ hℓ).trans hτ)
  have hfint : ∀ ℓ, Integrable (fun τ => I.g' ℓ τ * x ℓ τ) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ A
    · have hi := (gp_int I ℓ (hI ℓ) s T (hA ℓ hℓ)).integrable_indicator measurableSet_Icc
      have h2 : Integrable (fun τ => (Icc s T).indicator (I.g' ℓ) τ * x ℓ τ) := by
        refine hi.mul_bdd (c := 1) (x1 ℓ).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall (fun τ => ?_)
        rcases x2 ℓ τ with h | h <;> simp [h]
      refine h2.congr (Filter.Eventually.of_forall (fun τ => ?_))
      dsimp only
      by_cases hτ : τ ∈ Icc s T
      · simp [indicator_of_mem hτ]
      · rw [indicator_of_notMem hτ]
        simp only [mem_Icc, not_and_or, not_le] at hτ
        rcases hτ with h | h
        · simp [x3 ℓ τ h]
        · simp [hT ℓ τ h]
    · have : (fun τ => I.g' ℓ τ * x ℓ τ) = fun _ => 0 := by
        funext τ; simp [x4 ℓ hℓ τ]
      rw [this]; exact integrable_zero _ _ _
  have hanti : Antitone (betaHat I.g' x) := by
    intro t t' htt
    apply Finset.sum_le_sum
    intro ℓ _
    apply setIntegral_mono_set (hfint ℓ).integrableOn
    · exact Filter.Eventually.of_forall (fun τ => hfnn ℓ τ)
    · exact (Ioi_subset_Ioi htt).eventuallyLE
  have hnn : ∀ t, 0 ≤ betaHat I.g' x t := by
    intro t
    apply Finset.sum_nonneg
    intro ℓ _
    exact setIntegral_nonneg measurableSet_Ioi (fun τ _ => hfnn ℓ τ)
  have hzero : ∀ t, T ≤ t → betaHat I.g' x t = 0 := by
    intro t ht
    apply Finset.sum_eq_zero
    intro ℓ _
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro τ hτ
    simp [hT ℓ τ (lt_of_le_of_lt ht hτ)]
  refine ⟨?_, hnn, hfint⟩
  have hbd : IntegrableOn (betaHat I.g' x) (Icc s T) := by
    refine Measure.integrableOn_of_bounded (M := betaHat I.g' x s) (by simp)
      hanti.measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun t ht => ?_))
    rw [Real.norm_of_nonneg (hnn t)]
    exact hanti ht.1
  refine hbd.of_forall_sdiff_eq_zero measurableSet_Ici ?_
  intro t ht
  apply hzero
  by_contra hc
  exact ht.2 ⟨mem_Ici.1 ht.1, le_of_not_ge hc⟩

theorem optInt_eq {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral G s A ρ x) : offCost G x = rnf G s A ρ := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6, _⟩, hopt⟩ := hx
  have hfr : IsOffFracSched s A ρ x := by
    refine ⟨x1, fun j t => ?_, x3, x4, x5, fun j hj => (x6 j hj).symm.le⟩
    rcases x2 j t with h | h <;> simp [h]
  apply le_antisymm
  · exact le_sInf (by rintro _ ⟨y, hy, rfl⟩; exact hopt y hy)
  · exact sInf_le ⟨x, hfr, rfl⟩

theorem bh_tail {m : ℕ} (gp : Fin m → ℝ → ℝ) (s : ℝ) (x : Fin m → ℝ → ℝ) (t : ℝ)
    (ht : s ≤ t) : betaHat gp (tailFrom s x) t = betaHat gp x t := by
  unfold betaHat
  apply Finset.sum_congr rfl
  intro ℓ _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ hτ
  dsimp only
  rw [tailFrom_of_le _ _ (ht.trans (le_of_lt hτ))]

theorem bh_ae {m : ℕ} (gp : Fin m → ℝ → ℝ) (x y : Fin m → ℝ → ℝ)
    (h : ∀ ℓ, x ℓ =ᵐ[volume] y ℓ) (t : ℝ) : betaHat gp x t = betaHat gp y t := by
  unfold betaHat
  apply Finset.sum_congr rfl
  intro ℓ _
  apply integral_congr_ae
  apply ae_restrict_of_ae
  filter_upwards [h ℓ] with τ hτ
  rw [hτ]

theorem seg_eq (I : Instance n) (hmono : Monotone I.r) (k : Fin n) :
    I.segment k = Ici (I.r k) \ (if h : k.val + 1 < n then Ici (I.r ⟨k.val + 1, h⟩) else ∅) := by
  ext t
  simp only [Instance.segment, mem_setOf_eq, mem_diff, mem_Ici]
  split_ifs with h
  · simp only [mem_Ici, not_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 ⟨k.val + 1, h⟩ (by rw [Fin.lt_def]; simp)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k' hk' => lt_of_lt_of_le h2 (hmono ?_)⟩
      rw [Fin.le_def]; rw [Fin.lt_def] at hk'; simp; omega
  · simp only [notMem_empty, not_false_eq_true, and_true]
    constructor
    · exact fun h' => h'.1
    · intro h1
      refine ⟨h1, fun k' hk' => ?_⟩
      exfalso; rw [Fin.lt_def] at hk'; have := k'.isLt; omega

end GFCSSpeedAux

open GenCostSched.GFCS GFCSSpeedAux in
theorem solution {n : ℕ} (I : Instance n) (H : Set (ℝ → ℝ)) (K : ℝ) (hI : I.Standing)
    (h2 : I.TwiceDiff) (hH : ∀ j, I.g j ∈ H) (hMS : IsMonotoneSubstitute H)
    (hK : I.CurvBound K) (X : ℕ → Fin n → ℝ → ℝ) (hX : I.IsAlg2Run X) (ε : ℝ)
    (hε : K < 1 + ε) :
    I.algCost X ≤ ENNReal.ofReal ((1 + ε) / (1 + ε - K)) * I.optLP (1 / (1 + ε)) := by
  have hJS : ∀ j, I.JobStanding j := hI.1
  have hK1 : 1 ≤ K := hK.1
  have hAl_lt : ∀ (k j : Fin n), j ∈ I.aliveOld (X k.val) k → j < k :=
    fun k j hj => (mem_aliveOld.1 hj).1
  have hknot : ∀ k : Fin n, k ∉ I.aliveOld (X k.val) k := fun k hk => lt_irrefl _ (hAl_lt k k hk)
  have hAk' : ∀ k : Fin n, ∀ j ∈ I.aliveOld (X k.val) k, I.r j ≤ I.r k :=
    fun k j hj => hI.2 (hAl_lt k j hj).le
  have hAk : ∀ k : Fin n, ∀ j ∈ insert k (I.aliveOld (X k.val) k), I.r j ≤ I.r k := by
    intro k j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_rfl
    · exact hAk' k j hj
  have hkk : ∀ k : Fin n, I.residual (X k.val) k k = I.v k := by
    intro k
    have h5 := (run_inv I hI X hX k.val k.isLt.le).2.2.2.2 k le_rfl
    simp only [Instance.residual]
    rw [setIntegral_congr_fun measurableSet_Iio (g := fun _ => (0:ℝ)) (fun t _ => h5 t)]
    simp
  have hρpos' : ∀ k : Fin n, ∀ j ∈ I.aliveOld (X k.val) k, 0 < I.residual (X k.val) k j :=
    fun k j hj => (mem_aliveOld.1 hj).2
  have hρpos : ∀ k : Fin n, ∀ j ∈ insert k (I.aliveOld (X k.val) k),
      0 < I.residual (X k.val) k j := by
    intro k j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [hkk]; exact (hJS j).1
    · exact hρpos' k j hj
  have hDA := fun k : Fin n =>
    dual_attainment I hJS (I.r k) _ (I.residual (X k.val) k) (hAk k) (hρpos k)
  have hDAo := fun k : Fin n =>
    dual_attainment I hJS (I.r k) _ (I.residual (X k.val) k) (hAk' k) (hρpos' k)
  have hex : ∀ k : Fin n, ∃ (a : Fin n → ℝ) (β : ℝ → ℝ),
      IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k)) (I.residual (X k.val) k) a β :=
    fun k => by
      obtain ⟨_, a, β, h, _⟩ := hDA k
      exact ⟨a, β, h.1⟩
  choose Ad Bd hAB using hex
  have hnewopt : ∀ k : Fin n, IsOptIntegral I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (xn I X k) := fun k => (hX.2 k).2.1
  have hfin : ∀ k : Fin n, offCost I.g (xn I X k) ≠ ⊤ := by
    intro k; rw [optInt_eq _ _ _ _ _ (hnewopt k)]; exact (hDA k).1
  have hold := old_opt I hI X hX hfin
  have hfino : ∀ k : Fin n, offCost I.g (xt I X k) ≠ ⊤ := by
    intro k; rw [optInt_eq _ _ _ _ _ (hold k).1]; exact (hDAo k).1
  -- increments
  set Δ : Fin n → ℝ := fun k =>
    (offCost I.g (xn I X k)).toReal - (offCost I.g (xt I X k)).toReal with hΔdef
  have hΔ : ∀ k, Δ k ≤ Ad k k * I.v k := by
    intro k
    have h6 := lemma_6 I hJS (I.r k) (I.aliveOld (X k.val) k) (I.residual (X k.val) k) k
      (hknot k) (hAk' k) rfl (hρpos' k) (hkk k) (Ad k) (Bd k) (hAB k)
    rw [← optInt_eq _ _ _ _ _ (hnewopt k), ← optInt_eq _ _ _ _ _ (hold k).1] at h6
    have ha0 : 0 ≤ Ad k k * I.v k :=
      mul_nonneg ((hAB k).1.2.1 k (Finset.mem_insert_self _ _)) (hJS k).1.le
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfino k, ENNReal.ofReal_ne_top⟩) h6
    rw [ENNReal.toReal_add (hfino k) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ha0] at this
    simp only [hΔdef]; linarith
  have hpost : ∀ k : Fin n, postpones (I.r k) (I.aliveOld (X k.val) k) (xt I X k) (xn I X k) := by
    intro k ℓ hℓ u hu
    have h := (hX.2 k).2.2 ℓ hℓ u hu
    have e : xt I X k ℓ = tailFrom (I.r k) (X k.val) ℓ := by
      funext t; simp [xt, hℓ, xo]
    rw [e]; exact h
  have hBI : ∀ k : Fin n, ∫ t in Ici (I.r k), (betaHat I.g' (xn I X k) t - betaHat I.g' (xt I X k) t)
      ≤ K * Δ k := fun k =>
    beta_increment_le I hJS h2 K hK (I.r k) (I.aliveOld (X k.val) k) (I.residual (X k.val) k) k
      (hknot k) (hAk' k) rfl (hρpos' k) (hkk k) (xt I X k) (xn I X k) (hold k).1 (hnewopt k)
      (hpost k)
  -- integrability of β̂
  have hBn : ∀ k : Fin n, IntegrableOn (betaHat I.g' (xn I X k)) (Ici (I.r k)) := fun k =>
    (BH_int I hJS _ _ _ (hAk k) _ (hnewopt k).1).1
  have hBo : ∀ k : Fin n, IntegrableOn (betaHat I.g' (xt I X k)) (Ici (I.r k)) := fun k =>
    (BH_int I hJS _ _ _ (hAk' k) _ (hold k).1.1).1
  have hxoxt : ∀ k : Fin n, ∀ t, betaHat I.g' (xo I X k) t = betaHat I.g' (xt I X k) t := by
    intro k t
    apply bh_ae
    intro ℓ
    by_cases hℓ : ℓ ∈ I.aliveOld (X k.val) k
    · exact Filter.Eventually.of_forall (fun τ => by simp [xt, hℓ])
    · filter_upwards [(hold k).2 ℓ hℓ] with τ hτ
      simp [xt, hℓ, hτ]
  -- cost decomposition
  set P : Fin n → ℝ≥0∞ := fun k =>
    ∑ j, ∫⁻ t in Iio (I.r k), ENNReal.ofReal (I.g j t * X (k.val + 1) j t) with hPdef
  have hcost : ∀ k : Fin n, I.cost (X (k.val + 1)) = P k + offCost I.g (xn I X k) ∧
      I.cost (X k.val) = P k + offCost I.g (xt I X k) := by
    intro k
    obtain ⟨hbef, _, _⟩ := hX.2 k
    constructor
    · simp only [Instance.cost, offCost, hPdef, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [lint_split _ (I.r k)]
      congr 1
      rw [show xn I X k = tailFrom (I.r k) (X (k.val + 1)) from rfl, lint_tail]
    · simp only [Instance.cost, offCost, hPdef, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [lint_split _ (I.r k)]
      congr 1
      · apply setLIntegral_congr_fun measurableSet_Iio
        intro t ht; dsimp only; rw [hbef j t (mem_Iio.1 ht)]
      · rw [← lint_tail]
        apply lintegral_congr_ae
        by_cases hj : j ∈ I.aliveOld (X k.val) k
        · exact Filter.Eventually.of_forall (fun t => by simp [xt, hj, xo])
        · filter_upwards [(hold k).2 j hj] with t ht
          have ht' : tailFrom (I.r k) (X k.val) j t = 0 := by simpa [xo] using ht
          simp [xt, hj, ht']
  have hCf : ∀ i, i ≤ n → I.cost (X i) ≠ ⊤ := by
    intro i
    induction i with
    | zero => intro _; rw [hX.1]; simp [Instance.cost, offCost]
    | succ i ih =>
      intro hi
      have hk := hcost ⟨i, by omega⟩
      simp only at hk
      rw [hk.1]
      have hPf : P ⟨i, by omega⟩ ≠ ⊤ := by
        have := ih (by omega)
        rw [hk.2] at this
        exact (ENNReal.add_ne_top.1 this).1
      exact ENNReal.add_ne_top.2 ⟨hPf, hfin _⟩
  set C : ℕ → ℝ := fun i => (I.cost (X i)).toReal with hCdef
  have hstep : ∀ k : Fin n, C (k.val + 1) - C k.val = Δ k := by
    intro k
    have hk := hcost k
    have hPf : P k ≠ ⊤ := by
      have := hCf k.val k.isLt.le
      rw [hk.2] at this
      exact (ENNReal.add_ne_top.1 this).1
    simp only [hCdef, hΔdef]
    rw [hk.1, hk.2, ENNReal.toReal_add hPf (hfin k), ENNReal.toReal_add hPf (hfino k)]
    ring
  have hC0 : C 0 = 0 := by simp [hCdef, hX.1, Instance.cost, offCost]
  have hCn : C n = ∑ k, Δ k := by
    have : ∑ k : Fin n, Δ k = ∑ k : Fin n, (fun i => C (i + 1) - C i) k.val :=
      Finset.sum_congr rfl (fun k _ => (hstep k).symm)
    rw [this, Fin.sum_univ_eq_sum_range (fun i => C (i + 1) - C i) n,
      Finset.sum_range_sub, hC0, sub_zero]
  -- β̂ telescoping
  set b : Fin n → ℝ → ℝ := fun k => betaHat I.g' (X (k.val + 1)) with hbdef
  have hb_eq : ∀ k : Fin n, ∀ t, I.r k ≤ t → b k t = betaHat I.g' (xn I X k) t :=
    fun k t ht => (bh_tail I.g' (I.r k) (X (k.val + 1)) t ht).symm
  have hbint : ∀ k : Fin n, IntegrableOn (b k) (Ici (I.r k)) := fun k =>
    (hBn k).congr_fun (fun t ht => (hb_eq k t (mem_Ici.1 ht)).symm) measurableSet_Ici
  have hBnk : ∀ k : Fin n, ∫ t in Ici (I.r k), b k t = ∫ t in Ici (I.r k), betaHat I.g' (xn I X k) t :=
    fun k => setIntegral_congr_fun measurableSet_Ici (fun t ht => hb_eq k t (mem_Ici.1 ht))
  set O : ℕ → ℝ := fun i => if h : i < n then
    ∫ t in Ici (I.r ⟨i, h⟩), betaHat I.g' (xt I X ⟨i, h⟩) t else 0 with hOdef
  have hsegm : ∀ k : Fin n, MeasurableSet (I.segment k) := by
    intro k; rw [seg_eq I hI.2 k]; split_ifs
    · exact measurableSet_Ici.diff measurableSet_Ici
    · exact measurableSet_Ici.diff MeasurableSet.empty
  have hsegsub : ∀ k : Fin n, I.segment k ⊆ Ici (I.r k) := fun k t ht => mem_Ici.2 ht.1
  have hseg : ∀ k : Fin n, ∫ t in I.segment k, b k t =
      (∫ t in Ici (I.r k), betaHat I.g' (xn I X k) t) - O (k.val + 1) := by
    intro k
    rw [seg_eq I hI.2 k]
    split_ifs with h
    · set k' : Fin n := ⟨k.val + 1, h⟩
      have hkk' : k ≤ k' := by rw [Fin.le_def]; simp [k']
      rw [setIntegral_sdiff measurableSet_Ici (hbint k) (Ici_subset_Ici.2 (hI.2 hkk')), hBnk k]
      congr 1
      simp only [hOdef, dif_pos h]
      apply setIntegral_congr_fun measurableSet_Ici
      intro t ht
      simp only [hbdef]
      rw [← hxoxt k' t]
      exact (bh_tail I.g' (I.r k') (X (k.val + 1)) t (mem_Ici.1 ht)).symm
    · rw [diff_empty, hBnk k]
      simp [hOdef, h]
  have hconcat : ∫ t in Ici 0, I.concatDual b t = ∑ k : Fin n, ∫ t in I.segment k, b k t := by
    unfold Instance.concatDual
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl; intro k _
      rw [setIntegral_indicator (hsegm k)]
      rw [inter_eq_right.2 ((hsegsub k).trans (Ici_subset_Ici.2 (hJS k).2.1))]
    · intro k _
      exact (((hbint k).mono_set (hsegsub k)).integrable_indicator (hsegm k)).integrableOn
  have hO0 : O 0 = 0 := by
    simp only [hOdef]
    split_ifs with h
    · have hz : ∀ t, betaHat I.g' (xt I X ⟨0, h⟩) t = 0 := by
        intro t
        have : xt I X ⟨0, h⟩ = 0 := by
          funext j τ
          have : j ∉ I.aliveOld (X 0) ⟨0, h⟩ := by
            intro hj; have := (mem_aliveOld.1 hj).1; rw [Fin.lt_def] at this; simp at this
          simp [xt, this]
        rw [this]; simp [betaHat]
      simp [hz]
    · rfl
  have hOn : O n = 0 := by simp [hOdef]
  have htele : ∑ k : Fin n, O (k.val + 1) = ∑ k : Fin n, O k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun i => O (i + 1)) n, Fin.sum_univ_eq_sum_range O n]
    have h1 := Finset.sum_range_succ' O n
    have h2 := Finset.sum_range_succ O n
    rw [hO0, add_zero] at h1
    rw [hOn, add_zero] at h2
    rw [← h1, h2]
  have hOk : ∀ k : Fin n, O k.val = ∫ t in Ici (I.r k), betaHat I.g' (xt I X k) t := by
    intro k; simp [hOdef, k.isLt]
  have hBeta : ∫ t in Ici 0, I.concatDual b t = ∑ k : Fin n,
      ∫ t in Ici (I.r k), (betaHat I.g' (xn I X k) t - betaHat I.g' (xt I X k) t) := by
    rw [hconcat]
    simp_rw [hseg]
    rw [Finset.sum_sub_distrib, htele]
    simp_rw [hOk]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [integral_sub (hBn k) (hBo k)]
  -- final
  have hfeasD := betahat_dual_feasible I hI X hX Ad Bd hAB
  have hpos : 0 < 1 + ε := by linarith
  have hc : 0 < 1 / (1 + ε) := by positivity
  have wd := weak_duality_21 I hI _ _ hfeasD (1 / (1 + ε)) hc
  set SB := ∑ k : Fin n,
      ∫ t in Ici (I.r k), (betaHat I.g' (xn I X k) t - betaHat I.g' (xt I X k) t) with hSB
  set SD := ∑ k : Fin n, Δ k with hSD
  set SA := ∑ k : Fin n, Ad k k * I.v k with hSA
  have hSAD : SD ≤ SA := Finset.sum_le_sum (fun k _ => hΔ k)
  have hSBD : SB ≤ K * SD := by
    rw [hSD, Finset.mul_sum]; exact Finset.sum_le_sum (fun k _ => hBI k)
  have hD : I.dualObj (1 / (1 + ε)) (fun k => Ad k k) (I.concatDual b) = SA - 1 / (1 + ε) * SB := by
    unfold Instance.dualObj
    rw [hBeta]
  rw [hD] at wd
  set R := (1 + ε) / (1 + ε - K) with hR
  have hRpos : 0 < R := div_pos hpos (by linarith)
  have hR1 : R * (1 - 1 / (1 + ε) * K) = 1 := by
    have : (1 + ε - K) ≠ 0 := by linarith
    rw [hR]; field_simp
  have hmain : C n ≤ R * (SA - 1 / (1 + ε) * SB) := by
    have h1 : SD - 1 / (1 + ε) * (K * SD) ≤ SA - 1 / (1 + ε) * SB := by
      have := mul_le_mul_of_nonneg_left hSBD hc.le
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hRpos.le
    have h3 : R * (SD - 1 / (1 + ε) * (K * SD)) = SD := by
      calc R * (SD - 1 / (1 + ε) * (K * SD)) = R * (1 - 1 / (1 + ε) * K) * SD := by ring
        _ = SD := by rw [hR1, one_mul]
    rw [hCn]; linarith
  unfold Instance.algCost
  rw [← ENNReal.ofReal_toReal (hCf n le_rfl)]
  calc ENNReal.ofReal (I.cost (X n)).toReal = ENNReal.ofReal (C n) := rfl
    _ ≤ ENNReal.ofReal (R * (SA - 1 / (1 + ε) * SB)) := ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal R * ENNReal.ofReal (SA - 1 / (1 + ε) * SB) := ENNReal.ofReal_mul hRpos.le
    _ ≤ ENNReal.ofReal R * I.optLP (1 / (1 + ε)) := by gcongr
