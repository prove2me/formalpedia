-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:33:39.255524+00:00
-- url     : https://prove2.me/submissions/7dad26fd-0ea5-4867-b4a1-6889aabc4134

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Theorems.Thm_CrossLearnCB_UCB1CL_lemma_3
import Theorems.Thm_CrossLearnCB_UCB1CL_lemma_4

open MeasureTheory ProbabilityTheory

namespace UCB1CLThm1Aux
open CrossLearnCB.UCB1CL

/-- Pathwise split (3) of the pseudo-regret into pre-regret, post-regret and the rounds with
gap below `Δmin`. -/
lemma split {K C : ℕ} (gap : Fin K → Fin C → ℝ) (G : Fin K → Fin C → Fin C → Prop)
    (ctx : ℕ → Fin C) (J : ℕ → Fin K) (T : ℕ) (Δmin : ℝ) :
    pseudoRegret gap ctx J T = regPre gap G ctx J T Δmin + regPost gap G ctx J T Δmin
      + ∑ t ∈ Finset.range T, (if gap (J t) (ctx t) < Δmin then gap (J t) (ctx t) else 0) := by
  classical
  unfold pseudoRegret regPre regPost
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h0 : Δmin ≤ gap (J t) (ctx t)
  · have h0' : ¬ gap (J t) (ctx t) < Δmin := not_lt.2 h0
    by_cases h1 : (obsCount G ctx J t (J t) (ctx t) : ℝ) ≤ mThr T (gap (J t) (ctx t))
    · have h1' : ¬ mThr T (gap (J t) (ctx t)) < (obsCount G ctx J t (J t) (ctx t) : ℝ) :=
        not_lt.2 h1
      simp only [h0, h1, h0', h1', and_self, and_false, if_true, if_false]; ring
    · have h1' : mThr T (gap (J t) (ctx t)) < (obsCount G ctx J t (J t) (ctx t) : ℝ) :=
        lt_of_not_ge h1
      simp only [h0, h1, h0', h1', and_self, and_false, if_true, if_false]; ring
  · have h0' : gap (J t) (ctx t) < Δmin := lt_of_not_ge h0
    simp only [h0, h0', false_and, if_true, if_false]; ring

/-- A real function of an arm sequence that only depends on the first `T` arms is measurable. -/
lemma measurable_of_dep {K : ℕ} [NeZero K] (T : ℕ) (f : (ℕ → Fin K) → ℝ)
    (hf : ∀ J J' : ℕ → Fin K, (∀ s < T, J s = J' s) → f J = f J') : Measurable f := by
  classical
  let ext : (Fin T → Fin K) → (ℕ → Fin K) := fun y s => if h : s < T then y ⟨s, h⟩ else 0
  let g : (Fin T → Fin K) → ℝ := fun y => f (ext y)
  have hg : Measurable g := measurable_of_countable g
  have hres : Measurable (fun J : ℕ → Fin K => fun s : Fin T => J s) :=
    measurable_pi_lambda _ (fun s => measurable_pi_apply _)
  have : f = g ∘ (fun J : ℕ → Fin K => fun s : Fin T => J s) := by
    funext J
    simp only [Function.comp, g]
    apply hf
    intro s hs
    simp [ext, hs]
  rw [this]
  exact hg.comp hres

lemma obsCount_congr {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J J' : ℕ → Fin K) (t : ℕ) (h : ∀ s < t, J s = J' s) (i : Fin K) (c : Fin C) :
    obsCount G ctx J t i c = obsCount G ctx J' t i c := by
  classical
  unfold obsCount
  congr 1
  apply Finset.filter_congr
  intro s hs
  rw [h s (Finset.mem_range.1 hs)]

lemma regPost_dep {K C : ℕ} (gap : Fin K → Fin C → ℝ) (G : Fin K → Fin C → Fin C → Prop)
    (ctx : ℕ → Fin C) (T : ℕ) (Δmin : ℝ) (J J' : ℕ → Fin K) (h : ∀ s < T, J s = J' s) :
    regPost gap G ctx J T Δmin = regPost gap G ctx J' T Δmin := by
  classical
  unfold regPost
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.1 ht
  rw [h t ht', obsCount_congr G ctx J J' t (fun s hs => h s (by omega))]

lemma regPost_le {K C : ℕ} (gap : Fin K → Fin C → ℝ) (hgap : ∀ i c, gap i c ∈ Set.Icc (0 : ℝ) 1)
    (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C) (T : ℕ) (Δmin : ℝ) (J : ℕ → Fin K) :
    |regPost gap G ctx J T Δmin| ≤ T := by
  classical
  have h0 : 0 ≤ regPost gap G ctx J T Δmin := by
    unfold regPost
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact (hgap _ _).1
    · exact le_refl 0
  rw [abs_of_nonneg h0]
  unfold regPost
  calc _ ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        split_ifs
        · exact (hgap _ _).2
        · norm_num
    _ = T := by simp

end UCB1CLThm1Aux

open CrossLearnCB.UCB1CL in
theorem solution {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) :
    (∀ Δs : ℝ, 0 < Δs → (∀ i c, 0 < gap P R i c → Δs ≤ gap P R i c) →
      ∫ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T ∂P
        ≤ 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δs + K * Real.pi ^ 2 / 3) ∧
    ∫ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T ∂P
      ≤ 17 * Real.sqrt (T * Real.log T * ∑ i, (cliqueCoverNumber (G i) : ℝ))
        + K * Real.pi ^ 2 / 3 := by
  classical
  -- means and gaps lie in [0, 1]
  have hmeasR : ∀ i c, Measurable (fun ω => R 0 ω i c) := fun i c =>
    (measurable_pi_apply c).comp ((measurable_pi_apply i).comp (hR.measurable 0))
  have hmu : ∀ i c, mu P R i c ∈ Set.Icc (0 : ℝ) 1 := by
    intro i c
    have hint : Integrable (fun ω => R 0 ω i c) P := by
      refine (integrable_const (1 : ℝ)).mono' (hmeasR i c).aestronglyMeasurable
        (ae_of_all _ (fun ω => ?_))
      have := hR.mem_Icc 0 ω i c
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
    constructor
    · exact integral_nonneg (fun ω => (hR.mem_Icc 0 ω i c).1)
    · unfold mu
      calc ∫ ω, R 0 ω i c ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
            integral_mono hint (integrable_const _) (fun ω => (hR.mem_Icc 0 ω i c).2)
        _ = 1 := by simp
  have hgap : ∀ i c, gap P R i c ∈ Set.Icc (0 : ℝ) 1 := by
    intro i c
    unfold gap muStar
    constructor
    · have := Finset.le_sup' (fun j => mu P R j c) (Finset.mem_univ i)
      linarith
    · have h1 : Finset.univ.sup' Finset.univ_nonempty (fun j => mu P R j c) ≤ 1 :=
        Finset.sup'_le _ _ (fun j _ => (hmu j c).2)
      linarith [(hmu i c).1]
  -- measurability of the arm process
  have hImeas : ∀ t, Measurable (I t) := by
    intro t
    refine (hI.adapted t).mono ?_ le_rfl
    apply Measurable.comap_le
    exact measurable_pi_lambda _ (fun s => hR.measurable s)
  have hJmeas : Measurable (fun ω => fun s => I s ω) := measurable_pi_lambda _ hImeas
  have hpost_int : ∀ Δmin : ℝ,
      Integrable (fun ω => regPost (gap P R) G ctx (fun s => I s ω) T Δmin) P := by
    intro Δmin
    have hm : Measurable (fun J : ℕ → Fin K => regPost (gap P R) G ctx J T Δmin) :=
      UCB1CLThm1Aux.measurable_of_dep T _ (UCB1CLThm1Aux.regPost_dep _ G ctx T Δmin)
    refine (integrable_const ((T : ℝ))).mono' (hm.comp hJmeas).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs]
    exact UCB1CLThm1Aux.regPost_le _ hgap G ctx T Δmin _
  have hpseudo_nonneg : ∀ ω, 0 ≤ pseudoRegret (gap P R) ctx (fun s => I s ω) T := by
    intro ω
    unfold pseudoRegret
    exact Finset.sum_nonneg (fun t _ => (hgap _ _).1)
  -- generic bound: for Δmin > 0 and a pathwise bound `B` on the small-gap rounds
  have hgen : ∀ Δmin : ℝ, 0 < Δmin → ∀ Bsmall : ℝ,
      (∀ J : ℕ → Fin K, ∑ t ∈ Finset.range T,
        (if gap P R (J t) (ctx t) < Δmin then gap P R (J t) (ctx t) else 0) ≤ Bsmall) →
      ∫ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T ∂P
        ≤ 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δmin + Bsmall
          + K * Real.pi ^ 2 / 3 := by
    intro Δmin hΔ Bsmall hB
    have h4 := CrossLearnCB.UCB1CL.lemma_4 P R hR G hG ctx T hT I hI Δmin hΔ
    set c3 := 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δmin
    have hpath : ∀ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T
        ≤ (c3 + Bsmall) + regPost (gap P R) G ctx (fun s => I s ω) T Δmin := by
      intro ω
      rw [UCB1CLThm1Aux.split (gap P R) G ctx (fun s => I s ω) T Δmin]
      have h3 := CrossLearnCB.UCB1CL.lemma_3 (gap P R) hgap G hG ctx (fun s => I s ω) T hT
        Δmin hΔ
      have hb := hB (fun s => I s ω)
      linarith
    calc ∫ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T ∂P
        ≤ ∫ ω, ((c3 + Bsmall) + regPost (gap P R) G ctx (fun s => I s ω) T Δmin) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ hpseudo_nonneg)
            ((integrable_const _).add (hpost_int Δmin)) (ae_of_all _ hpath)
      _ = (c3 + Bsmall) + ∫ ω, regPost (gap P R) G ctx (fun s => I s ω) T Δmin ∂P := by
          rw [integral_add (integrable_const _) (hpost_int Δmin)]
          simp
      _ ≤ c3 + Bsmall + K * Real.pi ^ 2 / 3 := by linarith
  refine ⟨?_, ?_⟩
  · -- gap-dependent bound with Δmin = Δs: the small-gap rounds have zero gap
    intro Δs hΔs hlow
    have := hgen Δs hΔs 0 (by
      intro J
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro t _
      split_ifs with h
      · rcases (hgap (J t) (ctx t)).1.lt_or_eq with hp | hp
        · exact absurd (hlow _ _ hp) (not_le.2 h)
        · exact hp.symm
      · rfl)
    linarith
  · -- gap-independent bound with Δmin = √(T log T Σκ) / T
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    have hlog : 0 < Real.log T := Real.log_pos (by exact_mod_cast (show 1 < T by omega))
    have hκ : ∀ i, 1 ≤ cliqueCoverNumber (G i) := by
      intro i
      have hne : {r : ℕ | ∃ f : Fin C → Fin r, ∀ u v, f u = f v → G i u v}.Nonempty :=
        ⟨C, id, fun u v h => by simp only [id] at h; subst h; exact hG i u⟩
      obtain ⟨f, _⟩ := Nat.sInf_mem hne
      have := (f 0).isLt
      unfold cliqueCoverNumber
      omega
    have hκsum : (1 : ℝ) ≤ ∑ i, (cliqueCoverNumber (G i) : ℝ) := by
      have h0 : (1 : ℝ) ≤ (cliqueCoverNumber (G 0) : ℝ) := by exact_mod_cast hκ 0
      have : (cliqueCoverNumber (G 0) : ℝ) ≤ ∑ i, (cliqueCoverNumber (G i) : ℝ) :=
        Finset.single_le_sum (f := fun i => (cliqueCoverNumber (G i) : ℝ))
          (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ 0)
      linarith
    set κs := ∑ i, (cliqueCoverNumber (G i) : ℝ)
    set Q := (T : ℝ) * Real.log T * κs with hQ
    have hQpos : 0 < Q := by positivity
    have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQpos
    have hsQ2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQpos.le
    set Δmin := Real.sqrt Q / T
    have hΔ : 0 < Δmin := by positivity
    have := hgen Δmin hΔ (T * Δmin) (by
      intro J
      calc _ ≤ ∑ _t ∈ Finset.range T, Δmin := by
            apply Finset.sum_le_sum
            intro t _
            split_ifs with h
            · exact h.le
            · exact hΔ.le
        _ = T * Δmin := by simp)
    have e1 : 16 * Real.log T * κs / Δmin = 16 * Real.sqrt Q := by
      simp only [Δmin]
      field_simp
      rw [hsQ2, hQ]; ring
    have e2 : (T : ℝ) * Δmin = Real.sqrt Q := by
      simp only [Δmin]; field_simp
    rw [e1, e2] at this
    linarith
