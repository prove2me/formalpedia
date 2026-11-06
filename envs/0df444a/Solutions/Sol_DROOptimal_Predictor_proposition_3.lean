-- Prove2me | solution 1 for DROOptimal.Predictor.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:49:42.997864+00:00
-- url     : https://prove2.me/submissions/2b6d8472-1530-4675-8a09-64b113480d52

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Theorems.Thm_DROOptimal_Predictor_eq_15

open DROOptimal.Predictor Filter Topology

namespace DROm4P3

lemma coord_cont {d : ℕ} (i : Fin d) : Continuous (fun q : Δ d => (q : Fin d → ℝ) i) :=
  (continuous_apply i).comp continuous_subtype_val

lemma coord_nonneg {d : ℕ} (q : Δ d) (i : Fin d) : 0 ≤ (q : Fin d → ℝ) i := q.2.1 i

lemma coord_le_one {d : ℕ} (q : Δ d) (i : Fin d) : (q : Fin d → ℝ) i ≤ 1 := by
  have := Finset.single_le_sum (fun j _ => q.2.1 j) (Finset.mem_univ i)
  rw [q.2.2] at this; exact this

lemma coord_sum {d : ℕ} (q : Δ d) : ∑ i, (q : Fin d → ℝ) i = 1 := q.2.2

/-- a log(a/b) ≥ a − b. -/
lemma mul_log_div_ge_sub (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hb)
    rw [inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : a * (b / a) = b := by field_simp
    rw [mul_sub, mul_one, h3] at h2
    exact h2

lemma mul_log_div_eq (a b : ℝ) (hb : b ≠ 0) :
    a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  rcases eq_or_ne a 0 with h | h
  · subst h; simp
  · rw [Real.log_div h hb]; ring

lemma mul_le_abs (a t : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : a * t ≤ |t| := by
  nlinarith [le_abs_self t, abs_nonneg t, neg_abs_le t]

/-- Joint lower semicontinuity of the relative entropy on 𝒫 × 𝒫. -/
lemma relEntropy_lsc {d : ℕ} :
    LowerSemicontinuous (fun pq : Δ d × Δ d => relEntropy pq.1 pq.2) := by
  classical
  rintro ⟨p, q⟩ y hy
  change y < relEntropy p q at hy
  have c1 : ∀ i, Continuous (fun pq : Δ d × Δ d => (pq.1 : Fin d → ℝ) i) :=
    fun i => (coord_cont i).comp continuous_fst
  have c2 : ∀ i, Continuous (fun pq : Δ d × Δ d => (pq.2 : Fin d → ℝ) i) :=
    fun i => (coord_cont i).comp continuous_snd
  by_cases hc : ∀ i, (q : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0
  · let G : Δ d × Δ d → ℝ := fun pq => ∑ i,
      if (q : Fin d → ℝ) i = 0 then (pq.1 : Fin d → ℝ) i - (pq.2 : Fin d → ℝ) i
      else (pq.1 : Fin d → ℝ) i * Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i)
    have hGeq : relEntropy p q = (G (p, q) : EReal) := by
      simp only [relEntropy, if_pos hc, G]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs with h
      · simp [h, hc i h]
      · rfl
    have hGc : ContinuousAt G (p, q) := by
      refine tendsto_finsetSum _ (fun i _ => ?_)
      by_cases h : (q : Fin d → ℝ) i = 0
      · simp only [if_pos h]
        exact ((c1 i).continuousAt (x := (p, q))).sub ((c2 i).continuousAt (x := (p, q)))
      · simp only [if_neg h]
        have hq : 0 < (q : Fin d → ℝ) i := lt_of_le_of_ne (coord_nonneg q i) (Ne.symm h)
        have hev : (fun pq : Δ d × Δ d => (pq.1 : Fin d → ℝ) i * Real.log ((pq.1 : Fin d → ℝ) i /
            (pq.2 : Fin d → ℝ) i)) =ᶠ[𝓝 (p, q)] (fun pq => (pq.1 : Fin d → ℝ) i *
            Real.log ((pq.1 : Fin d → ℝ) i) - (pq.1 : Fin d → ℝ) i *
            Real.log ((pq.2 : Fin d → ℝ) i)) := by
          filter_upwards [(c2 i).continuousAt.eventually (lt_mem_nhds hq)] with pq hpq
          exact mul_log_div_eq _ _ hpq.ne'
        refine ContinuousAt.congr ?_ hev.symm
        exact (Real.continuous_mul_log.comp (c1 i)).continuousAt.sub
          ((c1 i).continuousAt.mul ((c2 i).continuousAt.log hq.ne'))
    rw [hGeq] at hy
    obtain ⟨R, hyR, hRG⟩ := EReal.lt_iff_exists_real_btwn.mp hy
    have hRG' : R < G (p, q) := by exact_mod_cast hRG
    filter_upwards [hGc.eventually (lt_mem_nhds hRG')] with pq hpq
    change y < relEntropy pq.1 pq.2
    by_cases hc' : ∀ i, (pq.2 : Fin d → ℝ) i = 0 → (pq.1 : Fin d → ℝ) i = 0
    · simp only [relEntropy, if_pos hc']
      refine lt_of_lt_of_le hyR ?_
      have hle : G pq ≤ ∑ i, (pq.1 : Fin d → ℝ) i *
          Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        split_ifs with h
        · rcases (coord_nonneg pq.2 i).eq_or_lt with h2 | h2
          · rw [← h2, hc' i h2.symm]; simp
          · exact mul_log_div_ge_sub _ _ (coord_nonneg pq.1 i) h2
        · exact le_rfl
      exact_mod_cast (hpq.le.trans hle)
    · simp only [relEntropy, if_neg hc']
      exact lt_of_lt_of_le hyR le_top
  · push Not at hc
    obtain ⟨j, hqj, hpj⟩ := hc
    have hpj' : 0 < (p : Fin d → ℝ) j := lt_of_le_of_ne (coord_nonneg p j) (Ne.symm hpj)
    obtain ⟨R, hR⟩ : ∃ R : ℝ, y ≤ (R : EReal) := by
      induction y using EReal.rec with
      | bot => exact ⟨0, bot_le⟩
      | coe a => exact ⟨a, le_rfl⟩
      | top => exact absurd hy (not_lt.mpr le_top)
    set A : ℝ := |R| + d + 1 with hAdef
    have hA : 0 ≤ A := by positivity
    set h2 : ℝ := (p : Fin d → ℝ) j / 2 with hh2def
    have hh2 : 0 < h2 := by positivity
    set δ : ℝ := h2 * Real.exp (-(A / h2)) with hδdef
    have hδ : 0 < δ := mul_pos hh2 (Real.exp_pos _)
    have ev1 : ∀ᶠ pq : Δ d × Δ d in 𝓝 (p, q), (pq.2 : Fin d → ℝ) j < δ :=
      (c2 j).continuousAt.eventually (gt_mem_nhds (by simpa [hqj] using hδ))
    have ev2 : ∀ᶠ pq : Δ d × Δ d in 𝓝 (p, q), h2 < (pq.1 : Fin d → ℝ) j :=
      (c1 j).continuousAt.eventually (lt_mem_nhds (by
        change (p : Fin d → ℝ) j / 2 < (p : Fin d → ℝ) j; linarith))
    filter_upwards [ev1, ev2] with pq hq' hp'
    change y < relEntropy pq.1 pq.2
    by_cases hc' : ∀ i, (pq.2 : Fin d → ℝ) i = 0 → (pq.1 : Fin d → ℝ) i = 0
    · simp only [relEntropy, if_pos hc']
      refine lt_of_le_of_lt hR ?_
      have hqj' : 0 < (pq.2 : Fin d → ℝ) j :=
        lt_of_le_of_ne (coord_nonneg _ j) (fun h => (ne_of_gt (hh2.trans hp')) (hc' j h.symm))
      have hterm : ∀ i, -1 ≤ (pq.1 : Fin d → ℝ) i *
          Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) := by
        intro i
        rcases (coord_nonneg pq.2 i).eq_or_lt with h | h
        · rw [← h, hc' i h.symm]; simp
        · have := mul_log_div_ge_sub _ _ (coord_nonneg pq.1 i) h
          linarith [coord_nonneg pq.1 i, coord_le_one pq.2 i]
      have hj : A ≤ (pq.1 : Fin d → ℝ) j *
          Real.log ((pq.1 : Fin d → ℝ) j / (pq.2 : Fin d → ℝ) j) := by
        have hratio : h2 / δ ≤ (pq.1 : Fin d → ℝ) j / (pq.2 : Fin d → ℝ) j := by
          rw [div_le_div_iff₀ hδ hqj']
          nlinarith
        have hlog : Real.log (h2 / δ) = A / h2 := by
          rw [hδdef, div_mul_eq_div_div, div_self hh2.ne', one_div, Real.log_inv,
            Real.log_exp, neg_neg]
        have hl : A / h2 ≤ Real.log ((pq.1 : Fin d → ℝ) j / (pq.2 : Fin d → ℝ) j) :=
          hlog ▸ Real.log_le_log (div_pos hh2 hδ) hratio
        calc A = h2 * (A / h2) := by field_simp
          _ ≤ (pq.1 : Fin d → ℝ) j * (A / h2) :=
              mul_le_mul_of_nonneg_right hp'.le (div_nonneg hA hh2.le)
          _ ≤ _ := mul_le_mul_of_nonneg_left hl (by linarith)
      have hsum := Finset.single_le_sum (f := fun i =>
          (pq.1 : Fin d → ℝ) i * Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) + 1)
        (fun i _ => by linarith [hterm i]) (Finset.mem_univ j)
      rw [Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at hsum
      have : R < ∑ i, (pq.1 : Fin d → ℝ) i *
          Real.log ((pq.1 : Fin d → ℝ) i / (pq.2 : Fin d → ℝ) i) := by
        have := le_abs_self R
        linarith
      exact_mod_cast this
    · simp only [relEntropy, if_neg hc']
      exact lt_of_le_of_lt hR (EReal.coe_lt_top R)

lemma relEntropy_self {d : ℕ} (p : Δ d) : relEntropy p p = 0 := by
  classical
  have hc : ∀ i, (p : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0 := fun _ h => h
  simp only [relEntropy, if_pos hc]
  have : ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (p : Fin d → ℝ) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : (p : Fin d → ℝ) i = 0
    · simp [h]
    · simp [div_self h]
  rw [this]; rfl

/-- Gibbs: I(p, q) ≤ 0 forces q = p. -/
lemma gibbs_eq {d : ℕ} (p q : Δ d) (h : relEntropy p q ≤ ((0 : ℝ) : EReal)) : q = p := by
  classical
  unfold relEntropy at h
  split_ifs at h with hc
  · have hs : ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q : Fin d → ℝ) i) ≤ 0 := by
      exact_mod_cast h
    set t : Fin d → ℝ := fun i => (p : Fin d → ℝ) i *
      Real.log ((p : Fin d → ℝ) i / (q : Fin d → ℝ) i) - ((p : Fin d → ℝ) i - (q : Fin d → ℝ) i)
      with htdef
    have ht0 : ∀ i, 0 ≤ t i := by
      intro i
      rcases (coord_nonneg q i).eq_or_lt with h2 | h2
      · simp only [htdef]; rw [← h2, hc i h2.symm]; simp
      · simp only [htdef]; linarith [mul_log_div_ge_sub _ _ (coord_nonneg p i) h2]
    have hsum : ∑ i, t i =
        ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q : Fin d → ℝ) i) := by
      simp only [htdef, Finset.sum_sub_distrib, coord_sum]; ring
    have hall : ∀ i, t i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ht0 i)).mp
        (le_antisymm (hsum ▸ hs) (Finset.sum_nonneg (fun i _ => ht0 i)))
      exact fun i => this i (Finset.mem_univ i)
    apply Subtype.ext; funext i
    change (q : Fin d → ℝ) i = (p : Fin d → ℝ) i
    have hti := hall i
    simp only [htdef] at hti
    rcases (coord_nonneg q i).eq_or_lt with h2 | h2
    · rw [← h2, hc i h2.symm]
    · rcases (coord_nonneg p i).eq_or_lt with h3 | h3
      · rw [← h3] at hti; simp at hti; linarith
      · by_contra hne
        set z := (q : Fin d → ℝ) i / (p : Fin d → ℝ) i with hzdef
        have hz : 0 < z := div_pos h2 h3
        have hz1 : z ≠ 1 := fun h => hne ((div_eq_one_iff_eq h3.ne').mp h)
        have hlt := Real.log_lt_sub_one_of_pos hz hz1
        have hl : Real.log ((p : Fin d → ℝ) i / (q : Fin d → ℝ) i) = - Real.log z := by
          rw [← Real.log_inv, inv_div]
        rw [hl] at hti
        have hq : (q : Fin d → ℝ) i = (p : Fin d → ℝ) i * z := by
          rw [hzdef]; field_simp
        have h4 := mul_lt_mul_of_pos_left hlt h3
        rw [mul_sub, mul_one, ← hq] at h4
        linarith
  · exact absurd h (not_le.mpr (EReal.coe_lt_top 0))

lemma cost_cont {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (x : ↥X) :
    Continuous (fun P : Δ d => cost γ x P) := by
  unfold cost
  exact continuous_finsetSum _ (fun i _ => (coord_cont i).mul continuous_const)

lemma cost_le_abs {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (x : ↥X)
    (P : Δ d) : cost γ x P ≤ ∑ i, |γ x i| := by
  unfold cost
  exact Finset.sum_le_sum (fun i _ => mul_le_abs _ _ (coord_nonneg P i) (coord_le_one P i))

lemma cost_diff {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (x y : ↥X)
    (P : Δ d) : cost γ x P ≤ cost γ y P + ∑ i, |γ x i - γ y i| := by
  unfold cost
  have : ∑ i, (P : Fin d → ℝ) i * γ x i - ∑ i, (P : Fin d → ℝ) i * γ y i ≤
      ∑ i, |γ x i - γ y i| := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← mul_sub]
    exact mul_le_abs _ _ (coord_nonneg P i) (coord_le_one P i)
  linarith

end DROm4P3

open DROm4P3 in
theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) :
    IsPredictor (drPredictor γ r) := by
  classical
  have : CompactSpace (Δ d) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin d))
  set S : Δ d → Set (Δ d) := fun P' => {P : Δ d | relEntropy P' P ≤ (r : EReal)} with hSdef
  have hFdef : ∀ x P', drPredictor γ r x P' = sSup ((fun P => cost γ x P) '' S P') :=
    fun _ _ => rfl
  have self_mem : ∀ P', P' ∈ S P' := fun P' => by
    change relEntropy P' P' ≤ _; rw [relEntropy_self]; exact_mod_cast hr
  have hbdd : ∀ x P', BddAbove ((fun P => cost γ x P) '' S P') := by
    intro x P'
    refine ⟨∑ i, |γ x i|, ?_⟩
    rintro _ ⟨P, _, rfl⟩
    exact cost_le_abs γ x P
  have le_F : ∀ x P' P, P ∈ S P' → cost γ x P ≤ drPredictor γ r x P' := fun x P' P hP => by
    rw [hFdef]; exact le_csSup (hbdd x P') ⟨P, hP, rfl⟩
  have F_le : ∀ x P' (b : ℝ), (∀ P ∈ S P', cost γ x P ≤ b) → drPredictor γ r x P' ≤ b := by
    intro x P' b h
    rw [hFdef]
    exact csSup_le ((Set.nonempty_of_mem (self_mem P')).image _)
      (by rintro _ ⟨P, hP, rfl⟩; exact h P hP)
  have xlip : ∀ x y P', drPredictor γ r x P' ≤ drPredictor γ r y P' + ∑ i, |γ x i - γ y i| := by
    intro x y P'
    apply F_le
    intro P hP
    have := le_F y P' P hP
    linarith [cost_diff γ x y P]
  have hclosed : IsClosed {pq : Δ d × Δ d | relEntropy pq.1 pq.2 ≤ (r : EReal)} :=
    relEntropy_lsc.isClosed_preimage _
  -- continuity in ℙ' for a fixed decision
  have cont_snd : ∀ x (P0 : Δ d), ContinuousAt (fun P' => drPredictor γ r x P') P0 := by
    intro x P0
    rw [ContinuousAt, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rcases hr.eq_or_lt with h0 | hpos
      · -- r = 0
        have hF0 : drPredictor γ r x P0 ≤ cost γ x P0 := by
          apply F_le
          intro P hP
          have hP' : relEntropy P0 P ≤ ((0 : ℝ) : EReal) := by rw [h0]; exact hP
          rw [gibbs_eq P0 P hP']
        filter_upwards [(cost_cont γ x).continuousAt.eventually
          (lt_mem_nhds (lt_of_lt_of_le ha hF0))] with P' hP'
        exact lt_of_lt_of_le hP' (le_F x P' P' (self_mem P'))
      · -- r > 0: a maximiser, then display (15)
        have hSc : IsClosed (S P0) :=
          hclosed.preimage (continuous_const.prodMk continuous_id)
        obtain ⟨P₀, hmem, hmax⟩ := hSc.isCompact.exists_isMaxOn ⟨P0, self_mem P0⟩
          (cost_cont γ x).continuousOn
        have hopt : drPredictor γ r x P0 = cost γ x P₀ :=
          le_antisymm (F_le x P0 _ (fun P hP => hmax hP)) (le_F x P0 P₀ hmem)
        obtain ⟨P₂, hpos2, hI2, hc2⟩ := DROOptimal.Predictor.eq_15 X hX γ hγ r hpos x P0 P₀
          hmem hopt (drPredictor γ r x P0 - a) (by linarith)
        -- I(·, ℙ₂) is continuous since ℙ₂ > 0
        set g : Δ d → ℝ := fun P' => ∑ i, (P' : Fin d → ℝ) i *
          Real.log ((P' : Fin d → ℝ) i / (P₂ : Fin d → ℝ) i) with hgdef
        have hg : ∀ P', relEntropy P' P₂ = (g P' : EReal) := by
          intro P'
          have hc : ∀ i, (P₂ : Fin d → ℝ) i = 0 → (P' : Fin d → ℝ) i = 0 :=
            fun i h => absurd h (hpos2 i).ne'
          simp only [relEntropy, if_pos hc, hgdef]
        have hgc : Continuous g := by
          refine continuous_finsetSum _ (fun i _ => ?_)
          have : (fun P' : Δ d => (P' : Fin d → ℝ) i *
              Real.log ((P' : Fin d → ℝ) i / (P₂ : Fin d → ℝ) i)) =
              (fun P' : Δ d => (P' : Fin d → ℝ) i * Real.log ((P' : Fin d → ℝ) i) -
                (P' : Fin d → ℝ) i * Real.log ((P₂ : Fin d → ℝ) i)) := by
            funext P'; exact mul_log_div_eq _ _ (hpos2 i).ne'
          rw [this]
          exact (Real.continuous_mul_log.comp (coord_cont i)).sub
            ((coord_cont i).mul continuous_const)
        have hgr : g P0 < r := by
          have := hI2; rw [hg] at this; exact_mod_cast this
        filter_upwards [hgc.continuousAt.eventually (gt_mem_nhds hgr)] with P' hP'
        have hmem2 : P₂ ∈ S P' := by
          change relEntropy P' P₂ ≤ _; rw [hg]; exact_mod_cast hP'.le
        have := le_F x P' P₂ hmem2
        linarith
    · by_contra hcon
      rw [not_eventually] at hcon
      obtain ⟨u, hu, hua⟩ := exists_seq_forall_of_frequently hcon
      set b := (drPredictor γ r x P0 + a) / 2 with hb
      have hex : ∀ k, ∃ P, P ∈ S (u k) ∧ b < cost γ x P := by
        intro k
        have h1 : b < drPredictor γ r x (u k) := by
          have := hua k; push Not at this; linarith
        rw [hFdef] at h1
        obtain ⟨_, ⟨P, hP, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup
          ((Set.nonempty_of_mem (self_mem (u k))).image _) h1
        exact ⟨P, hP, hlt⟩
      choose v hv hvb using hex
      obtain ⟨Pstar, -, φ, hφ, hlim⟩ :=
        isCompact_univ.tendsto_subseq (fun k => Set.mem_univ (v k))
      have hjoint : Tendsto (fun k => (u (φ k), v (φ k))) atTop (𝓝 (P0, Pstar)) :=
        (hu.comp hφ.tendsto_atTop).prodMk_nhds hlim
      have hmem : relEntropy P0 Pstar ≤ (r : EReal) :=
        hclosed.mem_of_tendsto hjoint (Eventually.of_forall (fun k => hv (φ k)))
      have h1 : cost γ x Pstar ≤ drPredictor γ r x P0 := le_F x P0 Pstar hmem
      have h2 : b ≤ cost γ x Pstar :=
        ge_of_tendsto ((cost_cont γ x).continuousAt.tendsto.comp hlim)
          (Eventually.of_forall (fun k => (hvb (φ k)).le))
      linarith
  -- joint continuity
  unfold IsPredictor
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, P0⟩
  have key : ∀ x P', |drPredictor γ r x P' - drPredictor γ r x0 P'| ≤
      ∑ i, |γ x i - γ x0 i| := by
    intro x P'
    have hsym : ∑ i, |γ x0 i - γ x i| = ∑ i, |γ x i - γ x0 i| :=
      Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
    rw [abs_sub_le_iff]
    constructor
    · linarith [xlip x x0 P']
    · linarith [xlip x0 x P']
  have h1 : Tendsto (fun q : ↥X × Δ d => drPredictor γ r q.1 q.2 - drPredictor γ r x0 q.2)
      (𝓝 (x0, P0)) (𝓝 0) := by
    have hc : Continuous (fun q : ↥X × Δ d => ∑ i, |γ q.1 i - γ x0 i|) :=
      continuous_finsetSum _ (fun i _ => (((hγ i).comp continuous_fst).sub continuous_const).abs)
    refine squeeze_zero_norm (fun q => (Real.norm_eq_abs _).le.trans (key q.1 q.2)) ?_
    simpa using hc.tendsto (x0, P0)
  have h2 : Tendsto (fun q : ↥X × Δ d => drPredictor γ r x0 q.2) (𝓝 (x0, P0))
      (𝓝 (drPredictor γ r x0 P0)) :=
    (cont_snd x0 P0).tendsto.comp continuousAt_snd
  have := h1.add h2
  simp only [sub_add_cancel, zero_add] at this
  exact this
