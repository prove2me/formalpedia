-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:31:30.442976+00:00
-- url     : https://prove2.me/submissions/019b1e4c-0bd1-4e05-87f5-8a244cedd9a2

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace UCB1CLEq4Aux
open CrossLearnCB.UCB1CL

/-- Successive pulls of arm `i` in contexts of `S` have strictly increasing `pullsIn` counts. -/
lemma pullsIn_lt {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) {t t' : ℕ} (htt : t < t') (hi : I t = i) (hS : ctx t ∈ S) :
    pullsIn ctx I t i S < pullsIn ctx I t' i S := by
  classical
  unfold pullsIn
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
    exact ⟨by omega, hs.2⟩
  · intro h
    have : t ∈ (Finset.range t').filter (fun s => I s = i ∧ ctx s ∈ S) := by
      simp [htt, hi, hS]
    have := h this
    simp at this

lemma pullsIn_injOn {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) (A : Finset ℕ) (hA : ∀ t ∈ A, I t = i ∧ ctx t ∈ S) :
    Set.InjOn (fun t => pullsIn ctx I t i S) A := by
  intro t ht t' ht' h
  simp only at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := pullsIn_lt ctx I i S hlt (hA t ht).1 (hA t ht).2
    omega
  · have := pullsIn_lt ctx I i S hlt (hA t' ht').1 (hA t' ht').2
    omega

/-- A set of pulls in `S` whose `pullsIn` count is at most `m ≥ 0` has at most `m + 1` rounds. -/
lemma card_le_of_pullsIn_le {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) (A : Finset ℕ) (hA : ∀ t ∈ A, I t = i ∧ ctx t ∈ S) (m : ℝ)
    (hm : 0 ≤ m) (hle : ∀ t ∈ A, (pullsIn ctx I t i S : ℝ) ≤ m) :
    (A.card : ℝ) ≤ m + 1 := by
  have hmaps : Set.MapsTo (fun t => pullsIn ctx I t i S) (A : Set ℕ)
      (Finset.range (⌊m⌋₊ + 1) : Set ℕ) := by
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    have := hle t ht
    have : pullsIn ctx I t i S ≤ ⌊m⌋₊ := Nat.le_floor this
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps (pullsIn_injOn ctx I i S A hA)
  simp only [Finset.card_range] at hcard
  have h1 : ((⌊m⌋₊ + 1 : ℕ) : ℝ) ≤ m + 1 := by
    push_cast
    linarith [Nat.floor_le hm]
  calc (A.card : ℝ) ≤ ((⌊m⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ m + 1 := h1

end UCB1CLEq4Aux

namespace UCB1CLLemma3Aux
open CrossLearnCB.UCB1CL

/-- `Σ_{j=0}^{N} 1/√(max j 1) ≤ 2√N` for `N ≥ 1`. -/
lemma sum_inv_sqrt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.range (N + 1), 1 / Real.sqrt (max (j : ℝ) 1) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      norm_num [Finset.sum_range_succ]
    · have ih := ih hpos
      rw [Finset.sum_range_succ]
      have hmax : max ((N + 1 : ℕ) : ℝ) 1 = (N : ℝ) + 1 := by
        push_cast
        exact max_eq_left (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
      rw [hmax]
      push_cast
      set a := Real.sqrt ((N : ℝ) + 1)
      set b := Real.sqrt (N : ℝ)
      have ha2 : a ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hb2 : b ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
      have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
      have hb : 0 ≤ b := Real.sqrt_nonneg _
      have key : 1 / a ≤ 2 * a - 2 * b := by
        rw [div_le_iff₀ ha]
        nlinarith [sq_nonneg (a - b)]
      linarith

/-- Block bound: the regret of pulls of one arm in one clique-like set `S`, each with
`pullsIn ≤ N` and gap at most `√L / √(max pullsIn 1)`, is at most `2 √L √N`. -/
lemma block_bound {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) (A : Finset ℕ) (hA : ∀ t ∈ A, I t = i ∧ ctx t ∈ S)
    (v : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (N : ℕ) (hN : 1 ≤ N)
    (hk : ∀ t ∈ A, pullsIn ctx I t i S ≤ N)
    (hv : ∀ t ∈ A, v t ≤ Real.sqrt L / Real.sqrt (max (pullsIn ctx I t i S : ℝ) 1)) :
    ∑ t ∈ A, v t ≤ 2 * Real.sqrt L * Real.sqrt N := by
  classical
  set h : ℕ → ℝ := fun j => Real.sqrt L / Real.sqrt (max (j : ℝ) 1)
  have hh0 : ∀ j, 0 ≤ h j := fun j => by positivity
  calc ∑ t ∈ A, v t ≤ ∑ t ∈ A, h (pullsIn ctx I t i S) := Finset.sum_le_sum hv
    _ = ∑ j ∈ A.image (fun t => pullsIn ctx I t i S), h j := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact UCB1CLEq4Aux.pullsIn_injOn ctx I i S A hA hx hy hxy
    _ ≤ ∑ j ∈ Finset.range (N + 1), h j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_image] at hj
          obtain ⟨t, ht, rfl⟩ := hj
          simp only [Finset.mem_range]
          have := hk t ht
          omega
        · intro j _ _; exact hh0 j
    _ = Real.sqrt L * ∑ j ∈ Finset.range (N + 1), 1 / Real.sqrt (max (j : ℝ) 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [h]
        ring
    _ ≤ Real.sqrt L * (2 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N hN) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt L * Real.sqrt N := by ring

end UCB1CLLemma3Aux

open CrossLearnCB.UCB1CL in
theorem solution {K C : ℕ} (gap : Fin K → Fin C → ℝ) (hgap : ∀ i c, gap i c ∈ Set.Icc (0 : ℝ) 1)
    (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G) (ctx : ℕ → Fin C) (I : ℕ → Fin K)
    (T : ℕ) (hT : 2 ≤ T) (Δmin : ℝ) (hΔ : 0 < Δmin) :
    regPre gap G ctx I T Δmin
      ≤ 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δmin := by
  classical
  have hlog2 : (1:ℝ) / 8 ≤ Real.log T := by
    have h1 : Real.log 2 ≤ Real.log T :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have h2 := Real.log_two_gt_d9
    linarith
  set L : ℝ := 8 * Real.log T with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hκ0 : 0 ≤ ∑ i, (cliqueCoverNumber (G i) : ℝ) := by positivity
  -- the set of counted rounds
  set B := (Finset.range T).filter (fun t => Δmin ≤ gap (I t) (ctx t) ∧
        (obsCount G ctx I t (I t) (ctx t) : ℝ) ≤ mThr T (gap (I t) (ctx t))) with hB
  have hreg : regPre gap G ctx I T Δmin = ∑ t ∈ B, gap (I t) (ctx t) := by
    unfold regPre
    rw [Finset.sum_filter]
  rcases le_or_gt Δmin 1 with hΔ1 | hΔ1
  swap
  · -- no round qualifies
    have : B = ∅ := by
      apply Finset.filter_false_of_mem
      intro t _ h
      have := (hgap (I t) (ctx t)).2
      linarith [h.1]
    rw [hreg, this, Finset.sum_empty]
    positivity
  set M : ℝ := L / Δmin ^ 2 with hMdef
  have hM1 : L ≤ M := by
    rw [hMdef, le_div_iff₀ (by positivity)]
    have : Δmin ^ 2 ≤ 1 := by nlinarith
    nlinarith
  set N : ℕ := ⌊M⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hNM : (N : ℝ) ≤ M := Nat.floor_le (by linarith)
  have hblock : 2 * Real.sqrt L * Real.sqrt N ≤ 2 * L / Δmin := by
    have : Real.sqrt L * Real.sqrt N ≤ L / Δmin := by
      rw [← Real.sqrt_mul (by linarith)]
      have hLM : L * N ≤ (L / Δmin) ^ 2 := by
        rw [div_pow]
        calc L * N ≤ L * M := mul_le_mul_of_nonneg_left hNM (by linarith)
          _ = L ^ 2 / Δmin ^ 2 := by rw [hMdef]; field_simp
      calc Real.sqrt (L * N) ≤ Real.sqrt ((L / Δmin) ^ 2) := Real.sqrt_le_sqrt hLM
        _ = L / Δmin := Real.sqrt_sq (by positivity)
    have h2 : 2 * L / Δmin = 2 * (L / Δmin) := by ring
    rw [h2]; linarith
  -- clique covers
  have hcov : ∀ i, ∃ f : Fin C → Fin (cliqueCoverNumber (G i)), ∀ u v, f u = f v → G i u v := by
    intro i
    have hne : {r : ℕ | ∃ f : Fin C → Fin r, ∀ u v, f u = f v → G i u v}.Nonempty :=
      ⟨C, id, fun u v h => by simp only [id] at h; subst h; exact hG i u⟩
    exact Nat.sInf_mem hne
  choose f hf using hcov
  rw [hreg]
  -- decompose by arm and clique
  rw [← Finset.sum_fiberwise B (fun t => I t)]
  have hper : ∀ i : Fin K, (∑ t ∈ B with I t = i, gap (I t) (ctx t))
      ≤ (cliqueCoverNumber (G i) : ℝ) * (2 * L / Δmin) := by
    intro i
    rw [← Finset.sum_fiberwise (B.filter (fun t => I t = i)) (fun t => f i (ctx t))]
    calc (∑ r, ∑ t ∈ (B.filter (fun t => I t = i)) with f i (ctx t) = r, gap (I t) (ctx t))
        ≤ ∑ _r : Fin (cliqueCoverNumber (G i)), 2 * L / Δmin := by
          apply Finset.sum_le_sum
          intro r _
          set S : Finset (Fin C) := Finset.univ.filter (fun c => f i c = r)
          set A := (B.filter (fun t => I t = i)).filter (fun t => f i (ctx t) = r)
          have hA : ∀ t ∈ A, I t = i ∧ ctx t ∈ S := by
            intro t ht
            simp only [A, Finset.mem_filter] at ht
            exact ⟨ht.1.2, by simp [S, ht.2]⟩
          -- pullsIn in the clique is at most the observation count
          have hpo : ∀ t ∈ A, pullsIn ctx I t i S ≤ obsCount G ctx I t i (ctx t) := by
            intro t ht
            have ht' := hA t ht
            unfold pullsIn obsCount
            apply Finset.card_le_card
            intro s hs
            simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
            refine ⟨hs.1, hs.2.1, ?_⟩
            have h1 := hs.2.2
            have h2 := ht'.2
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
            exact hf i _ _ (h1.trans h2.symm)
          have hcond : ∀ t ∈ A, Δmin ≤ gap i (ctx t) ∧
              (obsCount G ctx I t i (ctx t) : ℝ) ≤ mThr T (gap i (ctx t)) := by
            intro t ht
            simp only [A, B, Finset.mem_filter] at ht
            obtain ⟨⟨⟨_, h1, h2⟩, h3⟩, _⟩ := ht
            rw [h3] at h1 h2
            exact ⟨h1, h2⟩
          have hkm : ∀ t ∈ A, (pullsIn ctx I t i S : ℝ) ≤ L / gap i (ctx t) ^ 2 := by
            intro t ht
            have h1 : (pullsIn ctx I t i S : ℝ) ≤ obsCount G ctx I t i (ctx t) := by
              exact_mod_cast hpo t ht
            have h2 := (hcond t ht).2
            unfold mThr at h2
            rw [hLdef]; linarith
          have hgpos : ∀ t ∈ A, 0 < gap i (ctx t) := fun t ht => lt_of_lt_of_le hΔ (hcond t ht).1
          calc (∑ t ∈ A, gap (I t) (ctx t)) ≤ 2 * Real.sqrt L * Real.sqrt N := by
                apply UCB1CLLemma3Aux.block_bound ctx I i S A hA _ L (by linarith) N hN1
                · intro t ht
                  have h1 := hkm t ht
                  have hg := hgpos t ht
                  have h2 : L / gap i (ctx t) ^ 2 ≤ M := by
                    rw [hMdef]
                    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
                    exact pow_le_pow_left₀ hΔ.le (hcond t ht).1 2
                  exact Nat.le_floor (by linarith)
                · intro t ht
                  rw [(hA t ht).1]
                  have hg := hgpos t ht
                  have hg1 := (hgap i (ctx t)).2
                  have h1 := hkm t ht
                  set k : ℝ := (pullsIn ctx I t i S : ℝ)
                  have hk0 : 0 ≤ k := Nat.cast_nonneg _
                  rw [le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
                  rw [← Real.sqrt_sq hg.le, ← Real.sqrt_mul (by positivity)]
                  apply Real.sqrt_le_sqrt
                  rcases le_total k 1 with hk1 | hk1
                  · rw [max_eq_right hk1]; nlinarith
                  · rw [max_eq_left hk1]
                    rw [le_div_iff₀ (by positivity)] at h1
                    nlinarith
            _ ≤ 2 * L / Δmin := hblock
      _ = (cliqueCoverNumber (G i) : ℝ) * (2 * L / Δmin) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (∑ i, ∑ t ∈ B with I t = i, gap (I t) (ctx t))
      ≤ ∑ i, (cliqueCoverNumber (G i) : ℝ) * (2 * L / Δmin) := Finset.sum_le_sum (fun i _ => hper i)
    _ = 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δmin := by
        rw [← Finset.sum_mul, hLdef]; ring
