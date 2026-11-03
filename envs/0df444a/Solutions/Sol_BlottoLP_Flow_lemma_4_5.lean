-- Prove2me | solution 1 for BlottoLP.Flow.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:11:22.437735+00:00
-- url     : https://prove2.me/submissions/948d5eae-e8fc-4311-926d-596391ea9b58

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow.Lib

open Finset BlottoLP.Flow

theorem filter_lt_succ (K k : ℕ) (hk : k < K) :
    univ.filter (fun k' : Fin K => (k' : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (univ.filter (fun k' : Fin K => (k' : ℕ) < k)) := by
  ext k'
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem path_succ {K N : ℕ} (x : Pure K N) (k : Fin K) :
    ((prefixPath x).1 k.succ : ℕ) = (prefixPath x).1 k.castSucc + x.1 k := by
  show prefixSum x k.succ = prefixSum x k.castSucc + x.1 k
  unfold prefixSum
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [filter_lt_succ K k k.isLt, sum_insert (by simp), add_comm]

theorem path_zero {K N : ℕ} (x : Pure K N) : (prefixPath x).1 0 = 0 := (prefixPath x).2.1

theorem path_last {K N : ℕ} (x : Pure K N) : (prefixPath x).1 (Fin.last K) = Fin.last N :=
  (prefixPath x).2.2.1

/-- Lemma 4.3. -/
theorem lemma43 (K N : ℕ) : Function.Bijective (prefixPath : Pure K N → CanonicalPath K N) := by
  constructor
  · intro x x' h
    apply Subtype.ext
    funext k
    apply Fin.ext
    have h1 := path_succ x k
    have h2 := path_succ x' k
    rw [h] at h1
    omega
  · intro s
    obtain ⟨s, hs0, hsl, hsm⟩ := s
    let x : Fin K → Fin (N + 1) := fun k =>
      ⟨(s k.succ : ℕ) - s k.castSucc, lt_of_le_of_lt (Nat.sub_le _ _) (s k.succ).isLt⟩
    have tele : ∀ k (hk : k ≤ K),
        ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < k), (x k' : ℕ) =
          s ⟨k, Nat.lt_succ_of_le hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro hk
        have : (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (K + 1)) = 0 := rfl
        rw [this, hs0]; simp
      | succ k ih =>
        intro hk
        rw [filter_lt_succ K k hk, sum_insert (by simp), ih (by omega)]
        have hm := hsm ⟨k, hk⟩
        simp only [x]
        have e1 : (⟨k, hk⟩ : Fin K).castSucc = ⟨k, Nat.lt_succ_of_le (by omega)⟩ := rfl
        have e2 : (⟨k, hk⟩ : Fin K).succ = ⟨k + 1, Nat.lt_succ_of_le hk⟩ := rfl
        rw [e1, e2] at hm ⊢
        rw [Fin.le_def] at hm
        omega
    have hsum : ∑ k, (x k : ℕ) = N := by
      have := tele K le_rfl
      have hall : univ.filter (fun k' : Fin K => (k' : ℕ) < K) = univ := by
        ext k'; simp [k'.isLt]
      rw [hall] at this
      rw [this]
      have : (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1)) = Fin.last K := rfl
      rw [this, hsl]; simp
    refine ⟨⟨x, hsum⟩, ?_⟩
    apply Subtype.ext
    funext k
    apply Fin.ext
    show prefixSum ⟨x, hsum⟩ k = s k
    exact tele k (by omega)

/-- The layer-`k` edge of the canonical path of `x`. -/
def edgeOf {K N : ℕ} (x : Pure K N) (k : Fin K) : Edge K N :=
  ⟨(k, (prefixPath x).1 k.castSucc, (prefixPath x).1 k.succ), (prefixPath x).2.2.2 k⟩

theorem flowOf_eq {K N : ℕ} (σ : Pure K N → ℝ) (e : Edge K N) :
    flowOf σ e = ∑ x ∈ univ.filter (fun x => edgeOf x e.1.1 = e), σ x := by
  unfold flowOf
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, edgeOf, Subtype.ext_iff, Prod.ext_iff]

theorem sum_layer {K N : ℕ} (σ : Pure K N → ℝ) (k : Fin K) (Q : Edge K N → Prop)
    [DecidablePred Q] :
    ∑ e ∈ univ.filter (fun e : Edge K N => e.1.1 = k ∧ Q e), flowOf σ e =
      ∑ x ∈ univ.filter (fun x => Q (edgeOf x k)), σ x := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun x => Q (edgeOf x k)))
    (t := univ.filter (fun e : Edge K N => e.1.1 = k ∧ Q e)) (g := fun x => edgeOf x k)
    (by intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨rfl, hx⟩)]
  refine sum_congr rfl fun e he => ?_
  simp only [mem_filter, mem_univ, true_and] at he
  obtain ⟨rfl, hQ⟩ := he
  rw [flowOf_eq]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; exact ⟨h ▸ hQ, h⟩
  · rintro ⟨_, h⟩; exact h

theorem inflow_flowOf {K N : ℕ} (σ : Pure K N → ℝ) (k : Fin K) (l : Fin (N + 1)) :
    inflow (flowOf σ) k l = ∑ x ∈ univ.filter (fun x => (prefixPath x).1 k.succ = l), σ x :=
  sum_layer σ k (fun e => e.1.2.2 = l)

theorem outflow_flowOf {K N : ℕ} (σ : Pure K N → ℝ) (k : Fin K) (l : Fin (N + 1)) :
    outflow (flowOf σ) k l = ∑ x ∈ univ.filter (fun x => (prefixPath x).1 k.castSucc = l), σ x :=
  sum_layer σ k (fun e => e.1.2.1 = l)

/-- A flow of value `c` from `v_{0,0}` to `v_{K,N}` (the constraints (a) with `1` replaced
by `c`). -/
def IsFlowC {K N : ℕ} (c : ℝ) (F : Edge K N → ℝ) : Prop :=
  (∀ e, 0 ≤ F e) ∧
  (∀ (k k' : Fin K), (k' : ℕ) = k + 1 → ∀ l, inflow F k l = outflow F k' l) ∧
  (∀ k : Fin K, (k : ℕ) = 0 → ∀ l : Fin (N + 1), 0 < l → outflow F k l = 0) ∧
  (∀ k : Fin K, (k : ℕ) = 0 → outflow F k 0 = c) ∧
  (∀ k : Fin K, (k : ℕ) + 1 = K → inflow F k (Fin.last N) = c)

theorem isFlowC_flowOf {K N : ℕ} (σ : Pure K N → ℝ) (hσ : ∀ x, 0 ≤ σ x) :
    IsFlowC (∑ x, σ x) (flowOf σ) := by
  refine ⟨fun e => sum_nonneg fun x _ => hσ x, ?_, ?_, ?_, ?_⟩
  · intro k k' hk l
    rw [inflow_flowOf, outflow_flowOf]
    have : k'.castSucc = k.succ := Fin.ext (by simp [hk])
    rw [this]
  · intro k hk l hl
    rw [outflow_flowOf]
    have : k.castSucc = 0 := Fin.ext (by simp [hk])
    rw [this]
    apply sum_eq_zero
    intro x hx
    simp only [mem_filter, mem_univ, true_and, path_zero] at hx
    subst hx; exact absurd hl (lt_irrefl _)
  · intro k hk
    rw [outflow_flowOf]
    have : k.castSucc = 0 := Fin.ext (by simp [hk])
    rw [this]
    simp [path_zero]
  · intro k hk
    rw [inflow_flowOf]
    have : k.succ = Fin.last K := Fin.ext (by simp [hk])
    rw [this]
    simp [path_last]

theorem flowMarginal_flowOf {K N : ℕ} (σ : Pure K N → ℝ) :
    flowMarginal (flowOf σ) = marginal σ := by
  funext kj
  obtain ⟨k, j⟩ := kj
  unfold flowMarginal marginal
  rw [sum_layer σ k (fun e => (e.1.2.2 : ℕ) = e.1.2.1 + j)]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro x _
  simp only [edgeOf]
  rw [path_succ, Fin.ext_iff]
  omega

/-- Corollary 4.4. -/
theorem cor44 (K N : ℕ) (σ : Pure K N → ℝ) (hσ : IsMixed σ) :
    IsUnitFlow (flowOf σ) ∧ flowMarginal (flowOf σ) = marginal σ := by
  refine ⟨?_, flowMarginal_flowOf σ⟩
  have := isFlowC_flowOf σ hσ.1
  rw [hσ.2] at this
  exact this


section Decomp

variable {K N : ℕ}

theorem inflow_sub (F G : Edge K N → ℝ) (r : ℝ) (k : Fin K) (l : Fin (N + 1)) :
    inflow (fun e => F e - r * G e) k l = inflow F k l - r * inflow G k l := by
  simp [inflow, sum_sub_distrib, mul_sum]

theorem outflow_sub (F G : Edge K N → ℝ) (r : ℝ) (k : Fin K) (l : Fin (N + 1)) :
    outflow (fun e => F e - r * G e) k l = outflow F k l - r * outflow G k l := by
  simp [outflow, sum_sub_distrib, mul_sum]

theorem isFlowC_sub {c d r : ℝ} {F G : Edge K N → ℝ} (hF : IsFlowC c F) (hG : IsFlowC d G)
    (hnn : ∀ e, 0 ≤ F e - r * G e) : IsFlowC (c - r * d) (fun e => F e - r * G e) := by
  obtain ⟨_, h2, h3, h4, h5⟩ := hF
  obtain ⟨_, g2, g3, g4, g5⟩ := hG
  refine ⟨hnn, ?_, ?_, ?_, ?_⟩
  · intro k k' hk l; rw [inflow_sub, outflow_sub, h2 k k' hk l, g2 k k' hk l]
  · intro k hk l hl; rw [outflow_sub, h3 k hk l hl, g3 k hk l hl]; ring
  · intro k hk; rw [outflow_sub, h4 k hk, g4 k hk]
  · intro k hk; rw [inflow_sub, h5 k hk, g5 k hk]

/-- Total flow on the layer-`k` edges. -/
def layerSum (F : Edge K N → ℝ) (k : Fin K) : ℝ :=
  ∑ e ∈ univ.filter (fun e : Edge K N => e.1.1 = k), F e

theorem sum_outflow (F : Edge K N → ℝ) (k : Fin K) : ∑ l, outflow F k l = layerSum F k := by
  unfold outflow layerSum
  rw [← Finset.sum_fiberwise (s := univ.filter (fun e : Edge K N => e.1.1 = k))
    (g := fun e => e.1.2.1)]
  refine sum_congr rfl fun l _ => ?_
  rw [filter_filter]

theorem sum_inflow (F : Edge K N → ℝ) (k : Fin K) : ∑ l, inflow F k l = layerSum F k := by
  unfold inflow layerSum
  rw [← Finset.sum_fiberwise (s := univ.filter (fun e : Edge K N => e.1.1 = k))
    (g := fun e => e.1.2.2)]
  refine sum_congr rfl fun l _ => ?_
  rw [filter_filter]

theorem layerSum_eq {c : ℝ} {F : Edge K N → ℝ} (hF : IsFlowC c F) (k : Fin K) :
    layerSum F k = c := by
  obtain ⟨_, h2, h3, h4, _⟩ := hF
  have : ∀ m (hm : m < K), layerSum F ⟨m, hm⟩ = c := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [← sum_outflow, Finset.sum_eq_single 0]
      · exact h4 _ rfl
      · intro l _ hl; exact h3 _ rfl l (Fin.pos_iff_ne_zero.2 hl)
      · simp
    | succ m ih =>
      intro hm
      rw [← sum_outflow]
      have : ∀ l, outflow F ⟨m + 1, hm⟩ l = inflow F ⟨m, by omega⟩ l :=
        fun l => (h2 ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl l).symm
      simp_rw [this]
      rw [sum_inflow]
      exact ih _
  exact this k k.isLt

theorem le_layerSum {c : ℝ} {F : Edge K N → ℝ} (hF : IsFlowC c F) (e : Edge K N) :
    F e ≤ layerSum F e.1.1 :=
  single_le_sum (f := F) (fun e _ => hF.1 e) (by simp)

/-- A path of positive edges from `v_{0,0}` to `v_{K,N}`, traced backwards from `v_{K,N}`. -/
theorem trace (hK : 1 ≤ K) {c : ℝ} {F : Edge K N → ℝ} (hF : IsFlowC c F) (hc : 0 < c) :
    ∃ x : Pure K N, ∀ k, 0 < F (edgeOf x k) := by
  have claim : ∀ m, m ≤ K → ∃ s : Fin (K + 1) → Fin (N + 1), s (Fin.last K) = Fin.last N ∧
      ∀ k : Fin K, K ≤ (k : ℕ) + m →
        ∃ e : Edge K N, e.1 = (k, s k.castSucc, s k.succ) ∧ 0 < F e := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun _ => Fin.last N, rfl, fun k hk => absurd hk (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨s, hsl, hs⟩ := ih (by omega)
      set k₀ : Fin K := ⟨K - m - 1, by omega⟩ with hk₀
      have hin : 0 < inflow F k₀ (s k₀.succ) := by
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · have : k₀.succ = Fin.last K := Fin.ext (by simp [k₀]; omega)
          rw [this, hsl, hF.2.2.2.2 k₀ (by simp [k₀]; omega)]
          exact hc
        · set k₁ : Fin K := ⟨K - m, by omega⟩ with hk₁
          obtain ⟨e, he, hpos⟩ := hs k₁ (by simp [k₁]; omega)
          have hcons := hF.2.1 k₀ k₁ (by simp [k₀, k₁]; omega) (s k₀.succ)
          rw [hcons]
          have hcs : k₁.castSucc = k₀.succ := Fin.ext (by simp [k₀, k₁]; omega)
          have hle : F e ≤ outflow F k₁ (s k₀.succ) := by
            unfold outflow
            apply single_le_sum (f := F) (fun e _ => hF.1 e)
            simp only [mem_filter, mem_univ, true_and]
            rw [he, ← hcs]
            exact ⟨rfl, rfl⟩
          linarith
      obtain ⟨e, he, hpos⟩ : ∃ e ∈ univ.filter (fun e : Edge K N =>
          e.1.1 = k₀ ∧ e.1.2.2 = s k₀.succ), 0 < F e := by
        by_contra hcon
        push_neg at hcon
        have := sum_nonpos hcon
        unfold inflow at hin
        linarith
      simp only [mem_filter, mem_univ, true_and] at he
      have hne1 : Fin.last K ≠ k₀.castSucc := by
        intro h; have := congrArg Fin.val h; simp [k₀] at this; omega
      refine ⟨Function.update s k₀.castSucc e.1.2.1, ?_, ?_⟩
      · rw [Function.update_of_ne hne1]; exact hsl
      · intro k hk
        by_cases hkk : k = k₀
        · rw [hkk]
          refine ⟨e, ?_, hpos⟩
          have hne2 : k₀.succ ≠ k₀.castSucc := by
            intro h; have := congrArg Fin.val h; simp at this
          rw [Function.update_self, Function.update_of_ne hne2]
          exact Prod.ext he.1 (Prod.ext rfl he.2)
        · have hkv : (k : ℕ) ≠ k₀ := fun h => hkk (Fin.ext h)
          simp only [k₀] at hkv
          have hk' : K ≤ (k : ℕ) + m := by omega
          obtain ⟨e', he', hpos'⟩ := hs k hk'
          refine ⟨e', ?_, hpos'⟩
          have hne3 : k.castSucc ≠ k₀.castSucc := by
            intro h; have := congrArg Fin.val h; simp [k₀] at this; omega
          have hne4 : k.succ ≠ k₀.castSucc := by
            intro h; have := congrArg Fin.val h; simp [k₀] at this; omega
          rw [Function.update_of_ne hne3, Function.update_of_ne hne4]
          exact he'
  obtain ⟨s, hsl, hs⟩ := claim K le_rfl
  have hall : ∀ k : Fin K, ∃ e : Edge K N, e.1 = (k, s k.castSucc, s k.succ) ∧ 0 < F e :=
    fun k => hs k (by omega)
  have hmono : ∀ k : Fin K, s k.castSucc ≤ s k.succ := by
    intro k
    obtain ⟨e, he, _⟩ := hall k
    have := e.2
    rw [he] at this
    exact this
  have hs0 : s 0 = 0 := by
    obtain ⟨e, he, hpos⟩ := hall ⟨0, hK⟩
    have h0 : (⟨0, hK⟩ : Fin K).castSucc = 0 := rfl
    rw [h0] at he
    by_contra hne
    have hout := hF.2.2.1 ⟨0, hK⟩ rfl (s 0) (Fin.pos_iff_ne_zero.2 hne)
    have hle : F e ≤ outflow F ⟨0, hK⟩ (s 0) := by
      unfold outflow
      apply single_le_sum (f := F) (fun e _ => hF.1 e)
      simp only [mem_filter, mem_univ, true_and]
      rw [he]
      exact ⟨rfl, rfl⟩
    linarith
  obtain ⟨x, hx⟩ := (lemma43 K N).2 ⟨s, hs0, hsl, hmono⟩
  refine ⟨x, fun k => ?_⟩
  obtain ⟨e, he, hpos⟩ := hall k
  have : edgeOf x k = e := by
    apply Subtype.ext
    rw [he]
    simp only [edgeOf, hx]
  rw [this]
  exact hpos

theorem flowOf_pure (x : Pure K N) (e : Edge K N) :
    flowOf (pureMixed x) e = if edgeOf x e.1.1 = e then 1 else 0 := by
  rw [flowOf_eq]
  unfold pureMixed
  rw [Finset.sum_ite_eq']
  simp [mem_filter]

theorem flowOf_add (a b : Pure K N → ℝ) (r : ℝ) :
    flowOf (fun y => a y + r * b y) = fun e => flowOf a e + r * flowOf b e := by
  funext e
  simp [flowOf, sum_add_distrib, mul_sum]

theorem sum_pureMixed (x : Pure K N) : ∑ y, pureMixed x y = 1 := by
  simp [pureMixed]

theorem pureMixed_nonneg (x y : Pure K N) : 0 ≤ pureMixed x y := by
  unfold pureMixed; split_ifs <;> norm_num

/-- Flow decomposition (proof of Lemma 4.5): a flow of value `c` is the flow of a non-negative
weight function of total mass `c` with no more pure strategies in its support than the flow has
positive edges. -/
theorem decomp (hK : 1 ≤ K) : ∀ n : ℕ, ∀ (c : ℝ) (F : Edge K N → ℝ), IsFlowC c F →
    (univ.filter (fun e => F e ≠ 0)).card ≤ n →
    ∃ σ : Pure K N → ℝ, (∀ x, 0 ≤ σ x) ∧ ∑ x, σ x = c ∧ flowOf σ = F ∧
      (univ.filter (fun x => σ x ≠ 0)).card ≤ n := by
  have zero_case : ∀ (c : ℝ) (F : Edge K N → ℝ), IsFlowC c F → (∀ e, F e = 0) →
      ∃ σ : Pure K N → ℝ, (∀ x, 0 ≤ σ x) ∧ ∑ x, σ x = c ∧ flowOf σ = F ∧
        (univ.filter (fun x => σ x ≠ 0)).card = 0 := by
    intro c F hF hF0
    have hc : c = 0 := by
      rw [← layerSum_eq hF ⟨0, hK⟩]
      unfold layerSum
      exact sum_eq_zero fun e _ => hF0 e
    refine ⟨0, fun _ => le_rfl, by simp [hc], ?_, by simp⟩
    funext e
    simp [flowOf, hF0]
  intro n
  induction n with
  | zero =>
    intro c F hF hcard
    have hF0 : ∀ e, F e = 0 := by
      intro e
      by_contra h
      have hmem : e ∈ univ.filter (fun e => F e ≠ 0) := by simp [h]
      have := card_pos.2 ⟨e, hmem⟩
      omega
    obtain ⟨σ, h1, h2, h3, h4⟩ := zero_case c F hF hF0
    exact ⟨σ, h1, h2, h3, h4.le⟩
  | succ n ih =>
    intro c F hF hcard
    by_cases hF0 : ∀ e, F e = 0
    · obtain ⟨σ, h1, h2, h3, h4⟩ := zero_case c F hF hF0
      exact ⟨σ, h1, h2, h3, by omega⟩
    push_neg at hF0
    obtain ⟨e0, he0⟩ := hF0
    have hc : 0 < c := by
      rw [← layerSum_eq hF e0.1.1]
      exact lt_of_lt_of_le (lt_of_le_of_ne (hF.1 e0) (Ne.symm he0)) (le_layerSum hF e0)
    obtain ⟨x, hx⟩ := trace hK hF hc
    have hne : (univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, mem_univ _⟩
    set ε := (univ : Finset (Fin K)).inf' hne (fun k => F (edgeOf x k)) with hεdef
    have hεpos : 0 < ε := (lt_inf'_iff _).2 (fun k _ => hx k)
    have hεle : ∀ k, ε ≤ F (edgeOf x k) := fun k => inf'_le _ (mem_univ k)
    obtain ⟨kstar, -, hkstar⟩ := exists_mem_eq_inf' hne (fun k => F (edgeOf x k))
    have hP : IsFlowC 1 (flowOf (pureMixed x)) := by
      have := isFlowC_flowOf (pureMixed x) (pureMixed_nonneg x)
      rw [sum_pureMixed] at this
      exact this
    have hnn : ∀ e, 0 ≤ F e - ε * flowOf (pureMixed x) e := by
      intro e
      rw [flowOf_pure]
      split_ifs with h
      · have := hεle e.1.1
        rw [h] at this
        linarith
      · simp only [mul_zero, sub_zero]; exact hF.1 e
    have hF' : IsFlowC (c - ε) (fun e => F e - ε * flowOf (pureMixed x) e) := by
      have := isFlowC_sub hF hP hnn
      rw [mul_one] at this
      exact this
    have hsub : univ.filter (fun e => F e - ε * flowOf (pureMixed x) e ≠ 0) ⊂
        univ.filter (fun e => F e ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨edgeOf x kstar, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          exact ne_of_gt (hx kstar)
        · simp only [mem_filter, mem_univ, true_and, not_not]
          have h1 : flowOf (pureMixed x) (edgeOf x kstar) = 1 := by
            rw [flowOf_pure]; exact if_pos rfl
          rw [h1, ← hkstar]
          ring
      · intro e he
        simp only [mem_filter, mem_univ, true_and] at he ⊢
        intro hFe
        apply he
        rw [flowOf_pure]
        split_ifs with h
        · exfalso
          have := hx e.1.1
          rw [h] at this
          linarith
        · simp [hFe]
    have hcard' : (univ.filter (fun e => F e - ε * flowOf (pureMixed x) e ≠ 0)).card ≤ n := by
      have := card_lt_card hsub
      omega
    obtain ⟨σ', h1, h2, h3, h4⟩ := ih (c - ε) _ hF' hcard'
    refine ⟨fun y => σ' y + ε * pureMixed x y, ?_, ?_, ?_, ?_⟩
    · intro y
      exact add_nonneg (h1 y) (mul_nonneg hεpos.le (pureMixed_nonneg x y))
    · rw [sum_add_distrib, ← mul_sum, h2, sum_pureMixed]
      ring
    · rw [flowOf_add, h3]
      funext e
      ring
    · have hsub2 : univ.filter (fun y => σ' y + ε * pureMixed x y ≠ 0) ⊆
          insert x (univ.filter (fun y => σ' y ≠ 0)) := by
        intro y hy
        simp only [mem_filter, mem_univ, true_and, mem_insert] at hy ⊢
        by_cases hyx : y = x
        · left; exact hyx
        · right
          intro h
          apply hy
          simp [pureMixed, hyx, h]
      calc _ ≤ (insert x (univ.filter (fun y => σ' y ≠ 0))).card := card_le_card hsub2
        _ ≤ (univ.filter (fun y => σ' y ≠ 0)).card + 1 := card_insert_le _ _
        _ ≤ n + 1 := by omega

/-- Lemma 4.5. -/
theorem lem45 (K N : ℕ) (hK : 1 ≤ K) (F : Edge K N → ℝ) (hF : IsUnitFlow F) :
    ∃ σ : Pure K N → ℝ, IsMixed σ ∧ flowOf σ = F ∧
      (univ.filter (fun x : Pure K N => σ x ≠ 0)).card ≤ Fintype.card (Edge K N) := by
  obtain ⟨σ, h1, h2, h3, h4⟩ := decomp hK _ 1 F hF le_rfl
  refine ⟨σ, ⟨h1, h2⟩, h3, h4.trans ?_⟩
  exact (card_filter_le _ _).trans (by rw [card_univ])

end Decomp

end BlottoLP.Flow.Lib

open BlottoLP.Flow Finset in
theorem solution (K N : ℕ) (hK : 1 ≤ K) (F : Edge K N → ℝ) (hF : IsUnitFlow F) :
    ∃ σ : Pure K N → ℝ, IsMixed σ ∧ flowOf σ = F ∧
      (univ.filter (fun x : Pure K N => σ x ≠ 0)).card ≤ Fintype.card (Edge K N) :=
  BlottoLP.Flow.Lib.lem45 K N hK F hF
