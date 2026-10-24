-- Prove2me | solution 1 for FairGuarantees.BidChoose.right_hand_construction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:34:08.645251+00:00
-- url     : https://prove2.me/submissions/9bb51251-8b4f-4aa0-9626-03fff9cf6b44

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory FairGuarantees.DivideChoose FairGuarantees.BidChoose

namespace FGThm2iiiAux

variable {d : ℕ}

lemma u_nonneg {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (hinc : IsIncreasing Ω u) {S : Set (E d)} (hS : IsShare Ω S) : 0 ≤ u S := by
  have h0 : IsShare Ω (∅ : Set (E d)) := ⟨MeasurableSet.empty, Set.empty_subset _⟩
  have := hinc ∅ S h0 hS (Set.empty_subset _)
  rw [hu.1] at this
  exact this

lemma u_le {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u) :
    ∃ C : ℝ, ∀ S, IsShare Ω S → u S ≤ C := by
  obtain ⟨C, hC⟩ := hu.2.1
  exact ⟨C, fun S hS => (le_abs_self _).trans (hC S hS)⟩

lemma knife_share {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : IsKnife Ω K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsShare Ω (K t) := hK.2.2.1 t ht

lemma knife_mono {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : IsKnife Ω K) {t t' : ℝ}
    (h0 : 0 ≤ t) (htt : t ≤ t') (h1 : t' ≤ 1) : K t ⊆ K t' := by
  rcases eq_or_lt_of_le htt with h | h
  · rw [h]
  · exact (hK.2.2.2.2 t t' h0 h h1).1.subset

lemma piece_share {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : IsKnife Ω K) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) : IsShare Ω (K b \ K a) :=
  ⟨(knife_share hK hb).1.diff (knife_share hK ha).1, Set.sdiff_subset.trans (knife_share hK hb).2⟩

/-- A chain `0 = f 0 ≤ f 1 ≤ ⋯ ≤ f n = 1`. -/
def IsChain (n : ℕ) (f : ℕ → ℝ) : Prop := f 0 = 0 ∧ f n = 1 ∧ ∀ k < n, f k ≤ f (k + 1)

lemma chain_mono {n : ℕ} {f : ℕ → ℝ} (hf : IsChain n f) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    f i ≤ f j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hf.2.2 j (by omega))

lemma chain_mem {n : ℕ} {f : ℕ → ℝ} (hf : IsChain n f) {k : ℕ} (hk : k ≤ n) :
    f k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hf.1 ▸ chain_mono hf (Nat.zero_le _) hk, hf.2.1 ▸ chain_mono hf hk le_rfl⟩

lemma knife_partition {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : IsKnife Ω K) {n : ℕ}
    {f : ℕ → ℝ} (hf : IsChain n f) :
    IsPartition Ω Ω n (fun k : Fin n => K (f (k.val + 1)) \ K (f k.val)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := piece_share hK (chain_mem hf (show (i : ℕ) ≤ n by omega))
      (chain_mem hf (show (i : ℕ) + 1 ≤ n by omega))
    exact ⟨h, h.2⟩
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => Set.sdiff_subset.trans
        (knife_share hK (chain_mem hf (show (i : ℕ) + 1 ≤ n by omega))).2
    · intro x hx
      have key : ∀ m ≤ n, x ∈ K (f m) →
          ∃ i : Fin n, x ∈ K (f (i.val + 1)) \ K (f i.val) := by
        intro m
        induction m with
        | zero =>
          intro _ hx0
          rw [hf.1, hK.1] at hx0
          exact absurd hx0 (Set.notMem_empty x)
        | succ m ih =>
          intro hm hxm
          by_cases h : x ∈ K (f m)
          · exact ih (by omega) h
          · exact ⟨⟨m, by omega⟩, hxm, h⟩
      have : x ∈ K (f n) := by rw [hf.2.1, hK.2.1]; exact hx
      obtain ⟨i, hi⟩ := key n le_rfl this
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  · intro i j hij
    have hdisj : ∀ a b : Fin n, a.val < b.val →
        Disjoint (K (f (a.val + 1)) \ K (f a.val)) (K (f (b.val + 1)) \ K (f b.val)) := by
      intro a b hab
      rw [Set.disjoint_left]
      intro x hx hy
      exact hy.2 (knife_mono hK (chain_mem hf (show a.val + 1 ≤ n by omega)).1
        (chain_mono hf (show a.val + 1 ≤ b.val by omega) (by omega))
        (chain_mem hf (show b.val ≤ n by omega)).2 hx.1)
    have hd : Disjoint (K (f (i.val + 1)) \ K (f i.val)) (K (f (j.val + 1)) \ K (f j.val)) := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact hdisj i j h
      · exact (hdisj j i h).symm
    rw [Set.disjoint_iff_inter_eq_empty.1 hd]
    exact measure_empty

lemma upsilon_of_chain {n : ℕ} {f : ℕ → ℝ} (hf : IsChain n f) :
    IsUpsilon n (fun k : Fin (n + 1) => f k.val) := by
  refine ⟨by simpa using hf.1, by simpa using hf.2.1, ?_⟩
  rw [Fin.monotone_iff_le_succ]
  intro i
  simpa [Fin.val_succ] using hf.2.2 i i.isLt

lemma chain_of_upsilon {n : ℕ} {τ : Fin (n + 1) → ℝ} (hτ : IsUpsilon n τ) :
    ∃ f : ℕ → ℝ, IsChain n f ∧
      ∀ k : Fin n, τ k.castSucc = f k.val ∧ τ k.succ = f (k.val + 1) := by
  refine ⟨fun i => if h : i < n + 1 then τ ⟨i, h⟩ else 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [Nat.zero_lt_succ, dite_true]
    exact hτ.1
  · simp only [Nat.lt_succ_self, dite_true]
    exact hτ.2.1
  · intro k hk
    simp only [show k < n + 1 by omega, show k + 1 < n + 1 by omega, dite_true]
    exact hτ.2.2 (Fin.mk_le_mk.2 (by omega))
  · intro k
    simp only [show (k : ℕ) < n + 1 by omega, show (k : ℕ) + 1 < n + 1 by omega, dite_true]
    exact ⟨rfl, rfl⟩

lemma upsilon_mem {n : ℕ} {τ : Fin (n + 1) → ℝ} (hτ : IsUpsilon n τ) (i : Fin (n + 1)) :
    τ i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hτ.1 ▸ hτ.2.2 (Fin.zero_le i), hτ.2.1 ▸ hτ.2.2 (Fin.le_last i)⟩

lemma chain0 (n : ℕ) [NeZero n] : IsChain n (fun k => if k < n then 0 else 1) := by
  refine ⟨by simp [NeZero.pos n], by simp, ?_⟩
  intro k hk
  show (if k < n then (0:ℝ) else 1) ≤ (if k + 1 < n then (0:ℝ) else 1)
  split_ifs <;> norm_num

lemma maxmin_bdd {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u) (n : ℕ) [NeZero n] :
    BddAbove {x | ∃ P : Fin n → Set (E d), IsPartition Ω Ω n P ∧ x = ⨅ i, u (P i)} := by
  obtain ⟨C, hC⟩ := u_le hu
  refine ⟨C, ?_⟩
  rintro x ⟨P, hP, rfl⟩
  exact (ciInf_le (Finite.bddBelow_range _) (⟨0, NeZero.pos n⟩ : Fin n)).trans
    (hC _ (hP.1 _).1)

lemma le_maxmin {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {n : ℕ} [NeZero n]
    {P : Fin n → Set (E d)} (hP : IsPartition Ω Ω n P) : ⨅ i, u (P i) ≤ Maxmin Ω u n :=
  le_csSup (maxmin_bdd hu n) ⟨P, hP, rfl⟩

lemma minmax_le {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (hinc : IsIncreasing Ω u) {n : ℕ} [NeZero n]
    {P : Fin n → Set (E d)} (hP : IsPartition Ω Ω n P) : minMax Ω u n ≤ ⨆ i, u (P i) := by
  unfold minMax
  refine csInf_le ⟨0, ?_⟩ ⟨P, hP, rfl⟩
  rintro x ⟨Q, hQ, rfl⟩
  exact (u_nonneg hu hinc (hQ.1 ⟨0, NeZero.pos n⟩).1).trans
    (le_ciSup (f := fun i => u (Q i)) (Finite.bddAbove_range _) (⟨0, NeZero.pos n⟩ : Fin n))

lemma gamma_nonempty (n : ℕ) [NeZero n] (v : ℝ → ℝ → ℝ) :
    {y | ∃ τ : Fin (n + 1) → ℝ, IsUpsilon n τ ∧
      y = ⨅ k : Fin n, v (τ k.castSucc) (τ k.succ)}.Nonempty :=
  ⟨_, ⟨_, upsilon_of_chain (chain0 n), rfl⟩⟩

lemma gammaK_bdd {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    {K : ℝ → Set (E d)} (hK : IsKnife Ω K) (n : ℕ) [NeZero n] :
    BddAbove {y | ∃ τ : Fin (n + 1) → ℝ, IsUpsilon n τ ∧
      y = ⨅ k : Fin n, uKnife u K (τ k.castSucc) (τ k.succ)} := by
  obtain ⟨C, hC⟩ := u_le hu
  refine ⟨C, ?_⟩
  rintro y ⟨τ, hτ, rfl⟩
  exact (ciInf_le (Finite.bddBelow_range _) (⟨0, NeZero.pos n⟩ : Fin n)).trans
    (hC _ (piece_share hK (upsilon_mem hτ _) (upsilon_mem hτ _)))

lemma le_gammaK {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    {K : ℝ → Set (E d)} (hK : IsKnife Ω K) {n : ℕ} [NeZero n] {f : ℕ → ℝ} (hf : IsChain n f) :
    ⨅ k : Fin n, u (K (f (k.val + 1)) \ K (f k.val)) ≤ Gamma n (uKnife u K) :=
  le_csSup (gammaK_bdd hu hK n) ⟨_, upsilon_of_chain hf, rfl⟩

lemma delta_le {Ω : Set (E d)} (hΩ : IsManna Ω) {A B C : Set (E d)} (hA : A ⊆ Ω) (hB : B ⊆ Ω) :
    δ (A \ C) (B \ C) ≤ δ B A := by
  unfold δ
  apply ENNReal.toReal_mono
  · refine ((measure_mono ?_).trans_lt hΩ.2.1.measure_lt_top).ne
    intro x hx
    rcases Set.mem_symmDiff.1 hx with h | h
    · exact hB h.1
    · exact hA h.1
  · apply measure_mono
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_sdiff] at hx ⊢
    tauto

lemma cont_knife {Ω : Set (E d)} (hΩ : IsManna Ω) {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    {K : ℝ → Set (E d)} (hK : IsKnife Ω K) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun t => u (K t \ K s)) (Set.Icc s 1) := by
  rw [Metric.continuousOn_iff]
  intro t0 ht0 ε hε
  have ht0' : t0 ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.trans ht0.1, ht0.2⟩
  obtain ⟨η, hη, hηu⟩ := hu.2.2 _ (piece_share hK hs ht0') ε hε
  obtain ⟨δ', hδ', hδK⟩ := hK.2.2.2.1 t0 ht0' η hη
  refine ⟨δ', hδ', fun t ht hdist => ?_⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
  rw [Real.dist_eq]
  apply hηu _ (piece_share hK hs ht')
  calc δ (K t0 \ K s) (K t \ K s) ≤ δ (K t) (K t0) :=
        delta_le hΩ (knife_share hK ht0').2 (knife_share hK ht').2
    _ < η := hδK t ht' (by rwa [Real.dist_eq] at hdist)

lemma claim {Ω : Set (E d)} (hΩ : IsManna Ω) {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (hinc : IsIncreasing Ω u) {K : ℝ → Set (E d)} (hK : IsKnife Ω K) (v : ℝ) :
    ∀ m : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ f : ℕ → ℝ, f 0 = s ∧ f (m + 1) = 1 ∧
      (∀ k < m + 1, f k ≤ f (k + 1)) ∧
      ((∀ k < m + 1, u (K (f (k + 1)) \ K (f k)) ≤ v) ∨
        (∀ k < m + 1, v ≤ u (K (f (k + 1)) \ K (f k)))) := by
  have h11 : u (K 1 \ K 1) = 0 := by rw [Set.sdiff_self]; exact hu.1
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  intro m
  induction m with
  | zero =>
    intro s hs
    refine ⟨fun k => if k = 0 then s else 1, by simp, by simp, ?_, ?_⟩
    · intro k hk
      obtain rfl : k = 0 := by omega
      simp [hs.2]
    · rcases le_total (u (K 1 \ K s)) v with h | h
      · left
        intro k hk
        obtain rfl : k = 0 := by omega
        simpa using h
      · right
        intro k hk
        obtain rfl : k = 0 := by omega
        simpa using h
  | succ m ih =>
    intro s hs
    have hf0mono : ∀ k < m + 1 + 1,
        (fun k => if k = 0 then s else (1 : ℝ)) k ≤ (fun k => if k = 0 then s else (1 : ℝ)) (k + 1) := by
      intro k hk
      rcases k with _ | k
      · simp [hs.2]
      · simp
    by_cases hA : u (K 1 \ K s) ≤ v ∧ 0 ≤ v
    · refine ⟨fun k => if k = 0 then s else 1, by simp, by simp, hf0mono, Or.inl ?_⟩
      intro k hk
      rcases k with _ | k
      · simpa using hA.1
      · simpa [hu.1] using hA.2
    by_cases hB : v ≤ 0
    · refine ⟨fun k => if k = 0 then s else 1, by simp, by simp, hf0mono, Or.inr ?_⟩
      intro k hk
      rcases k with _ | k
      · simpa using hB.trans (u_nonneg hu hinc (piece_share hK hs hone))
      · simpa [hu.1] using hB
    push Not at hB
    have hlt : v < u (K 1 \ K s) := by
      by_contra h
      push Not at h
      exact hA ⟨h, hB.le⟩
    have hss : u (K s \ K s) = 0 := by rw [Set.sdiff_self]; exact hu.1
    obtain ⟨t, ht, htv⟩ := intermediate_value_Icc hs.2 (cont_knife hΩ hu hK hs)
      (show v ∈ Set.Icc (u (K s \ K s)) (u (K 1 \ K s)) from ⟨by rw [hss]; exact hB.le, hlt.le⟩)
    have htv' : u (K t \ K s) = v := htv
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
    obtain ⟨f', hf0, hf1, hfm, hfv⟩ := ih t ht01
    refine ⟨fun k => if k = 0 then s else f' (k - 1), by simp, by simpa using hf1, ?_, ?_⟩
    · intro k hk
      rcases k with _ | k
      · simp [hf0, ht.1]
      · simpa using hfm k (by omega)
    · rcases hfv with h | h
      · left
        intro k hk
        rcases k with _ | k
        · simp [hf0, htv']
        · simpa using h k (by omega)
      · right
        intro k hk
        rcases k with _ | k
        · simp [hf0, htv']
        · simpa using h k (by omega)

lemma uBid_le {Ω : Set (E d)} {θ : Measure (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (hinc : IsIncreasing Ω u) {T : Set (E d)} {t₁ t₂ : ℝ} (hT : IsShare Ω T)
    (hθT : (θ T).toReal = t₁) :
    uBid Ω θ u t₁ t₂ ≤ sSup {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = t₂ - t₁ ∧
      x = u S} := by
  unfold uBid
  refine csInf_le ⟨0, ?_⟩ ⟨T, hT, hθT, rfl⟩
  rintro y ⟨T', -, -, rfl⟩
  apply Real.sSup_nonneg
  rintro x ⟨S, hS, -, -, rfl⟩
  exact u_nonneg hu hinc hS

end FGThm2iiiAux

open FGThm2iiiAux in
theorem solution {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)}
    (hΩ : FairGuarantees.DivideChoose.IsManna Ω) {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {θ : Measure (FairGuarantees.DivideChoose.E d)} (hθ : IsBenchmark Ω θ) :
    ∀ τ : Fin (n + 1) → ℝ, IsUpsilon n τ →
      ⨅ k : Fin n, uBid Ω θ u (τ k.castSucc) (τ k.succ) ≤ FairGuarantees.DivideChoose.Maxmin Ω u n := by
    have hnpos : 0 < n := NeZero.pos n
    have hM0 : 0 ≤ Maxmin Ω u n := by
      let Q0 : Fin n → Set (E d) := fun i => if i.val = 0 then Ω else ∅
      have hQ0 : IsPartition Ω Ω n Q0 := by
        have hs : ∀ i, IsShare Ω (Q0 i) := by
          intro i
          by_cases hi : i.val = 0
          · simp only [Q0, hi, if_true]
            exact ⟨hΩ.1, subset_rfl⟩
          · simp only [Q0, hi, if_false]
            exact ⟨MeasurableSet.empty, Set.empty_subset _⟩
        refine ⟨fun i => ⟨hs i, (hs i).2⟩, ?_, ?_⟩
        · apply Set.Subset.antisymm (Set.iUnion_subset fun i => (hs i).2)
          intro x hx
          exact Set.mem_iUnion.2 ⟨⟨0, NeZero.pos n⟩, by simpa [Q0] using hx⟩
        · intro i j hij
          have : i.val ≠ 0 ∨ j.val ≠ 0 := by
            by_contra h
            push Not at h
            exact hij (Fin.ext (h.1.trans h.2.symm))
          rcases this with h | h
          · simp only [Q0, h, if_false, Set.empty_inter, measure_empty]
          · simp only [Q0, h, if_false, Set.inter_empty, measure_empty]
      exact (le_ciInf fun i => u_nonneg hu hinc (hQ0.1 i).1).trans (le_maxmin hu hQ0)
    have : IsFiniteMeasure θ := ⟨by
      rw [← measure_add_measure_compl hΩ.1, hθ.2.1, hθ.1]; simp⟩
    intro τ hτ
    by_contra hcon
    push Not at hcon
    obtain ⟨f, hf, hfeq⟩ := chain_of_upsilon hτ
    have hy : ∀ k : ℕ, k < n → Maxmin Ω u n < uBid Ω θ u (f k) (f (k + 1)) := by
      intro k hk
      calc Maxmin Ω u n < _ := hcon
        _ ≤ uBid Ω θ u (τ (⟨k, hk⟩ : Fin n).castSucc) (τ (⟨k, hk⟩ : Fin n).succ) :=
          ciInf_le (Finite.bddBelow_range _) _
        _ = _ := by rw [(hfeq _).1, (hfeq _).2]
    -- greedy construction
    have inv : ∀ k, k ≤ n - 1 → ∃ (P : ℕ → Set (E d)) (T : Set (E d)),
        (∀ i < k, IsShare Ω (P i) ∧ Maxmin Ω u n < u (P i) ∧ P i ⊆ T) ∧
        (∀ i < k, ∀ j < k, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ x ∈ T, ∃ i < k, x ∈ P i) ∧ IsShare Ω T ∧ (θ T).toReal = f k := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨fun _ => ∅, ∅, by simp, by simp, by simp,
          ⟨MeasurableSet.empty, Set.empty_subset _⟩, by simp [hf.1]⟩
      | succ k ih =>
        intro hk
        obtain ⟨P, T, hP, hPd, hTU, hT, hθT⟩ := ih (by omega)
        have hle := uBid_le (t₂ := f (k + 1)) hu hinc hT hθT
        have hlt := (hy k (by omega)).trans_le hle
        have hne : {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = f (k + 1) - f k ∧
            x = u S}.Nonempty := by
          by_contra hemp
          rw [Set.not_nonempty_iff_eq_empty] at hemp
          rw [hemp, Real.sSup_empty] at hlt
          linarith
        obtain ⟨x, ⟨S, hS, hST, hθS, rfl⟩, hxS⟩ := exists_lt_of_lt_csSup hne hlt
        refine ⟨fun i => if i = k then S else P i, T ∪ S, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst hik
            simp only [if_true]
            exact ⟨hS, hxS, Set.subset_union_right⟩
          · simp only [hik, if_false]
            obtain ⟨a, b, c⟩ := hP i (by omega)
            exact ⟨a, b, c.trans Set.subset_union_left⟩
        · intro i hi j hj hij
          by_cases hik : i = k
          · subst hik
            have hjk : j ≠ i := fun h => hij h.symm
            simp only [if_true, hjk, if_false]
            exact hST.mono_right (hP j (by omega)).2.2
          · by_cases hjk : j = k
            · subst hjk
              simp only [hik, if_true, if_false]
              exact (hST.mono_right (hP i (by omega)).2.2).symm
            · simp only [hik, hjk, if_false]
              exact hPd i (by omega) j (by omega) hij
        · intro x hx
          rcases hx with hx | hx
          · obtain ⟨i, hi, hxi⟩ := hTU x hx
            refine ⟨i, by omega, ?_⟩
            simp only [show i ≠ k by omega, if_false]
            exact hxi
          · exact ⟨k, by omega, by simpa using hx⟩
        · exact ⟨hT.1.union hS.1, Set.union_subset hT.2 hS.2⟩
        · rw [measure_union hST.symm hS.1, ENNReal.toReal_add (measure_ne_top θ T)
            (measure_ne_top θ S), hθT, hθS]
          ring
    obtain ⟨P, T, hP, hPd, hTU, hT, hθT⟩ := inv (n - 1) le_rfl
    -- last piece
    have hlast : Maxmin Ω u n < u (Ω \ T) := by
      have h1 := hy (n - 1) (by omega)
      rw [Nat.sub_add_cancel hnpos] at h1
      have h2 := uBid_le (t₂ := f n) hu hinc hT hθT
      have hΩT : IsShare Ω (Ω \ T) := ⟨hΩ.1.diff hT.1, Set.sdiff_subset⟩
      have h3 : sSup {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = f n - f (n - 1) ∧
          x = u S} ≤ u (Ω \ T) := by
        by_cases hne : {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧
            (θ S).toReal = f n - f (n - 1) ∧ x = u S}.Nonempty
        · apply csSup_le hne
          rintro x ⟨S, hS, hST, -, rfl⟩
          exact hinc S (Ω \ T) hS hΩT (fun z hz => ⟨hS.2 hz, Set.disjoint_left.1 hST hz⟩)
        · rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, Real.sSup_empty]
          exact u_nonneg hu hinc hΩT
      linarith
    let Q : Fin n → Set (E d) := fun i => if i.val < n - 1 then P i.val else Ω \ T
    have hQdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Q i) (Q j) := by
      have key : ∀ i j : Fin n, i.val < n - 1 → ¬ j.val < n - 1 → Disjoint (Q i) (Q j) := by
        intro i j hi hj
        simp only [Q, hi, hj, if_true, if_false]
        rw [Set.disjoint_left]
        intro z hz hz'
        exact hz'.2 ((hP i.val hi).2.2 hz)
      intro i j hij
      by_cases hi : i.val < n - 1
      · by_cases hj : j.val < n - 1
        · simp only [Q, hi, hj, if_true]
          exact hPd i.val hi j.val hj (Fin.val_ne_of_ne hij)
        · exact key i j hi hj
      · by_cases hj : j.val < n - 1
        · exact (key j i hj hi).symm
        · exfalso
          apply hij
          ext
          omega
    have hQ : IsPartition Ω Ω n Q := by
      have hQs : ∀ i, IsShare Ω (Q i) := by
        intro i
        by_cases hi : i.val < n - 1
        · simp only [Q, hi, if_true]
          exact (hP i.val hi).1
        · simp only [Q, hi, if_false]
          exact ⟨hΩ.1.diff hT.1, Set.sdiff_subset⟩
      refine ⟨fun i => ⟨hQs i, (hQs i).2⟩, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · exact Set.iUnion_subset fun i => (hQs i).2
        · intro x hx
          by_cases hxT : x ∈ T
          · obtain ⟨i, hi, hxi⟩ := hTU x hxT
            refine Set.mem_iUnion.2 ⟨⟨i, by omega⟩, ?_⟩
            simp only [Q, hi, if_true]
            exact hxi
          · refine Set.mem_iUnion.2 ⟨⟨n - 1, by omega⟩, ?_⟩
            simp only [Q, lt_irrefl, if_false]
            exact ⟨hx, hxT⟩
      · intro i j hij
        rw [Set.disjoint_iff_inter_eq_empty.1 (hQdisj i j hij)]
        exact measure_empty
    have hQv : ∀ i, Maxmin Ω u n < u (Q i) := by
      intro i
      by_cases hi : i.val < n - 1
      · simp only [Q, hi, if_true]
        exact (hP i.val hi).2.1
      · simp only [Q, hi, if_false]
        exact hlast
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => u (Q i))
    have := le_maxmin hu hQ
    rw [← hi] at this
    exact absurd this (not_le.2 (hQv i))
