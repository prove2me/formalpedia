-- Prove2me | solution 1 for FairGuarantees.BidChoose.proposition_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:53:30.92073+00:00
-- url     : https://prove2.me/submissions/262da39e-ad23-409d-b856-426f01258b6b

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory FairGuarantees.DivideChoose FairGuarantees.BidChoose

namespace FGThm2iiiAux

variable {d : ℕ}

/-- A weak moving knife: as `IsKnife` but only weakly inclusion-increasing. -/
def WKnife (Ω : Set (E d)) (K : ℝ → Set (E d)) : Prop :=
  K 0 = ∅ ∧ K 1 = Ω ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, IsShare Ω (K t)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ε > 0, ∃ η > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |t - s| < η → δ (K t) (K s) < ε) ∧
    ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ 1 → K t ⊆ K t'

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

lemma knife_share {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : WKnife Ω K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsShare Ω (K t) := hK.2.2.1 t ht

lemma knife_mono {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : WKnife Ω K) {t t' : ℝ}
    (h0 : 0 ≤ t) (htt : t ≤ t') (h1 : t' ≤ 1) : K t ⊆ K t' :=
  hK.2.2.2.2 t t' h0 htt h1

lemma piece_share {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : WKnife Ω K) {a b : ℝ}
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

lemma knife_partition {Ω : Set (E d)} {K : ℝ → Set (E d)} (hK : WKnife Ω K) {n : ℕ}
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
    {K : ℝ → Set (E d)} (hK : WKnife Ω K) (n : ℕ) [NeZero n] :
    BddAbove {y | ∃ τ : Fin (n + 1) → ℝ, IsUpsilon n τ ∧
      y = ⨅ k : Fin n, uKnife u K (τ k.castSucc) (τ k.succ)} := by
  obtain ⟨C, hC⟩ := u_le hu
  refine ⟨C, ?_⟩
  rintro y ⟨τ, hτ, rfl⟩
  exact (ciInf_le (Finite.bddBelow_range _) (⟨0, NeZero.pos n⟩ : Fin n)).trans
    (hC _ (piece_share hK (upsilon_mem hτ _) (upsilon_mem hτ _)))

lemma le_gammaK {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    {K : ℝ → Set (E d)} (hK : WKnife Ω K) {n : ℕ} [NeZero n] {f : ℕ → ℝ} (hf : IsChain n f) :
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
    {K : ℝ → Set (E d)} (hK : WKnife Ω K) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
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
    (hinc : IsIncreasing Ω u) {K : ℝ → Set (E d)} (hK : WKnife Ω K) (v : ℝ) :
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


lemma l4ii_weak {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : WKnife Ω K) :
    ∃ τ : Fin (n + 1) → ℝ, IsUpsilon n τ ∧ ∃ c : ℝ,
      (∀ k : Fin n, uKnife u K (τ k.castSucc) (τ k.succ) = c) ∧
      c = Gamma n (uKnife u K) := by
  have hnpos : 0 < n := NeZero.pos n
  -- joint continuity of `(s, t) ↦ u(K t \ K s)` on the square
  have hfin : ∀ A B : Set (E d), A ⊆ Ω → B ⊆ Ω → volume (symmDiff A B) ≠ ⊤ := by
    intro A B hA hB
    refine ((measure_mono ?_).trans_lt hΩ.2.1.measure_lt_top).ne
    intro x hx
    rcases Set.mem_symmDiff.1 hx with h | h
    · exact hA h.1
    · exact hB h.1
  have hcomm : ∀ A B : Set (E d), δ A B = δ B A := by
    intro A B
    unfold δ
    rw [symmDiff_comm]
  have key : ∀ A B C D : Set (E d), A ⊆ Ω → B ⊆ Ω → C ⊆ Ω → D ⊆ Ω →
      δ (A \ B) (C \ D) ≤ δ A C + δ B D := by
    intro A B C D hA hB hC hD
    unfold δ
    rw [← ENNReal.toReal_add (hfin A C hA hC) (hfin B D hB hD)]
    apply ENNReal.toReal_mono
    · exact ENNReal.add_ne_top.2 ⟨hfin A C hA hC, hfin B D hB hD⟩
    · refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_union] at hx ⊢
      tauto
  have hsq : ContinuousOn (fun q : ℝ × ℝ => u (K q.2 \ K q.1))
      {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1} := by
    rw [Metric.continuousOn_iff]
    rintro ⟨s₁, s₂⟩ ⟨hs₁, hs₂⟩ ε hε
    obtain ⟨η, hη, hηu⟩ := hu.2.2 _ (piece_share hK hs₁ hs₂) ε hε
    obtain ⟨δ₁, hδ₁, hK₁⟩ := hK.2.2.2.1 s₁ hs₁ (η / 2) (by linarith)
    obtain ⟨δ₂, hδ₂, hK₂⟩ := hK.2.2.2.1 s₂ hs₂ (η / 2) (by linarith)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩ hdist
    rw [Prod.dist_eq, max_lt_iff] at hdist
    have d1 : |t₁ - s₁| < δ₁ := by
      have := hdist.1; rw [Real.dist_eq] at this; exact this.trans_le (min_le_left _ _)
    have d2 : |t₂ - s₂| < δ₂ := by
      have := hdist.2; rw [Real.dist_eq] at this; exact this.trans_le (min_le_right _ _)
    rw [Real.dist_eq]
    apply hηu _ (piece_share hK ht₁ ht₂)
    calc δ (K s₂ \ K s₁) (K t₂ \ K t₁) ≤ δ (K s₂) (K t₂) + δ (K s₁) (K t₁) :=
          key _ _ _ _ (knife_share hK hs₂).2 (knife_share hK hs₁).2 (knife_share hK ht₂).2
            (knife_share hK ht₁).2
      _ = δ (K t₂) (K s₂) + δ (K t₁) (K s₁) := by rw [hcomm (K s₂), hcomm (K s₁)]
      _ < η / 2 + η / 2 := add_lt_add (hK₂ t₂ ht₂ d2) (hK₁ t₁ ht₁ d1)
      _ = η := by ring
  -- clamp to `[0, 1]`
  let p : ℝ → ℝ := fun x => (Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ)
  have hp_mem : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1 := fun x => (Set.projIcc (0 : ℝ) 1 zero_le_one x).2
  have hp_id : ∀ x ∈ Set.Icc (0 : ℝ) 1, p x = x := fun x hx => by
    simp only [p, Set.projIcc_of_mem _ hx]
  have hp_mono : Monotone p := fun a b h => Set.monotone_projIcc zero_le_one h
  have hp_cont : Continuous p := continuous_subtype_val.comp continuous_projIcc
  let G : ℝ → ℝ → ℝ := fun s t => u (K (p t) \ K (p s))
  have hGc : Continuous (fun q : ℝ × ℝ => G q.1 q.2) :=
    hsq.comp_continuous ((hp_cont.comp continuous_fst).prodMk (hp_cont.comp continuous_snd))
      (fun q => ⟨hp_mem _, hp_mem _⟩)
  have hG0 : ∀ s t, 0 ≤ G s t := fun s t =>
    u_nonneg hu hinc (piece_share hK (hp_mem s) (hp_mem t))
  have hGle : ∀ s t, t ≤ s → G s t = 0 := by
    intro s t hts
    have hsub : K (p t) ⊆ K (p s) := knife_mono hK (hp_mem t).1 (hp_mono hts) (hp_mem s).2
    simp only [G, Set.sdiff_eq_empty.2 hsub, hu.1]
  have hGmono : ∀ s t t', t ≤ t' → G s t ≤ G s t' := by
    intro s t t' h
    exact hinc _ _ (piece_share hK (hp_mem s) (hp_mem t)) (piece_share hK (hp_mem s) (hp_mem t'))
      (Set.diff_subset_diff_left (knife_mono hK (hp_mem t).1 (hp_mono h) (hp_mem t').2))
  have hGanti : ∀ s s' t, s ≤ s' → G s' t ≤ G s t := by
    intro s s' t h
    exact hinc _ _ (piece_share hK (hp_mem s') (hp_mem t)) (piece_share hK (hp_mem s) (hp_mem t))
      (Set.diff_subset_diff_right (knife_mono hK (hp_mem s).1 (hp_mono h) (hp_mem s').2))
  have hGu : ∀ s t, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → G s t = u (K t \ K s) := by
    intro s t hs ht
    simp only [G, hp_id s hs, hp_id t ht]
  have gmono : ∀ (N : ℕ) (f : ℕ → ℝ), (∀ k < N, f k ≤ f (k + 1)) → ∀ i j, i ≤ j → j ≤ N →
      f i ≤ f j := by
    intro N f hf i j hij hjN
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hf j (by omega))
  -- main induction on the number of pieces
  have main : ∀ m : ℕ, ∃ W : ℝ → ℝ, Continuous W ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, a ≤ b → W b ≤ W a) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ f : ℕ → ℝ, f 0 = s ∧ f (m + 1) = 1 ∧
        (∀ k < m + 1, f k ≤ f (k + 1)) ∧ ∀ k < m + 1, G (f k) (f (k + 1)) = W s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ f : ℕ → ℝ, f 0 = s → f (m + 1) = 1 →
        (∀ k < m + 1, f k ≤ f (k + 1)) → ∃ k < m + 1, G (f k) (f (k + 1)) ≤ W s) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun s => G s 1, hGc.comp (continuous_id.prodMk continuous_const), ?_, ?_, ?_⟩
      · intro a _ b _ hab
        exact hGanti a b 1 hab
      · intro s hs
        refine ⟨fun k => if k = 0 then s else 1, by simp, by simp, ?_, ?_⟩
        · intro k hk
          obtain rfl : k = 0 := by omega
          simp [hs.2]
        · intro k hk
          obtain rfl : k = 0 := by omega
          simp
      · intro s hs f hf0 hf1 _
        exact ⟨0, by omega, by rw [hf0, zero_add, hf1]⟩
    | succ m ih =>
      obtain ⟨W, hWc, hWanti, hWeq, hWub⟩ := ih
      have hW0 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ W s := by
        intro s hs
        obtain ⟨f, -, -, -, hfe⟩ := hWeq s hs
        rw [← hfe 0 (by omega)]
        exact hG0 _ _
      have hW1 : W 1 = 0 := by
        obtain ⟨f, hf0, hf1, hfm, hfe⟩ := hWeq 1 ⟨zero_le_one, le_rfl⟩
        rw [← hfe 0 (by omega), hf0]
        apply hGle
        rw [← hf1]
        exact gmono (m + 1) f hfm 1 (m + 1) (by omega) le_rfl
      let H : ℝ → ℝ → ℝ := fun s t => min (G s t) (W t)
      have hHc : Continuous (fun q : ℝ × ℝ => H q.1 q.2) := hGc.min (hWc.comp continuous_snd)
      let W' : ℝ → ℝ := fun s => sSup ((H s) '' Set.Icc (0 : ℝ) 1)
      have hW'c : Continuous W' := isCompact_Icc.continuous_sSup hHc
      have hbdd : ∀ s, BddAbove ((H s) '' Set.Icc (0 : ℝ) 1) := fun s =>
        isCompact_Icc.bddAbove_image (hHc.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hne : ∀ s, ((H s) '' Set.Icc (0 : ℝ) 1).Nonempty := fun s =>
        ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      -- crossing point
      have hcross : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc s 1, G s t = W t ∧ W' s = W t := by
        intro s hs
        have hφc : Continuous (fun t => G s t - W t) :=
          (hGc.comp (continuous_const.prodMk continuous_id)).sub hWc
        obtain ⟨t, ht, htv⟩ := intermediate_value_Icc hs.2 hφc.continuousOn
          (show (0 : ℝ) ∈ Set.Icc (G s s - W s) (G s 1 - W 1) from
            ⟨by rw [hGle s s le_rfl]; linarith [hW0 s hs], by rw [hW1]; linarith [hG0 s 1]⟩)
        have hGW : G s t = W t := by
          have : G s t - W t = 0 := htv
          linarith
        have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
        refine ⟨t, ht, hGW, le_antisymm ?_ ?_⟩
        · apply csSup_le (hne s)
          rintro y ⟨t', ht', rfl⟩
          rcases le_total t' t with h | h
          · exact (min_le_left _ _).trans ((hGmono s t' t h).trans hGW.le)
          · exact (min_le_right _ _).trans (hWanti t ht01 t' ht' h)
        · refine le_trans ?_ (le_csSup (hbdd s) ⟨t, ht01, rfl⟩)
          show W t ≤ min (G s t) (W t)
          rw [hGW, min_self]
      refine ⟨W', hW'c, ?_, ?_, ?_⟩
      · intro a ha b hb hab
        apply csSup_le (hne b)
        rintro y ⟨t, ht, rfl⟩
        refine le_trans ?_ (le_csSup (hbdd a) ⟨t, ht, rfl⟩)
        exact min_le_min_right _ (hGanti a b t hab)
      · intro s hs
        obtain ⟨t, ht, hGW, hW'⟩ := hcross s hs
        have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
        obtain ⟨f', hf0, hf1, hfm, hfe⟩ := hWeq t ht01
        refine ⟨fun k => if k = 0 then s else f' (k - 1), by simp, by simpa using hf1, ?_, ?_⟩
        · intro k hk
          rcases k with _ | k
          · simp [hf0, ht.1]
          · simpa using hfm k (by omega)
        · intro k hk
          rcases k with _ | k
          · simp only [if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, zero_add,
              Nat.sub_self]
            rw [hf0, hGW, hW']
          · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
            rw [hfe k (by omega), hW']
      · intro s hs f hf0 hf1 hfm
        obtain ⟨t, ht, hGW, hW'⟩ := hcross s hs
        have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
        rcases le_total (f 1) t with h | h
        · refine ⟨0, by omega, ?_⟩
          rw [hf0, zero_add, hW', ← hGW]
          exact hGmono s _ _ h
        · have hf1mem : f 1 ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨ht01.1.trans h, hf1 ▸ gmono (m + 1 + 1) f hfm 1 (m + 1 + 1) (by omega) le_rfl⟩
          obtain ⟨k, hk, hkle⟩ := hWub (f 1) hf1mem (fun k => f (k + 1)) rfl
            (by simpa using hf1) (fun k hk => hfm (k + 1) (by omega))
          refine ⟨k + 1, by omega, ?_⟩
          rw [hW']
          exact hkle.trans (hWanti t ht01 (f 1) hf1mem h)
  obtain ⟨W, -, -, hWeq, hWub⟩ := main (n - 1)
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  rw [hn] at hWeq hWub
  obtain ⟨f, hf0, hf1, hfm, hfe⟩ := hWeq 0 ⟨le_rfl, zero_le_one⟩
  have hc : IsChain n f := ⟨hf0, hf1, hfm⟩
  have hval : ∀ k : Fin n, u (K (f (k.val + 1)) \ K (f k.val)) = W 0 := by
    intro k
    rw [← hGu _ _ (chain_mem hc (show k.val ≤ n by omega)) (chain_mem hc (show k.val + 1 ≤ n by omega))]
    exact hfe k k.isLt
  refine ⟨fun k => f k.val, upsilon_of_chain hc, W 0, fun k => hval k, le_antisymm ?_ ?_⟩
  · exact (le_ciInf fun k => (hval k).ge).trans (le_gammaK hu hK hc)
  · apply csSup_le (gamma_nonempty n _)
    rintro y ⟨τ, hτ, rfl⟩
    obtain ⟨g, hg, hgeq⟩ := chain_of_upsilon hτ
    obtain ⟨k, hk, hkle⟩ := hWub 0 ⟨le_rfl, zero_le_one⟩ g hg.1 hg.2.1 hg.2.2
    calc (⨅ j : Fin n, uKnife u K (τ j.castSucc) (τ j.succ))
        ≤ uKnife u K (τ (⟨k, hk⟩ : Fin n).castSucc) (τ (⟨k, hk⟩ : Fin n).succ) :=
          ciInf_le (Finite.bddBelow_range _) _
      _ = G (g k) (g (k + 1)) := by
          rw [(hgeq ⟨k, hk⟩).1, (hgeq ⟨k, hk⟩).2,
            hGu _ _ (chain_mem hg (show k ≤ n by omega)) (chain_mem hg (show k + 1 ≤ n by omega))]
          rfl
      _ ≤ W 0 := hkle


lemma ball_iUnion (S : Set (E d)) (r₀ : ℝ) : S ∩ Metric.ball (0 : E d) r₀ =
    ⋃ n : ℕ, S ∩ Metric.closedBall (0 : E d) (r₀ - 1 / ((n : ℝ) + 1)) := by
  ext x
  simp only [Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion]
  constructor
  · rintro ⟨hxA, hlt⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    exact ⟨n, hxA, by linarith⟩
  · rintro ⟨n, hxA, hle⟩
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨hxA, by linarith⟩

lemma closedBall_iInter (S : Set (E d)) (r₀ : ℝ) : S ∩ Metric.closedBall (0 : E d) r₀ =
    ⋂ n : ℕ, S ∩ Metric.closedBall (0 : E d) (r₀ + 1 / ((n : ℝ) + 1)) := by
  ext x
  simp only [Set.mem_inter_iff, Metric.mem_closedBall, Set.mem_iInter]
  constructor
  · rintro ⟨hxA, hle⟩ n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨hxA, by linarith⟩
  · intro h
    refine ⟨(h 0).1, ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
    have := (h n).2
    linarith

lemma cont_ball_vol (hd : 0 < d) {S : Set (E d)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤) :
    Continuous (fun r : ℝ => (volume (S ∩ Metric.closedBall (0 : E d) r)).toReal) := by
  have : Nontrivial (E d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [hd])
  have hne : ∀ X ⊆ S, volume X ≠ ⊤ := fun X hX => ne_top_of_le_ne_top hfin (measure_mono hX)
  set ψ : ℝ → ℝ := fun r => (volume (S ∩ Metric.closedBall (0 : E d) r)).toReal with hψ
  have hmono : Monotone ψ := fun a b hab => ENNReal.toReal_mono (hne _ Set.inter_subset_left)
    (measure_mono (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hab)))
  rw [Metric.continuous_iff]
  intro b ε hε
  -- value at b equals the value of the open ball
  have hball : (volume (S ∩ Metric.ball (0 : E d) b)).toReal = ψ b := by
    apply le_antisymm
    · exact ENNReal.toReal_mono (hne _ Set.inter_subset_left)
        (measure_mono (Set.inter_subset_inter_right _ Metric.ball_subset_closedBall))
    · apply ENNReal.toReal_mono (hne _ Set.inter_subset_left)
      calc volume (S ∩ Metric.closedBall (0 : E d) b)
          ≤ volume ((S ∩ Metric.ball (0 : E d) b) ∪ Metric.sphere 0 b) := by
            apply measure_mono
            rintro x ⟨hxA, hx⟩
            rw [← Metric.ball_union_sphere] at hx
            rcases hx with hx | hx
            · exact Or.inl ⟨hxA, hx⟩
            · exact Or.inr hx
        _ ≤ volume (S ∩ Metric.ball (0 : E d) b) + volume (Metric.sphere (0 : E d) b) :=
            measure_union_le _ _
        _ = volume (S ∩ Metric.ball (0 : E d) b) := by
            rw [Measure.addHaar_sphere (μ := volume), add_zero]
  -- left approximation
  have hmonoU : Monotone fun n : ℕ => S ∩ Metric.closedBall (0 : E d) (b - 1 / ((n : ℝ) + 1)) := by
    intro a c hac
    apply Set.inter_subset_inter_right
    apply Metric.closedBall_subset_closedBall
    have := Nat.one_div_le_one_div (α := ℝ) hac
    linarith
  have hU := tendsto_measure_iUnion_atTop (μ := volume) hmonoU
  rw [← ball_iUnion] at hU
  have hL := (ENNReal.tendsto_toReal (hne _ Set.inter_subset_left)).comp hU
  rw [hball] at hL
  obtain ⟨n, hn⟩ := (hL.eventually (eventually_gt_nhds (show ψ b - ε < ψ b by linarith))).exists
  -- right approximation
  have hantiI : Antitone fun n : ℕ => S ∩ Metric.closedBall (0 : E d) (b + 1 / ((n : ℝ) + 1)) := by
    intro a c hac
    apply Set.inter_subset_inter_right
    apply Metric.closedBall_subset_closedBall
    have := Nat.one_div_le_one_div (α := ℝ) hac
    linarith
  have hI := tendsto_measure_iInter_atTop (μ := volume)
      (fun n => (hS.inter Metric.isClosed_closedBall.measurableSet).nullMeasurableSet) hantiI
      ⟨0, hne _ Set.inter_subset_left⟩
  rw [← closedBall_iInter] at hI
  have hR := (ENNReal.tendsto_toReal (hne _ Set.inter_subset_left)).comp hI
  obtain ⟨n', hn'⟩ := (hR.eventually (eventually_lt_nhds (show ψ b < ψ b + ε by linarith))).exists
  have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hp' : (0 : ℝ) < 1 / ((n' : ℝ) + 1) := by positivity
  refine ⟨min (1 / ((n : ℝ) + 1)) (1 / ((n' : ℝ) + 1)), lt_min hp hp', fun a ha => ?_⟩
  rw [Real.dist_eq] at ha ⊢
  have ha1 := (abs_lt.1 ha).1
  have ha2 := (abs_lt.1 ha).2
  have hm1 := min_le_left (1 / ((n : ℝ) + 1)) (1 / ((n' : ℝ) + 1))
  have hm2 := min_le_right (1 / ((n : ℝ) + 1)) (1 / ((n' : ℝ) + 1))
  have hn1 : ψ b - ε < ψ (b - 1 / ((n : ℝ) + 1)) := hn
  have hn2 : ψ (b + 1 / ((n' : ℝ) + 1)) < ψ b + ε := hn'
  rw [abs_lt]
  rcases le_total a b with hab | hab
  · have h1 := hmono hab
    have h2 := hmono (show b - 1 / ((n : ℝ) + 1) ≤ a by linarith)
    constructor <;> linarith
  · have h1 := hmono hab
    have h2 := hmono (show a ≤ b + 1 / ((n' : ℝ) + 1) by linarith)
    constructor <;> linarith


lemma delta_nested {A B : Set (E d)} (hA : MeasurableSet A) (hAB : A ⊆ B)
    (hB : volume B ≠ ⊤) : δ A B = (volume B).toReal - (volume A).toReal := by
  unfold δ
  rw [symmDiff_of_le hAB, measure_sdiff hAB hA.nullMeasurableSet
    (ne_top_of_le_ne_top hB (measure_mono hAB)),
    ENNReal.toReal_sub_of_le (measure_mono hAB) hB]

lemma u_null {Ω : Set (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {A B : Set (E d)}
    (hA : IsShare Ω A) (hB : IsShare Ω B) (hAB : A ⊆ B) (h0 : volume (B \ A) = 0) :
    u A = u B := by
  by_contra hne
  have hε : 0 < |u A - u B| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨η, hη, hηu⟩ := hu.2.2 B hB _ hε
  have hδ : δ B A = 0 := by
    unfold δ
    rw [measure_mono_null (fun x hx => ?_) h0, ENNReal.toReal_zero]
    rcases Set.mem_symmDiff.1 hx with h | h
    · exact h
    · exact absurd (hAB h.1) h.2
  have := hηu A hA (by rw [hδ]; exact hη)
  exact lt_irrefl _ this

lemma pigeon {n : ℕ} [NeZero n] {f : ℕ → ℝ} (hf : IsChain n f) :
    ∃ k < n, ∃ j : ℕ, j < n ∧ (j : ℝ) ≤ n * f k ∧ n * f (k + 1) ≤ j + 1 := by
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have key : ∀ k, 1 ≤ k → k ≤ n → (k : ℝ) < n * f k := by
    intro k hk1 hkn
    induction k, hk1 using Nat.le_induction with
    | base =>
      have := hcon 0 (NeZero.pos n) 0 (NeZero.pos n) (by rw [hf.1]; simp)
      simpa using this
    | succ k hk ih =>
      have ihk := ih (by omega)
      have hfk0 : 0 ≤ f k := (chain_mem hf (show k ≤ n by omega)).1
      have hfk1 : f (k + 1) ≤ 1 := (chain_mem hf (show k + 1 ≤ n by omega)).2
      have hj1 : ((⌊(n : ℝ) * f k⌋₊ : ℕ) : ℝ) ≤ n * f k := Nat.floor_le (by positivity)
      have hkj : k ≤ ⌊(n : ℝ) * f k⌋₊ := Nat.le_floor ihk.le
      by_cases hjn : ⌊(n : ℝ) * f k⌋₊ < n
      · have h1 := hcon k (by omega) _ hjn hj1
        have h2 : (k : ℝ) ≤ ⌊(n : ℝ) * f k⌋₊ := by exact_mod_cast hkj
        push_cast
        linarith
      · push Not at hjn
        have h3 : (n : ℝ) ≤ n * f k := le_trans (by exact_mod_cast hjn) hj1
        have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
          rw [Nat.cast_sub (NeZero.pos n), Nat.cast_one]
          ring
        have h1 := hcon k (by omega) (n - 1) (by omega) (by linarith)
        rw [hcast] at h1
        nlinarith
  have := key n (NeZero.pos n) le_rfl
  rw [hf.2.1] at this
  simp at this

lemma knife_of_partition (hd : 0 < d) {Ω : Set (E d)} (hΩ : IsManna Ω) {n : ℕ} [NeZero n]
    {P : Fin n → Set (E d)} (hP : IsPartition Ω Ω n P) :
    ∃ (K : ℝ → Set (E d)) (P' : Fin n → Set (E d)), WKnife Ω K ∧
      (∀ j, P' j ⊆ P j ∧ volume (P j \ P' j) = 0 ∧ MeasurableSet (P' j)) ∧
      (∀ (j : Fin n) (a b : ℝ), (j : ℝ) ≤ n * a → n * b ≤ j + 1 → K b \ K a ⊆ P' j) ∧
      (∀ j : Fin n, P' j ⊆ K (((j : ℝ) + 1) / n) \ K ((j : ℝ) / n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E d)).1 hΩ.2.1
  set R := max R0 0 with hRdef
  have hR : Ω ⊆ Metric.closedBall (0 : E d) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR0' : 0 ≤ R := le_max_right _ _
  have hnorm : ∀ x ∈ Ω, ‖x‖ ≤ R := fun x hx => mem_closedBall_zero_iff.1 (hR hx)
  let P' : Fin n → Set (E d) := fun j => P j \ ⋃ (l : Fin n) (_ : l < j), P l
  have hP'sub : ∀ j, P' j ⊆ P j := fun j => Set.sdiff_subset
  have hP'Ω : ∀ j, P' j ⊆ Ω := fun j => (hP'sub j).trans (hP.1 j).2
  have hP'm : ∀ j, MeasurableSet (P' j) := fun j =>
    (hP.1 j).1.1.diff (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ => (hP.1 l).1.1)
  have hP'null : ∀ j, volume (P j \ P' j) = 0 := by
    intro j
    refine measure_mono_null (t := ⋃ (l : Fin n) (_ : l < j), P j ∩ P l) ?_ ?_
    · intro x hx
      have hx2 : x ∈ ⋃ (l : Fin n) (_ : l < j), P l := by
        by_contra h
        exact hx.2 ⟨hx.1, h⟩
      simp only [Set.mem_iUnion] at hx2 ⊢
      obtain ⟨l, hl, hxl⟩ := hx2
      exact ⟨l, hl, hx.1, hxl⟩
    · exact measure_iUnion_null fun l => measure_iUnion_null fun hl => hP.2.2 j l (ne_of_gt hl)
  have hP'disj : ∀ i j, i ≠ j → Disjoint (P' i) (P' j) := by
    have h : ∀ i j : Fin n, i < j → Disjoint (P' i) (P' j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hxi hxj
      apply hxj.2
      simp only [Set.mem_iUnion]
      exact ⟨i, hij, hxi.1⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact h i j h'
    · exact (h j i h').symm
  have hP'cover : ∀ x ∈ Ω, ∃ j, x ∈ P' j := by
    classical
    intro x hx
    rw [← hP.2.1] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    have hne : (Finset.univ.filter (fun l : Fin n => x ∈ P l)).Nonempty :=
      ⟨i, by simp [hi]⟩
    set j := (Finset.univ.filter (fun l : Fin n => x ∈ P l)).min' hne with hj
    have hjmem := Finset.min'_mem _ hne
    rw [← hj] at hjmem
    refine ⟨j, (Finset.mem_filter.1 hjmem).2, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro l hl hxl
    have := Finset.min'_le (Finset.univ.filter (fun l : Fin n => x ∈ P l)) l (by simp [hxl])
    rw [← hj] at this
    exact absurd hl (not_lt.2 this)
  let rad : Fin n → ℝ → ℝ := fun j t => (R + 1) * (n * t - j) - 1
  let K : ℝ → Set (E d) := fun t => ⋃ j : Fin n, (P' j ∩ Metric.closedBall (0 : E d) (rad j t))
  have hmemK : ∀ x t, x ∈ K t ↔ ∃ j, x ∈ P' j ∧ ‖x‖ ≤ rad j t := by
    intro x t
    simp only [K, Set.mem_iUnion, Set.mem_inter_iff, mem_closedBall_zero_iff]
  have hKm : ∀ t, MeasurableSet (K t) := fun t =>
    MeasurableSet.iUnion fun j => (hP'm j).inter Metric.isClosed_closedBall.measurableSet
  have hKΩ : ∀ t, K t ⊆ Ω := fun t =>
    Set.iUnion_subset fun j => Set.inter_subset_left.trans (hP'Ω j)
  have hKmono : ∀ t t', t ≤ t' → K t ⊆ K t' := by
    intro t t' h
    apply Set.iUnion_mono
    intro j
    apply Set.inter_subset_inter_right
    apply Metric.closedBall_subset_closedBall
    have : (R + 1) * (n * t - j) ≤ (R + 1) * (n * t' - j) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    simp only [rad]
    linarith
  -- volume of K t as a sum
  have hfinP : ∀ j, volume (P' j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hΩ.2.1.measure_lt_top.ne (measure_mono (hP'Ω j))
  let Ψ : ℝ → ℝ := fun t => ∑ j : Fin n,
    (volume (P' j ∩ Metric.closedBall (0 : E d) (rad j t))).toReal
  have hΨc : Continuous Ψ := by
    apply continuous_finsetSum
    intro j _
    have h1 := cont_ball_vol hd (hP'm j) (hfinP j)
    have h2 : Continuous (rad j) := by
      simp only [rad]
      fun_prop
    exact h1.comp h2
  have hvolK : ∀ t, (volume (K t)).toReal = Ψ t := by
    intro t
    simp only [K, Ψ]
    rw [measure_iUnion (fun i j hij => ((hP'disj i j hij).mono Set.inter_subset_left
      Set.inter_subset_left)) (fun j => (hP'm j).inter Metric.isClosed_closedBall.measurableSet),
      tsum_fintype, ENNReal.toReal_sum]
    intro j _
    exact ne_top_of_le_ne_top (hfinP j) (measure_mono Set.inter_subset_left)
  have hfinK : ∀ t, volume (K t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hΩ.2.1.measure_lt_top.ne (measure_mono (hKΩ t))
  have hδK : ∀ t s, δ (K t) (K s) = |Ψ t - Ψ s| := by
    intro t s
    rcases le_total t s with h | h
    · rw [delta_nested (hKm t) (hKmono t s h) (hfinK s), hvolK, hvolK, abs_sub_comm,
        abs_of_nonneg]
      rw [← hvolK, ← hvolK]
      exact sub_nonneg.2 (ENNReal.toReal_mono (hfinK s) (measure_mono (hKmono t s h)))
    · have hc : δ (K t) (K s) = δ (K s) (K t) := by unfold δ; rw [symmDiff_comm]
      rw [hc, delta_nested (hKm s) (hKmono s t h) (hfinK t), hvolK, hvolK, abs_of_nonneg]
      rw [← hvolK, ← hvolK]
      exact sub_nonneg.2 (ENNReal.toReal_mono (hfinK t) (measure_mono (hKmono s t h)))
  refine ⟨K, P', ⟨?_, ?_, ?_, ?_, ?_⟩, fun j => ⟨hP'sub j, hP'null j, hP'm j⟩, ?_, ?_⟩
  · -- K 0 = ∅
    ext x
    simp only [hmemK, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro j _ hx
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have : rad j 0 < 0 := by
      simp only [rad]
      nlinarith
    linarith [norm_nonneg x]
  · -- K 1 = Ω
    apply Set.Subset.antisymm (hKΩ 1)
    intro x hx
    obtain ⟨j, hj⟩ := hP'cover x hx
    rw [hmemK]
    refine ⟨j, hj, ?_⟩
    have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have : R ≤ rad j 1 := by
      simp only [rad]
      nlinarith
    exact (hnorm x hx).trans this
  · intro t _
    exact ⟨hKm t, hKΩ t⟩
  · intro s _ ε hε
    obtain ⟨η, hη, hηΨ⟩ := Metric.continuous_iff.1 hΨc s ε hε
    refine ⟨η, hη, fun t _ ht => ?_⟩
    rw [hδK]
    have := hηΨ t (by rw [Real.dist_eq]; exact ht)
    rwa [Real.dist_eq] at this
  · intro t t' _ h _
    exact hKmono t t' h
  · -- pieces inside a block lie in P' j
    intro j a b ha hb x hx
    obtain ⟨hxb, hxa⟩ := hx
    obtain ⟨i, hxi, hri⟩ := (hmemK x b).1 hxb
    have hR1 : (0 : ℝ) < R + 1 := by linarith
    rcases lt_trichotomy i j with hij | hij | hij
    · exfalso
      apply hxa
      rw [hmemK]
      refine ⟨i, hxi, (hnorm x (hP'Ω i hxi)).trans ?_⟩
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      simp only [rad]
      nlinarith
    · rw [← hij]; exact hxi
    · exfalso
      have hij' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
      have : rad i b ≤ -1 := by
        simp only [rad]
        nlinarith
      linarith [norm_nonneg x]
  · -- P' j lies in the j-th block
    intro j x hx
    have hR1 : (0 : ℝ) < R + 1 := by linarith
    constructor
    · rw [hmemK]
      refine ⟨j, hx, (hnorm x (hP'Ω j hx)).trans ?_⟩
      have : (n : ℝ) * (((j : ℝ) + 1) / n) = j + 1 := by field_simp
      simp only [rad, this]
      nlinarith
    · rw [hmemK]
      rintro ⟨i, hxi, hri⟩
      have hij : i = j := by
        by_contra h
        exact Set.disjoint_left.1 (hP'disj i j h) hxi hx
      subst hij
      have : (n : ℝ) * ((i : ℝ) / n) = i := by field_simp
      simp only [rad, this, sub_self, mul_zero, zero_sub] at hri
      linarith [norm_nonneg x]

lemma key_ep (hd : 0 < d) {Ω : Set (E d)} (hΩ : IsManna Ω) {u : Set (E d) → ℝ}
    (hu : IsUtility Ω u) (hinc : IsIncreasing Ω u) {n : ℕ} [NeZero n]
    {P : Fin n → Set (E d)} (hP : IsPartition Ω Ω n P) :
    ∃ Q : Fin n → Set (E d), IsEquipartition Ω u Ω n Q ∧
      ⨅ i, u (P i) ≤ u (Q ⟨0, NeZero.pos n⟩) ∧ u (Q ⟨0, NeZero.pos n⟩) ≤ ⨆ i, u (P i) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  obtain ⟨K, P', hK, hP', hsub, hsup⟩ := knife_of_partition hd hΩ hP
  obtain ⟨τ, hτ, c, hc, hcΓ⟩ := l4ii_weak (n := n) hd hΩ hu hinc hK
  obtain ⟨f, hf, hfeq⟩ := chain_of_upsilon hτ
  have hval : ∀ k : Fin n, u (K (f (k.val + 1)) \ K (f k.val)) = c := by
    intro k
    rw [← (hfeq k).1, ← (hfeq k).2]
    exact hc k
  have hP'share : ∀ j, IsShare Ω (P' j) := fun j =>
    ⟨(hP' j).2.2, (hP' j).1.trans (hP.1 j).2⟩
  have huP' : ∀ j, u (P' j) = u (P j) := fun j =>
    u_null hu (hP'share j) (hP.1 j).1 (hP' j).1 (hP' j).2.1
  refine ⟨fun k => K (f (k.val + 1)) \ K (f k.val),
    ⟨knife_partition hK hf, fun i j => (hval i).trans (hval j).symm⟩, ?_, ?_⟩
  · -- lower bound via the block chain `j / n`
    let g : ℕ → ℝ := fun j => (j : ℝ) / n
    have hg : IsChain n g := by
      refine ⟨by simp [g], by simp [g, hnpos.ne'], ?_⟩
      intro k _
      simp only [g]
      apply div_le_div_of_nonneg_right _ hnpos.le
      push_cast
      linarith
    have h1 := le_gammaK hu hK hg
    rw [← hcΓ] at h1
    rw [hval]
    refine le_trans ?_ h1
    apply le_ciInf
    intro j
    have hb := hsup j
    have hgj : g (j.val + 1) = ((j : ℝ) + 1) / n := by simp [g]
    rw [hgj]
    calc ⨅ i, u (P i) ≤ u (P j) := ciInf_le (Finite.bddBelow_range _) j
      _ = u (P' j) := (huP' j).symm
      _ ≤ u (K (((j : ℝ) + 1) / n) \ K ((j : ℝ) / n)) := by
          have hj1 : ((j : ℝ) + 1) / n ∈ Set.Icc (0 : ℝ) 1 := by
            have := hg.2.2
            exact ⟨by positivity, by
              rw [div_le_one hnpos]; exact_mod_cast j.isLt⟩
          have hj0 : (j : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨by positivity, by rw [div_le_one hnpos]; exact_mod_cast j.isLt.le⟩
          exact hinc _ _ (hP'share j) (piece_share hK hj0 hj1) hb
  · -- upper bound via pigeonhole
    obtain ⟨k, hk, j, hj, h1, h2⟩ := pigeon hf
    have hin := hsub ⟨j, hj⟩ (f k) (f (k + 1)) h1 h2
    rw [hval]
    rw [← hval ⟨k, hk⟩]
    calc u (K (f (k + 1)) \ K (f k)) ≤ u (P' ⟨j, hj⟩) :=
          hinc _ _ (piece_share hK (chain_mem hf (show k ≤ n by omega))
            (chain_mem hf (show k + 1 ≤ n by omega))) (hP'share _) hin
      _ = u (P ⟨j, hj⟩) := huP' _
      _ ≤ ⨆ i, u (P i) := le_ciSup (f := fun i => u (P i)) (Finite.bddAbove_range _) _

end FGThm2iiiAux

open FGThm2iiiAux in
theorem solution {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u) :
    FairGuarantees.DivideChoose.minMax Ω u n = sInf {x | ∃ P : Fin n → Set (FairGuarantees.DivideChoose.E d), FairGuarantees.DivideChoose.IsEquipartition Ω u Ω n P ∧
        x = u (P ⟨0, Nat.pos_of_neZero n⟩)} ∧
    FairGuarantees.DivideChoose.Maxmin Ω u n = sSup {x | ∃ P : Fin n → Set (FairGuarantees.DivideChoose.E d), FairGuarantees.DivideChoose.IsEquipartition Ω u Ω n P ∧
        x = u (P ⟨0, Nat.pos_of_neZero n⟩)} := by
  -- the trivial partition
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
  obtain ⟨C, hC⟩ := u_le hu
  set EP := {x | ∃ P : Fin n → Set (E d), IsEquipartition Ω u Ω n P ∧
        x = u (P ⟨0, Nat.pos_of_neZero n⟩)} with hEP
  have hEPne : EP.Nonempty := by
    obtain ⟨Q, hQ, -, -⟩ := key_ep hd hΩ hu hinc hQ0
    exact ⟨_, Q, hQ, rfl⟩
  have hEPbdd : BddBelow EP := ⟨0, by
    rintro x ⟨P, hP, rfl⟩
    exact u_nonneg hu hinc (hP.1.1 _).1⟩
  have hEPbddA : BddAbove EP := ⟨C, by
    rintro x ⟨P, hP, rfl⟩
    exact hC _ (hP.1.1 _).1⟩
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · -- minMax ≤ inf over equipartitions
    refine le_csInf hEPne ?_
    rintro x ⟨P, hP, rfl⟩
    exact (minmax_le hu hinc hP.1).trans (ciSup_le fun i => (hP.2 i _).le)
  · -- inf over equipartitions ≤ minMax
    unfold minMax
    refine le_csInf ⟨_, Q0, hQ0, rfl⟩ ?_
    rintro y ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, -, hQle⟩ := key_ep hd hΩ hu hinc hP
    exact (csInf_le hEPbdd ⟨Q, hQ, rfl⟩).trans hQle
  · -- Maxmin ≤ sup over equipartitions
    unfold Maxmin
    refine csSup_le ⟨_, Q0, hQ0, rfl⟩ ?_
    rintro y ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, hQge, -⟩ := key_ep hd hΩ hu hinc hP
    exact hQge.trans (le_csSup hEPbddA ⟨Q, hQ, rfl⟩)
  · -- sup over equipartitions ≤ Maxmin
    refine csSup_le hEPne ?_
    rintro x ⟨P, hP, rfl⟩
    exact (le_ciInf fun i => (hP.2 _ i).le).trans (le_maxmin hu hP.1)
