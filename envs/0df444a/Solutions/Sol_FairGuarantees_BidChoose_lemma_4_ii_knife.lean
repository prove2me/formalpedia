-- Prove2me | solution 1 for FairGuarantees.BidChoose.lemma_4_ii_knife
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:47:06.183195+00:00
-- url     : https://prove2.me/submissions/a9e442b3-6352-4f6a-aa4b-1b5dc68d85ab

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
theorem solution {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) :
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
