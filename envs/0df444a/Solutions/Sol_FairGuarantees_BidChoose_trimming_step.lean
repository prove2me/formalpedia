-- Prove2me | solution 1 for FairGuarantees.BidChoose.trimming_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:43:12.335065+00:00
-- url     : https://prove2.me/submissions/202e937a-0874-44dc-8cd2-27bad7035b64

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

end FGThm2iiiAux

open FGThm2iiiAux in
theorem solution {d : ℕ} (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {S T : Set (FairGuarantees.DivideChoose.E d)} (hS : FairGuarantees.DivideChoose.IsShare Ω S) (hT : FairGuarantees.DivideChoose.IsShare Ω T) (hST : Disjoint S T)
    (hlt : u T < u S) :
    ∃ S' : Set (FairGuarantees.DivideChoose.E d), FairGuarantees.DivideChoose.IsShare Ω S' ∧ S' ⊆ S ∧
      u S' = u (T ∪ (S \ S')) ∧ u T ≤ u S' ∧ u S' ≤ u S := by
  have hΩfin : volume Ω ≠ ⊤ := hΩ.2.1.measure_lt_top.ne
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hΩfin (measure_mono hS.2)
  let X : ℝ → Set (E d) := fun r => S ∩ Metric.closedBall (0 : E d) r
  have hX : ∀ r, IsShare Ω (X r) := fun r =>
    ⟨hS.1.inter Metric.isClosed_closedBall.measurableSet, Set.inter_subset_left.trans hS.2⟩
  have hY : ∀ r, IsShare Ω (T ∪ (S \ X r)) := fun r =>
    ⟨hT.1.union (hS.1.diff (hX r).1), Set.union_subset hT.2 (Set.sdiff_subset.trans hS.2)⟩
  set ψ : ℝ → ℝ := fun r => (volume (S ∩ Metric.closedBall (0 : E d) r)).toReal with hψ
  have hψc : Continuous ψ := cont_ball_vol hd hS.1 hSfin
  have hfinX : ∀ r, volume (X r) ≠ ⊤ := fun r =>
    ne_top_of_le_ne_top hSfin (measure_mono Set.inter_subset_left)
  -- δ between two truncations
  have hδle : ∀ a b, a ≤ b → δ (X a) (X b) = ψ b - ψ a := by
    intro a b hab
    have hsub : X a ⊆ X b :=
      Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hab)
    unfold δ
    rw [symmDiff_of_le hsub, measure_sdiff hsub (hX a).1.nullMeasurableSet (hfinX a),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (hfinX b)]
  have hδabs : ∀ a b, δ (X a) (X b) = |ψ b - ψ a| := by
    intro a b
    rcases le_total a b with hab | hab
    · rw [hδle a b hab, abs_of_nonneg (by linarith [hδle a b hab, (show 0 ≤ δ (X a) (X b) from
        ENNReal.toReal_nonneg)])]
    · have h1 : δ (X a) (X b) = δ (X b) (X a) := by unfold δ; rw [symmDiff_comm]
      rw [h1, hδle b a hab, abs_sub_comm, abs_of_nonneg (by linarith [hδle b a hab,
        (show 0 ≤ δ (X b) (X a) from ENNReal.toReal_nonneg)])]
  have hδY : ∀ a b, δ (T ∪ (S \ X a)) (T ∪ (S \ X b)) ≤ δ (X a) (X b) := by
    intro a b
    unfold δ
    apply ENNReal.toReal_mono
    · refine ne_top_of_le_ne_top hSfin (measure_mono ?_)
      intro x hx
      rcases Set.mem_symmDiff.1 hx with h | h
      · exact h.1.1
      · exact h.1.1
    · apply measure_mono
      intro x hx
      simp only [X, Set.mem_symmDiff, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff] at hx ⊢
      tauto
  -- continuity of both utilities along the sweep
  have hcont : ∀ Z : ℝ → Set (E d), (∀ r, IsShare Ω (Z r)) →
      (∀ a b, δ (Z a) (Z b) ≤ |ψ b - ψ a|) → Continuous (fun r => u (Z r)) := by
    intro Z hZ hZδ
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨η, hη, hηu⟩ := hu.2.2 _ (hZ b) ε hε
    obtain ⟨δ', hδ', hψδ⟩ := Metric.continuous_iff.1 hψc b η hη
    refine ⟨δ', hδ', fun a ha => ?_⟩
    rw [Real.dist_eq]
    apply hηu _ (hZ a)
    have := hψδ a ha
    rw [Real.dist_eq] at this
    exact (hZδ b a).trans_lt this
  have hfc : Continuous (fun r => u (X r)) := hcont X hX fun a b => (hδabs a b).le
  have hgc : Continuous (fun r => u (T ∪ (S \ X r))) :=
    hcont (fun r => T ∪ (S \ X r)) hY fun a b => (hδY a b).trans (hδabs a b).le
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E d)).1 hΩ.2.1
  have hXneg : X (-1) = ∅ := by
    simp only [X, Metric.closedBall_eq_empty.2 (show (-1 : ℝ) < 0 by norm_num), Set.inter_empty]
  have hXR : X (max R 0) = S := by
    apply Set.Subset.antisymm Set.inter_subset_left
    intro x hx
    exact ⟨hx, Metric.closedBall_subset_closedBall (le_max_left R 0) (hR (hS.2 hx))⟩
  have hh := (hfc.sub hgc).continuousOn (s := Set.Icc (-1 : ℝ) (max R 0))
  have hle : (-1 : ℝ) ≤ max R 0 := by linarith [le_max_right R 0]
  have hTS : IsShare Ω (T ∪ S) := ⟨hT.1.union hS.1, Set.union_subset hT.2 hS.2⟩
  have hv1 : u (X (-1)) - u (T ∪ (S \ X (-1))) ≤ 0 := by
    rw [hXneg, Set.sdiff_empty, hu.1]
    linarith [u_nonneg hu hinc hTS]
  have hv2 : 0 ≤ u (X (max R 0)) - u (T ∪ (S \ X (max R 0))) := by
    rw [hXR, Set.sdiff_self, Set.union_empty]
    linarith
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc hle hh ⟨hv1, hv2⟩
  have hr' : u (X r) = u (T ∪ (S \ X r)) := by
    have : u (X r) - u (T ∪ (S \ X r)) = 0 := hr
    linarith
  refine ⟨X r, hX r, Set.inter_subset_left, hr', ?_, ?_⟩
  · rw [hr']
    exact hinc _ _ hT (hY r) Set.subset_union_left
  · exact hinc _ _ (hX r) hS Set.inter_subset_left
