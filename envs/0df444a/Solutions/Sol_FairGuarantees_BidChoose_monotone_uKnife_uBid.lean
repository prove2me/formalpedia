-- Prove2me | solution 1 for FairGuarantees.BidChoose.monotone_uKnife_uBid
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:40:54.655068+00:00
-- url     : https://prove2.me/submissions/479720cc-475b-47e2-aa05-6ccdf4d453d5

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


lemma atomless_ivt (hd : 0 < d) {Ω : Set (E d)} (hΩ : IsManna Ω) {θ : Measure (E d)}
    [IsFiniteMeasure θ] (hθc : θ Ωᶜ = 0) (hθ : θ ≪ volume.restrict Ω) {A : Set (E d)}
    (hA : MeasurableSet A) {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ (θ A).toReal) :
    ∃ B ⊆ A, MeasurableSet B ∧ (θ B).toReal = m := by
  rcases eq_or_lt_of_le hm with hmeq | hmlt
  · exact ⟨A, subset_rfl, hA, hmeq.symm⟩
  have : Nontrivial (E d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [hd])
  have hsph : ∀ r : ℝ, θ (Metric.sphere (0 : E d) r) = 0 := fun r =>
    hθ (le_antisymm ((Measure.restrict_apply_le _ _).trans
      (Measure.addHaar_sphere (μ := volume) 0 r).le) (zero_le))
  let φ : ℝ → ℝ := fun r => (θ (A ∩ Metric.closedBall (0 : E d) r)).toReal
  have hφmono : Monotone φ := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hab)))
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E d)).1 hΩ.2.1
  have hφR : φ R = (θ A).toReal := by
    apply le_antisymm
    · exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left)
    · apply ENNReal.toReal_mono (measure_ne_top _ _)
      calc θ A ≤ θ ((A ∩ Metric.closedBall 0 R) ∪ Ωᶜ) := by
            apply measure_mono
            intro x hx
            by_cases hxΩ : x ∈ Ω
            · exact Or.inl ⟨hx, hR hxΩ⟩
            · exact Or.inr hxΩ
        _ ≤ θ (A ∩ Metric.closedBall 0 R) + θ Ωᶜ := measure_union_le _ _
        _ = θ (A ∩ Metric.closedBall 0 R) := by rw [hθc, add_zero]
  let S : Set ℝ := {r | φ r ≤ m}
  have hS1 : (-1 : ℝ) ∈ S := by
    show φ (-1) ≤ m
    simp only [φ, Metric.closedBall_eq_empty.2 (show (-1 : ℝ) < 0 by norm_num), Set.inter_empty,
      measure_empty, ENNReal.toReal_zero]
    exact hm0
  have hSbdd : BddAbove S := by
    refine ⟨R, fun r hr => ?_⟩
    by_contra h
    push Not at h
    have := hφmono h.le
    have hr' : φ r ≤ m := hr
    linarith
  set r₀ := sSup S with hr₀
  -- the open ball has measure ≤ m
  have h1 : (θ (A ∩ Metric.ball (0 : E d) r₀)).toReal ≤ m := by
    have heq : A ∩ Metric.ball (0 : E d) r₀ =
        ⋃ n : ℕ, A ∩ Metric.closedBall (0 : E d) (r₀ - 1 / ((n : ℝ) + 1)) := by
      ext x
      simp only [Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion]
      constructor
      · rintro ⟨hxA, hlt⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        exact ⟨n, hxA, by linarith⟩
      · rintro ⟨n, hxA, hle⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact ⟨hxA, by linarith⟩
    have hmono : Monotone fun n : ℕ => A ∩ Metric.closedBall (0 : E d) (r₀ - 1 / ((n : ℝ) + 1)) := by
      intro a b hab
      apply Set.inter_subset_inter_right
      apply Metric.closedBall_subset_closedBall
      have := Nat.one_div_le_one_div (α := ℝ) hab
      linarith
    rw [heq, hmono.measure_iUnion]
    refine (ENNReal.le_ofReal_iff_toReal_le ?_ hm0).1 ?_
    · exact ne_top_of_le_ne_top (measure_ne_top θ Set.univ)
        (iSup_le fun n => measure_mono (Set.subset_univ _))
    · refine iSup_le fun n => ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨r, hrS, hr⟩ := exists_lt_of_lt_csSup ⟨-1, hS1⟩ (show r₀ - 1 / ((n : ℝ) + 1) < r₀ by linarith)
      have hle : φ (r₀ - 1 / ((n : ℝ) + 1)) ≤ m := (hφmono hr.le).trans hrS
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hm0).2 hle
  -- the closed ball has measure ≥ m
  have h2 : m ≤ (θ (A ∩ Metric.closedBall (0 : E d) r₀)).toReal := by
    have heq : A ∩ Metric.closedBall (0 : E d) r₀ =
        ⋂ n : ℕ, A ∩ Metric.closedBall (0 : E d) (r₀ + 1 / ((n : ℝ) + 1)) := by
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
    have hanti : Antitone fun n : ℕ => A ∩ Metric.closedBall (0 : E d) (r₀ + 1 / ((n : ℝ) + 1)) := by
      intro a b hab
      apply Set.inter_subset_inter_right
      apply Metric.closedBall_subset_closedBall
      have := Nat.one_div_le_one_div (α := ℝ) hab
      linarith
    rw [heq, hanti.measure_iInter (fun n => (hA.inter Metric.isClosed_closedBall.measurableSet).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    refine (ENNReal.ofReal_le_iff_le_toReal ?_).1 ?_
    · exact ne_top_of_le_ne_top (measure_ne_top θ (A ∩ Metric.closedBall 0 (r₀ + 1 / ((0 : ℕ) + 1))))
        (iInf_le _ 0)
    · refine le_iInf fun n => ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hnot : r₀ + 1 / ((n : ℝ) + 1) ∉ S := by
        intro hmem
        have := le_csSup hSbdd hmem
        linarith
      have hgt : m < φ (r₀ + 1 / ((n : ℝ) + 1)) := lt_of_not_ge hnot
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hgt.le
  refine ⟨A ∩ Metric.closedBall (0 : E d) r₀, Set.inter_subset_left,
    hA.inter Metric.isClosed_closedBall.measurableSet, le_antisymm ?_ h2⟩
  have : θ (A ∩ Metric.closedBall (0 : E d) r₀) ≤ θ (A ∩ Metric.ball (0 : E d) r₀) := by
    calc θ (A ∩ Metric.closedBall (0 : E d) r₀)
        ≤ θ ((A ∩ Metric.ball (0 : E d) r₀) ∪ Metric.sphere 0 r₀) := by
          apply measure_mono
          rintro x ⟨hxA, hx⟩
          rw [← Metric.ball_union_sphere] at hx
          rcases hx with hx | hx
          · exact Or.inl ⟨hxA, hx⟩
          · exact Or.inr hx
      _ ≤ θ (A ∩ Metric.ball (0 : E d) r₀) + θ (Metric.sphere 0 r₀) := measure_union_le _ _
      _ = θ (A ∩ Metric.ball (0 : E d) r₀) := by rw [hsph, add_zero]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) this).trans h1

end FGThm2iiiAux

namespace FGThm2iiiAux

variable {d : ℕ}

lemma meas_rest {Ω : Set (E d)} (hΩ : IsManna Ω) {θ : Measure (E d)} [IsFiniteMeasure θ]
    (hθ1 : θ Ω = 1) {U : Set (E d)} (hU : MeasurableSet U) (hUΩ : U ⊆ Ω) :
    (θ (Ω \ U)).toReal = 1 - (θ U).toReal := by
  rw [measure_diff hUΩ hU.nullMeasurableSet (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le (measure_mono hUΩ) (measure_ne_top _ _), hθ1, ENNReal.toReal_one]

lemma meas_union_real {θ : Measure (E d)} [IsFiniteMeasure θ] {S T : Set (E d)}
    (hST : Disjoint S T) (hT : MeasurableSet T) :
    (θ (S ∪ T)).toReal = (θ S).toReal + (θ T).toReal := by
  rw [measure_union hST hT, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

lemma inner_bdd {Ω : Set (E d)} {θ : Measure (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (T : Set (E d)) (m : ℝ) :
    BddAbove {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = m ∧ x = u S} := by
  obtain ⟨C, hC⟩ := u_le hu
  exact ⟨C, by rintro x ⟨S, hS, -, -, rfl⟩; exact hC S hS⟩

lemma inner_nonneg {Ω : Set (E d)} {θ : Measure (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (hinc : IsIncreasing Ω u) (T : Set (E d)) (m : ℝ) :
    0 ≤ sSup {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = m ∧ x = u S} := by
  apply Real.sSup_nonneg
  rintro x ⟨S, hS, -, -, rfl⟩
  exact u_nonneg hu hinc hS

lemma outer_bdd {Ω : Set (E d)} {θ : Measure (E d)} {u : Set (E d) → ℝ} (hu : IsUtility Ω u)
    (hinc : IsIncreasing Ω u) (t₁ t₂ : ℝ) :
    BddBelow {y | ∃ T, IsShare Ω T ∧ (θ T).toReal = t₁ ∧
      y = sSup {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = t₂ - t₁ ∧ x = u S}} := by
  refine ⟨0, ?_⟩
  rintro y ⟨T, -, -, rfl⟩
  exact inner_nonneg hu hinc T _

/-- `sSup A ≤ sSup B` when every element of `A` is dominated by an element of `B`, for sets of
utilities of shares. -/
lemma sSup_le_of_dom {A B : Set ℝ} (hB : BddAbove B) (h0 : 0 ≤ sSup B)
    (h : ∀ a ∈ A, ∃ b ∈ B, a ≤ b) : sSup A ≤ sSup B := by
  by_cases hA : A.Nonempty
  · apply csSup_le hA
    intro a ha
    obtain ⟨b, hb, hab⟩ := h a ha
    exact hab.trans (le_csSup hB hb)
  · rw [Set.not_nonempty_iff_eq_empty] at hA
    rw [hA, Real.sSup_empty]
    exact h0

end FGThm2iiiAux

open FGThm2iiiAux in
theorem solution {d : ℕ} (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) {θ : Measure (FairGuarantees.DivideChoose.E d)} (hθ : IsBenchmark Ω θ) :
    (∀ t₁ t₁' t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₁' → t₁' ≤ t₂ → t₂ ≤ 1 →
        uKnife u K t₁' t₂ ≤ uKnife u K t₁ t₂) ∧
    (∀ t₁ t₂ t₂' : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₂' → t₂' ≤ 1 →
        uKnife u K t₁ t₂ ≤ uKnife u K t₁ t₂') ∧
    (∀ t₁ t₁' t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₁' → t₁' ≤ t₂ → t₂ ≤ 1 →
        uBid Ω θ u t₁' t₂ ≤ uBid Ω θ u t₁ t₂) ∧
    (∀ t₁ t₂ t₂' : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₂' → t₂' ≤ 1 →
        uBid Ω θ u t₁ t₂ ≤ uBid Ω θ u t₁ t₂') := by
  have : IsFiniteMeasure θ := ⟨by
    rw [← measure_add_measure_compl hΩ.1, hθ.2.1, hθ.1]; simp⟩
  have hθc := hθ.1
  have hθ1 := hθ.2.1
  have hθac := hθ.2.2.1
  have hΩ1 : (θ Ω).toReal = 1 := by rw [hθ1, ENNReal.toReal_one]
  -- existence of a share of any measure in `[0, 1]`
  have hexT : ∀ t, 0 ≤ t → t ≤ 1 → ∃ T, IsShare Ω T ∧ (θ T).toReal = t := by
    intro t h0 h1
    obtain ⟨B, hBΩ, hB, hθB⟩ := atomless_ivt hd hΩ hθc hθac hΩ.1 h0 (by rw [hΩ1]; exact h1)
    exact ⟨B, ⟨hB, hBΩ⟩, hθB⟩
  -- monotonicity of the inner sup in the measure of the bid
  have hF : ∀ T, IsShare Ω T → ∀ t₁ t₂ t₂', (θ T).toReal = t₁ → t₁ ≤ t₂ → t₂ ≤ t₂' → t₂' ≤ 1 →
      sSup {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = t₂ - t₁ ∧ x = u S} ≤
      sSup {x | ∃ S, IsShare Ω S ∧ Disjoint S T ∧ (θ S).toReal = t₂' - t₁ ∧ x = u S} := by
    intro T hT t₁ t₂ t₂' hθT h12 h22 h2
    apply sSup_le_of_dom (inner_bdd hu T _) (inner_nonneg hu hinc T _)
    rintro a ⟨S, hS, hST, hθS, rfl⟩
    have hTS : MeasurableSet (T ∪ S) := hT.1.union hS.1
    have hTSΩ : T ∪ S ⊆ Ω := Set.union_subset hT.2 hS.2
    have hrest : (θ (Ω \ (T ∪ S))).toReal = 1 - t₂ := by
      rw [meas_rest hΩ hθ1 hTS hTSΩ, Set.union_comm, meas_union_real hST hT.1, hθS, hθT]
      ring
    obtain ⟨R, hRsub, hR, hθR⟩ := atomless_ivt hd hΩ hθc hθac (hΩ.1.diff hTS)
      (show 0 ≤ t₂' - t₂ by linarith) (by rw [hrest]; linarith)
    have hRS : Disjoint S R := Set.disjoint_left.2 fun x hx hxR =>
      (hRsub hxR).2 (Or.inr hx)
    refine ⟨u (S ∪ R), ⟨S ∪ R, ⟨hS.1.union hR, Set.union_subset hS.2
      (hRsub.trans Set.sdiff_subset)⟩, ?_, ?_, rfl⟩, ?_⟩
    · refine Disjoint.union_left hST (Set.disjoint_left.2 fun x hxR hxT => ?_)
      exact (hRsub hxR).2 (Or.inl hxT)
    · rw [meas_union_real hRS hR, hθS, hθR]
      ring
    · exact hinc S (S ∪ R) hS ⟨hS.1.union hR, Set.union_subset hS.2
        (hRsub.trans Set.sdiff_subset)⟩ Set.subset_union_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t₁ t₁' t₂ h0 h11 h12 h2
    have ht₁ : t₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨h0, by linarith⟩
    have ht₁' : t₁' ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have ht₂ : t₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    exact hinc _ _ (piece_share hK ht₁' ht₂) (piece_share hK ht₁ ht₂)
      (Set.diff_subset_diff_right (knife_mono hK h0 h11 ht₁'.2))
  · intro t₁ t₂ t₂' h0 h12 h22 h2
    have ht₁ : t₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨h0, by linarith⟩
    have ht₂ : t₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have ht₂' : t₂' ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    exact hinc _ _ (piece_share hK ht₁ ht₂) (piece_share hK ht₁ ht₂')
      (Set.diff_subset_diff_left (knife_mono hK ht₂.1 h22 h2))
  · intro t₁ t₁' t₂ h0 h11 h12 h2
    unfold uBid
    obtain ⟨T0, hT0, hθT0⟩ := hexT t₁ h0 (by linarith)
    refine le_csInf ⟨_, T0, hT0, hθT0, rfl⟩ ?_
    rintro b ⟨T, hT, hθT, rfl⟩
    have hrest : (θ (Ω \ T)).toReal = 1 - t₁ := by rw [meas_rest hΩ hθ1 hT.1 hT.2, hθT]
    obtain ⟨R, hRsub, hR, hθR⟩ := atomless_ivt hd hΩ hθc hθac (hΩ.1.diff hT.1)
      (show 0 ≤ t₁' - t₁ by linarith) (by rw [hrest]; linarith)
    have hRT : Disjoint R T := Set.disjoint_left.2 fun x hxR hxT => (hRsub hxR).2 hxT
    have hT' : IsShare Ω (T ∪ R) := ⟨hT.1.union hR, Set.union_subset hT.2
      (hRsub.trans Set.sdiff_subset)⟩
    have hθT' : (θ (T ∪ R)).toReal = t₁' := by
      rw [meas_union_real hRT.symm hR, hθT, hθR]
      ring
    refine (csInf_le (outer_bdd hu hinc _ _) ⟨T ∪ R, hT', hθT', rfl⟩).trans ?_
    apply sSup_le_of_dom (inner_bdd hu T _) (inner_nonneg hu hinc T _)
    rintro a ⟨S, hS, hST', hθS, rfl⟩
    have hSR : Disjoint S R := hST'.mono_right Set.subset_union_right
    have hSRs : IsShare Ω (S ∪ R) := ⟨hS.1.union hR, Set.union_subset hS.2
      (hRsub.trans Set.sdiff_subset)⟩
    refine ⟨u (S ∪ R), ⟨S ∪ R, hSRs, ?_, ?_, rfl⟩, ?_⟩
    · exact Disjoint.union_left (hST'.mono_right Set.subset_union_left) hRT
    · rw [meas_union_real hSR hR, hθS, hθR]
      ring
    · exact hinc S (S ∪ R) hS hSRs Set.subset_union_left
  · intro t₁ t₂ t₂' h0 h12 h22 h2
    unfold uBid
    obtain ⟨T0, hT0, hθT0⟩ := hexT t₁ h0 (by linarith)
    refine le_csInf ⟨_, T0, hT0, hθT0, rfl⟩ ?_
    rintro b ⟨T, hT, hθT, rfl⟩
    exact (csInf_le (outer_bdd hu hinc _ _) ⟨T, hT, hθT, rfl⟩).trans
      (hF T hT t₁ t₂ t₂' hθT h12 h22 h2)
