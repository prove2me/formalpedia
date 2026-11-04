-- Prove2me | solution 1 for CasinoCPT.Embedding.rootTime_continue_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:26:34.872351+00:00
-- url     : https://prove2.me/submissions/52d94f12-add9-47bf-84ae-1eb60ba22f69

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding

namespace Casino31Factor

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- the increment σ-algebras -/
abbrev mD (S : ℕ → Ω → ℤ) (i : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => S (i + 1) ω - S i ω) inferInstance

lemma mD_le_F {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (i : ℕ) : mD S i ≤ F (i + 1) :=
  ((hS.adapted (i + 1)).sub ((hS.adapted i).mono (F.mono (Nat.le_succ i)) le_rfl)).comap_le

lemma walk_indep {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : Finset ℕ) :
    ∀ (d : ℕ → Set Ω), (∀ i ∈ s, MeasurableSet[mD S i] (d i)) →
      ∀ g : Set Ω, MeasurableSet[F 0] g →
        P (g ∩ ⋂ i ∈ s, d i) = P g * ∏ i ∈ s, P (d i) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => intro d _ g _; simp
  | insert a s hlt ih =>
    intro d hd g hg
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.prod_insert ha, Finset.set_biInter_insert]
    have hR : MeasurableSet[F a] (g ∩ ⋂ i ∈ s, d i) := by
      refine MeasurableSet.inter (F.mono (Nat.zero_le a) _ hg) ?_
      refine Finset.measurableSet_biInter _ fun i hi => ?_
      exact F.mono (hlt i hi) _ (mD_le_F hS i _ (hd i (Finset.mem_insert_of_mem hi)))
    have hind := (Indep_iff _ _ P).mp (hS.indep a) (d a) (g ∩ ⋂ i ∈ s, d i)
      (hd a (Finset.mem_insert_self a s)) hR
    have e : g ∩ (d a ∩ ⋂ i ∈ s, d i) = d a ∩ (g ∩ ⋂ i ∈ s, d i) := by
      ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [e, hind, ih d (fun i hi => hd i (Finset.mem_insert_of_mem hi)) g hg]
    ring

/-- the joint family of increment σ-algebras and coin σ-algebras -/
def M (S : ℕ → Ω → ℤ) (coin : ℕ → ℤ → Ω → Bool) : ℕ ⊕ (ℕ × ℤ) → MeasurableSpace Ω :=
  Sum.elim (fun i => mD S i) (fun p => MeasurableSpace.comap (coin p.1 p.2) inferInstance)

lemma M_iIndep {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool)
    (hc : IsRootCoins P F b r coin) : iIndep (M S coin) P := by
  classical
  have hP := hS.isProb
  rw [iIndep_iff]
  intro s f hf
  have hL : ∀ i ∈ s.toLeft, MeasurableSet[mD S i] (f (Sum.inl i)) := by
    intro i hi; exact hf (Sum.inl i) (Finset.mem_toLeft.mp hi)
  have hR : ∀ p ∈ s.toRight, MeasurableSet[MeasurableSpace.comap (coin p.1 p.2) inferInstance]
      (f (Sum.inr p)) := by
    intro p hp; exact hf (Sum.inr p) (Finset.mem_toRight.mp hp)
  have hg : MeasurableSet[F 0] (⋂ p ∈ s.toRight, f (Sum.inr p)) :=
    Finset.measurableSet_biInter _ fun p hp => (hc.meas p.1 p.2).comap_le _ (hR p hp)
  have e : (⋂ i ∈ s, f i) = (⋂ p ∈ s.toRight, f (Sum.inr p)) ∩ ⋂ i ∈ s.toLeft, f (Sum.inl i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h; exact ⟨fun p hp => h _ hp, fun i hi => h _ hi⟩
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | inl i => exact h2 i hi
      | inr p => exact h1 p hi
  rw [e, walk_indep hS s.toLeft (fun i => f (Sum.inl i)) hL _ hg,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight, mul_comm]
  congr 1
  exact hc.indep.meas_biInter hR

end Casino31Factor

namespace Casino31Factor

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma le_rootTime_iff (S : ℕ → Ω → ℤ) (b : ℤ → ℕ) (coin : ℕ → ℤ → Ω → Bool) (ω : Ω) (n : ℕ) :
    (n : ℕ∞) ≤ rootTime S b coin ω ↔
      ∀ t, (b (S t ω) ≤ t ∧ coin t (S t ω) ω = false) → n ≤ t := by
  unfold rootTime
  rw [le_iInf₂_iff]
  simp only [Nat.cast_le]

end Casino31Factor

open Casino31Factor

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool) (hc : IsRootCoins P F b r coin)
    (n : ℕ) (x : ℤ) :
    P {ω | S n ω = x ∧ ((n + 1 : ℕ) : ℕ∞) ≤ rootTime S b coin ω} =
      P {ω | S n ω = x ∧ (n : ℕ∞) ≤ rootTime S b coin ω} * P {ω | coin n x ω = true} := by
  classical
  have hP := hS.isProb
  let Sset : Set (ℕ ⊕ (ℕ × ℤ)) := {i | Sum.elim (fun k => k < n) (fun p => p.1 < n) i}
  let Tset : Set (ℕ ⊕ (ℕ × ℤ)) := {Sum.inr (n, x)}
  have hdisj : Disjoint Sset Tset := by
    rw [Set.disjoint_singleton_right]
    simp [Sset]
  have hMle : ∀ i, M S coin i ≤ mΩ := by
    intro i
    cases i with
    | inl k => exact (mD_le_F hS k).trans (F.le _)
    | inr p => exact ((hc.meas p.1 p.2).comap_le).trans (F.le 0)
  have hind := indep_iSup_of_disjoint hMle (M_iIndep hS b r coin hc) hdisj
  have hDm : ∀ k < n, Measurable[⨆ i ∈ Sset, M S coin i] (fun ω => S (k + 1) ω - S k ω) := by
    intro k hk
    have : M S coin (Sum.inl k) ≤ (⨆ i ∈ Sset, M S coin i) := 
      le_iSup₂ (f := fun i (_ : i ∈ Sset) => M S coin i) (Sum.inl k) (by simpa [Sset] using hk)
    exact (comap_measurable _).mono this le_rfl
  have hSm : ∀ t ≤ n, Measurable[⨆ i ∈ Sset, M S coin i] (S t) := by
    intro t ht
    have e : S t = fun ω => ∑ k ∈ Finset.range t, (S (k + 1) ω - S k ω) := by
      funext ω
      rw [Finset.sum_range_sub (fun k => S k ω), hS.zero ω, sub_zero]
    rw [e]
    exact Finset.measurable_sum _ fun k hk => hDm k (by simp at hk; omega)
  have hCm : ∀ t < n, ∀ y, Measurable[⨆ i ∈ Sset, M S coin i] (coin t y) := by
    intro t ht y
    have : M S coin (Sum.inr (t, y)) ≤ (⨆ i ∈ Sset, M S coin i) := 
      le_iSup₂ (f := fun i (_ : i ∈ Sset) => M S coin i) (Sum.inr (t, y)) (by simpa [Sset] using ht)
    exact (comap_measurable _).mono this le_rfl
  -- the event E
  have hEeq : {ω | S n ω = x ∧ (n : ℕ∞) ≤ rootTime S b coin ω} =
      {ω | S n ω = x} ∩ ⋂ t ∈ Finset.range n, (⋃ y : ℤ,
        ({ω | S t ω = y} ∩ {_ω | b y ≤ t} ∩ {ω | coin t y ω = false}))ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      Set.mem_iUnion, Finset.mem_range, le_rootTime_iff, not_exists, not_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun t ht y hy hcf => ?_⟩
      obtain ⟨hy, hb⟩ := hy
      subst hy
      have := h2 t ⟨hb, hcf⟩; omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun t ⟨hb, hcf⟩ => ?_⟩
      by_contra hlt
      exact h2 t (by omega) (S t ω) ⟨rfl, hb⟩ hcf
  have hEm : MeasurableSet[⨆ i ∈ Sset, M S coin i] {ω | S n ω = x ∧ (n : ℕ∞) ≤ rootTime S b coin ω} := by
    rw [hEeq]
    refine MeasurableSet.inter ((hSm n le_rfl) (measurableSet_singleton x)) ?_
    refine Finset.measurableSet_biInter _ fun t ht => MeasurableSet.compl ?_
    have ht' : t < n := by simpa using ht
    refine MeasurableSet.iUnion fun y => MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
    · exact (hSm t ht'.le) (measurableSet_singleton y)
    · exact MeasurableSet.const _
    · exact (hCm t ht' y) (measurableSet_singleton false)
  have hCtm : MeasurableSet[⨆ i ∈ Tset, M S coin i] {ω | coin n x ω = true} := by
    have : M S coin (Sum.inr (n, x)) ≤ (⨆ i ∈ Tset, M S coin i) := 
      le_iSup₂ (f := fun i (_ : i ∈ Tset) => M S coin i) (Sum.inr (n, x)) rfl
    exact this _ ((comap_measurable (coin n x)) (measurableSet_singleton true))
  by_cases hbx : b x ≤ n
  · have hset : {ω | S n ω = x ∧ ((n + 1 : ℕ) : ℕ∞) ≤ rootTime S b coin ω} =
        {ω | S n ω = x ∧ (n : ℕ∞) ≤ rootTime S b coin ω} ∩ {ω | coin n x ω = true} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, le_rootTime_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, fun t ht => by have := h2 t ht; omega⟩, ?_⟩
        by_contra hf
        have := h2 n ⟨by rw [h1]; exact hbx, by rw [h1]; simpa using hf⟩
        omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun t ht => ?_⟩
        have := h2 t ht
        rcases lt_or_eq_of_le this with h | h
        · omega
        · subst h; rw [h1] at ht; rw [ht.2] at h3; exact absurd h3 (by decide)
    rw [hset]
    exact (Indep_iff _ _ P).mp hind _ _ hEm hCtm
  · push_neg at hbx
    have hset : {ω | S n ω = x ∧ ((n + 1 : ℕ) : ℕ∞) ≤ rootTime S b coin ω} =
        {ω | S n ω = x ∧ (n : ℕ∞) ≤ rootTime S b coin ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, le_rootTime_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun t ht => by have := h2 t ht; omega⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun t ht => ?_⟩
        have := h2 t ht
        rcases lt_or_eq_of_le this with h | h
        · omega
        · subst h; rw [h1] at ht; omega
    have hlaw := hc.law n x
    rw [if_pos hbx] at hlaw
    have hm : MeasurableSet {ω | coin n x ω = false} :=
      F.le 0 _ ((hc.meas n x) (measurableSet_singleton false))
    have h0 : P {ω | coin n x ω = false} = 0 := by
      rw [ENNReal.toReal_eq_zero_iff] at hlaw
      exact hlaw.resolve_right (measure_ne_top P _)
    have h1 : P {ω | coin n x ω = true} = 1 := by
      have : {ω | coin n x ω = true} = {ω | coin n x ω = false}ᶜ := by ext ω; simp
      rw [this, prob_compl_eq_one_sub hm, h0, tsub_zero]
    rw [hset, h1, mul_one]
