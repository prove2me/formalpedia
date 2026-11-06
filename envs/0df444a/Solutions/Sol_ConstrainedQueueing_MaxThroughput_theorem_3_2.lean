-- Prove2me | solution 1 for ConstrainedQueueing.MaxThroughput.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:58:17.824199+00:00
-- url     : https://prove2.me/submissions/324f9557-ad65-4c9a-813d-feb9497a748e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model
import Theorems.Thm_ConstrainedQueueing_MaxThroughput_lemma_3_2
import Theorems.Thm_ConstrainedQueueing_MaxThroughput_lemma_3_3

open scoped ENNReal

namespace CQThm32Aux
open ConstrainedQueueing.MaxThroughput

/-- A chain on a one-point state space with all transition probabilities equal to `1` is stable. -/
theorem stable_of_unique {σ : Type*} [Unique σ] (P : σ → σ → ℝ≥0∞) (hP : ∀ x y, P x y = 1) :
    IsStable P := by
  have hreach : ∀ x y : σ, Reaches P x y := by
    intro x y
    refine ⟨1, le_rfl, ?_⟩
    simp [stepProb, hP]
    simp [Subsingleton.elim y default]
  have hess : ∀ x : σ, IsEssential P x := fun x y _ => hreach y x
  refine ⟨?_, ?_⟩
  · intro y hy
    exact absurd (hess y) hy
  · intro x _
    have hfp : ∀ n, firstPassage P n x x = if n = 1 then 1 else 0 := by
      intro n
      match n with
      | 0 => simp [firstPassage, firstEntry]
      | 1 => simp [firstPassage, firstEntry, hP] <;> exact Subsingleton.elim _ _
      | n + 2 =>
        simp only [firstPassage, firstEntry]
        have : ∀ y : σ, ({x} : Set σ)ᶜ.indicator
            (fun y => P x y * firstEntry P {x} (n + 1) y) y = 0 := by
          intro y
          rw [Set.indicator_of_notMem]
          simp [Subsingleton.elim y x]
        simp [this]
    refine ⟨?_, ?_⟩
    · unfold returnProb
      rw [tsum_eq_single 1]
      · simp [hfp]
      · intro n hn; simp [hfp, hn]
    · unfold meanRecurrenceTime
      rw [tsum_eq_single 1]
      · simp [hfp]
      · intro n hn; simp [hfp, hn]

end CQThm32Aux

open ConstrainedQueueing.MaxThroughput in
theorem solution {L N J : ℕ} (net : ConstrainedQueueing.MaxThroughput.Network L N J)
    (hC1 : ConstrainedQueueing.MaxThroughput.C1 net)
    (hempty : (∅ : Finset (Fin N)) ∈ net.S) (hsingle : ∀ i : Fin N, ({i} : Finset (Fin N)) ∈ net.S)
    (hm : ∀ i, 0 < net.m i ∧ net.m i ≤ 1) (hC2 : ConstrainedQueueing.MaxThroughput.C2 net) :
    Cprime net ⊆ sysStabRegion net ∧ sysStabRegion net ⊆ closure (Cprime net) ∧
      ∀ g, IsPi0Rule net g →
        Cprime net ⊆ stabRegion net g ∧ stabRegion net g ⊆ sysStabRegion net ∧
          sysStabRegion net ⊆ closure (stabRegion net g) := by
  classical
  -- every π₀ rule is an activation rule
  have hact : ∀ g, IsPi0Rule net g → IsActivationRule net g := by
    intro g hg x
    obtain ⟨jhat, _, chat, hchatS, _, hgx⟩ := hg x
    refine ⟨?_, ?_⟩
    · apply hC1 chat hchatS
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hgx i] at hi
      by_contra hc
      rw [if_neg (fun h => hc h.1)] at hi
      simp at hi
    · intro l j
      by_cases hne : (Finset.univ.filter fun i => net.q i = l ∧ g x i = some j).Nonempty
      · obtain ⟨i0, hi0⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0
        obtain ⟨hq0, hg0⟩ := hi0
        have hg0' := hg0
        rw [hgx i0] at hg0'
        by_cases hcond : i0 ∈ chat ∧
            (Finset.univ.filter fun i' => net.q i' = net.q i0).card <
              xval net x (net.q i0) (jhat i0)
        · rw [if_pos hcond] at hg0'
          have hj : jhat i0 = j := Option.some.inj hg0'
          have hlt := hcond.2
          rw [hj, hq0] at hlt
          have hsub : (Finset.univ.filter fun i => net.q i = l ∧ g x i = some j) ⊆
              Finset.univ.filter fun i' => net.q i' = l := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi.1
          have := Finset.card_le_card hsub
          omega
        · rw [if_neg hcond] at hg0'
          simp at hg0'
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
  have hstab : ∀ g, IsPi0Rule net g → stabRegion net g ⊆ sysStabRegion net := by
    intro g hg
    intro a ha
    unfold sysStabRegion
    exact Set.mem_biUnion (x := g) (hact g hg) ha
  -- sysStabRegion ⊆ closure C′, via Lemma 3.3 and a two-point arrival law with mean `a`
  have h33 : sysStabRegion net ⊆ closure (Cprime net) := by
    intro a ha
    unfold sysStabRegion at ha
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at ha
    obtain ⟨g, hg, ha⟩ := ha
    obtain ⟨hnn, hst⟩ := ha
    by_contra hna
    -- construct the arrival law
    have hlaw : ∀ r : ℝ, 0 ≤ r → ∃ μ : PMF ℕ, Summable (fun k : ℕ => (k : ℝ) ^ 2 * (μ k).toReal)
        ∧ ∑' k : ℕ, (k : ℝ) * (μ k).toReal = r := by
      intro r hr
      set n : ℕ := ⌊r⌋₊ + 1 with hn
      have hnpos : (0 : ℝ) < n := by positivity
      have hrn : r < n := by
        rw [hn]; push_cast; exact Nat.lt_floor_add_one r
      have hn0 : n ≠ 0 := by omega
      set t : ℝ := r / n with ht
      have ht0 : 0 ≤ t := div_nonneg hr hnpos.le
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hnpos]; exact hrn.le
      let f : ℕ → ℝ≥0∞ := fun k =>
        if k = n then ENNReal.ofReal t else if k = 0 then ENNReal.ofReal (1 - t) else 0
      have hsum : ∑ k ∈ ({0, n} : Finset ℕ), f k = 1 := by
        rw [Finset.sum_pair (Ne.symm hn0)]
        simp only [f, if_neg (Ne.symm hn0), if_neg hn0, eq_self_iff_true, if_true]
        rw [← ENNReal.ofReal_add (by linarith) ht0]
        simp
      have hzero : ∀ k ∉ ({0, n} : Finset ℕ), f k = 0 := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp [f, hk.1, hk.2]
      refine ⟨PMF.ofFinset f {0, n} hsum hzero, ?_, ?_⟩
      · apply summable_of_ne_finset_zero (s := ({0, n} : Finset ℕ))
        intro k hk
        simp [PMF.ofFinset_apply, hzero k hk]
      · rw [tsum_eq_sum (s := ({0, n} : Finset ℕ))]
        · rw [Finset.sum_pair (Ne.symm hn0)]
          simp only [PMF.ofFinset_apply, f, if_neg (Ne.symm hn0), if_neg hn0, eq_self_iff_true,
            if_true]
          rw [ENNReal.toReal_ofReal ht0, ht]
          field_simp
          simp
        · intro k hk
          simp [PMF.ofFinset_apply, hzero k hk]
    choose μ hμ1 hμ2 using hlaw
    let α : ArrivalLaw net := fun p => μ (a p) (hnn p)
    have hadm : Admissible α := fun p => hμ1 (a p) (hnn p)
    have hmean : meanRate α = a := by
      funext p
      exact hμ2 (a p) (hnn p)
    have := lemma_3_3 net hm g hg α hadm (by rw [hmean]; exact hna)
    exact this (hst α hadm hmean)
  -- C′ ⊆ sysStabRegion
  have hCsys : Cprime net ⊆ sysStabRegion net := by
    by_cases hJ : J = 0
    · subst hJ
      -- the state space is a single point
      let g0 : (QIdx net → ℕ) → MultiAct N 0 := fun _ _ => none
      have hg0 : IsActivationRule net g0 := by
        intro x
        refine ⟨?_, ?_⟩
        · unfold IsMultiAct
          simpa [g0] using hempty
        · intro l j; exact j.elim0
      intro a ha
      unfold sysStabRegion
      refine Set.mem_biUnion (x := g0) hg0 ?_
      refine ⟨fun p => p.1.2.elim0, ?_⟩
      intro α _ _
      have : IsEmpty (QIdx net) := ⟨fun p => p.1.2.elim0⟩
      letI : Unique (QIdx net → ℕ) := Pi.uniqueOfIsEmpty _
      apply CQThm32Aux.stable_of_unique
      intro x y
      unfold transProb
      have hA : ∀ A : QIdx net → ℕ, arrivalProb α A = 1 := by
        intro A; unfold arrivalProb; simp
      have hS : ∑ M : Fin N → Bool, serviceProb net M = 1 := by
        unfold serviceProb
        have := (Finset.prod_univ_sum (fun _ : Fin N => (Finset.univ : Finset Bool))
          (fun i (b : Bool) => if b then ENNReal.ofReal (net.m i)
            else ENNReal.ofReal (1 - net.m i))).symm
        rw [Fintype.piFinset_univ] at this
        rw [this]
        apply Finset.prod_eq_one
        intro i _
        rw [Fintype.sum_bool]
        simp only [if_true, Bool.false_eq_true, if_false]
        rw [← ENNReal.ofReal_add (hm i).1.le (by linarith [(hm i).2])]
        simp
      rw [tsum_eq_single (default : QIdx net → ℕ)]
      · simp only [hA, one_mul, Subsingleton.elim (nextState net g0 x default _) y, if_true,
          mul_one]
        exact hS
      · intro b hb; exact absurd (Subsingleton.elim b default) hb
    · -- a π₀ rule exists
      have : NeZero J := ⟨hJ⟩
      have key : ∀ x : QIdx net → ℕ, ∃ jhat : Fin N → Fin J,
          (∀ i j, D net x i j ≤ D net x i (jhat i)) ∧
          ∃ chat ∈ net.S,
            ∀ c ∈ net.S, ∑ i ∈ c, D net x i (jhat i) ≤ ∑ i ∈ chat, D net x i (jhat i) := by
        intro x
        have hj : ∀ i, ∃ j0 : Fin J, ∀ j, D net x i j ≤ D net x i j0 := by
          intro i
          obtain ⟨j0, _, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => D net x i j)
            Finset.univ_nonempty
          exact ⟨j0, fun j => hj0 j (Finset.mem_univ j)⟩
        choose jhat hjhat using hj
        refine ⟨jhat, hjhat, ?_⟩
        obtain ⟨chat, hchat, hmax⟩ := Set.exists_max_image net.S
          (fun c => ∑ i ∈ c, D net x i (jhat i)) (Set.toFinite _) ⟨∅, hempty⟩
        exact ⟨chat, hchat, hmax⟩
      choose jhat hjhat chat hchatS hchat using key
      let g : (QIdx net → ℕ) → MultiAct N J := fun x i =>
        if i ∈ chat x ∧
            (Finset.univ.filter fun i' => net.q i' = net.q i).card < xval net x (net.q i) (jhat x i)
        then some (jhat x i) else none
      have hg : IsPi0Rule net g := fun x =>
        ⟨jhat x, hjhat x, chat x, hchatS x, hchat x, fun i => rfl⟩
      exact (lemma_3_2 net hC1 hempty hsingle hm hC2 g hg).trans (hstab g hg)
  refine ⟨hCsys, h33, ?_⟩
  intro g hg
  have h1 := lemma_3_2 net hC1 hempty hsingle hm hC2 g hg
  exact ⟨h1, hstab g hg, h33.trans (closure_mono h1)⟩
