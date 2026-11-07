-- Prove2me | solution 1 for ConstrainedQueueing.MaxThroughput.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:01:00.745119+00:00
-- url     : https://prove2.me/submissions/040d6c03-1b89-4a1b-b15a-4ccc992fadaa

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

open scoped ENNReal

open ConstrainedQueueing.MaxThroughput in
theorem solution {L N J : ℕ} (net : ConstrainedQueueing.MaxThroughput.Network L N J)
    (hm : ∀ i, 0 < net.m i) :
    closure (Cprime net) =
      {a | (∀ p, 0 ≤ a p) ∧ ∃ f, IsAdmissibleFlow net a f ∧
        ∃ c ∈ coS net, ∀ i, fhat f i / net.m i ≤ c i} := by
  classical
  set R := {a : QIdx net → ℝ | (∀ p, 0 ≤ a p) ∧ ∃ f, IsAdmissibleFlow net a f ∧
        ∃ c ∈ coS net, ∀ i, fhat f i / net.m i ≤ c i} with hR
  -- `co(S)` lies in the unit cube
  have hcube : coS net ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    unfold coS
    apply convexHull_min
    · rintro _ ⟨c, _, rfl⟩
      intro i _
      unfold actVec
      split_ifs <;> simp
    · exact convex_pi (𝕜 := ℝ) (fun _ _ => convex_Icc 0 1)
  have hcoS_closed : IsClosed (coS net) := by
    unfold coS
    exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ) ((Set.toFinite net.S).image actVec)).isClosed
  -- the flow-to-rate map
  let Φ : (Fin N → Fin J → ℝ) → (QIdx net → ℝ) := fun f p =>
    (∑ i ∈ Finset.univ.filter (fun i => net.q i = p.1.1), f i p.1.2)
      - ∑ i ∈ Finset.univ.filter (fun i => net.h i = p.1.1), f i p.1.2
  have hΦc : Continuous Φ := by
    apply continuous_pi; intro p
    apply Continuous.sub
    · exact continuous_finsetSum _ (fun i _ =>
        (continuous_apply p.1.2).comp (continuous_apply i))
    · exact continuous_finsetSum _ (fun i _ =>
        (continuous_apply p.1.2).comp (continuous_apply i))
  have hfhatc : ∀ i, Continuous (fun f : Fin N → Fin J → ℝ => fhat f i) := by
    intro i
    unfold fhat
    exact continuous_finsetSum _ (fun j _ => (continuous_apply j).comp (continuous_apply i))
  -- the compact set of (flow, c) pairs
  let K : Set ((Fin N → Fin J → ℝ) × (Fin N → ℝ)) :=
    {x | x.2 ∈ coS net ∧ (∀ i j, 0 ≤ x.1 i j) ∧ (∀ i j, net.q i ∈ net.V j → x.1 i j = 0) ∧
      (∀ i, fhat x.1 i / net.m i ≤ x.2 i) ∧ ∀ p, 0 ≤ Φ x.1 p}
  have hKclosed : IsClosed K := by
    have hK : K = {x | x.2 ∈ coS net} ∩
        ((⋂ i, ⋂ j, {x : (Fin N → Fin J → ℝ) × (Fin N → ℝ) | 0 ≤ x.1 i j}) ∩
        ((⋂ i, ⋂ j, {x : (Fin N → Fin J → ℝ) × (Fin N → ℝ) | net.q i ∈ net.V j → x.1 i j = 0}) ∩
        ((⋂ i, {x : (Fin N → Fin J → ℝ) × (Fin N → ℝ) | fhat x.1 i / net.m i ≤ x.2 i}) ∩
        (⋂ p, {x : (Fin N → Fin J → ℝ) × (Fin N → ℝ) | 0 ≤ Φ x.1 p})))) := by
      ext x
      simp only [K, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hK]
    refine IsClosed.inter (hcoS_closed.preimage continuous_snd) ?_
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_le continuous_const (by fun_prop)
    · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      by_cases hq : net.q i ∈ net.V j
      · simp only [hq, forall_const]
        exact isClosed_eq (by fun_prop) continuous_const
      · simp [hq]
    · refine isClosed_iInter fun i => ?_
      exact isClosed_le (((hfhatc i).comp continuous_fst).div_const _)
        ((continuous_apply i).comp continuous_snd)
    · refine isClosed_iInter fun p => ?_
      exact isClosed_le continuous_const (((continuous_apply p).comp hΦc).comp continuous_fst)
  have hKsub : K ⊆ (Set.pi Set.univ (fun i => Set.pi Set.univ (fun _ => Set.Icc 0 (net.m i))))
      ×ˢ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    rintro ⟨f, c⟩ ⟨hc, hf0, _, hfc, _⟩
    have hc1 := hcube hc
    refine ⟨?_, hc1⟩
    intro i _ j _
    refine ⟨hf0 i j, ?_⟩
    have h1 : f i j ≤ fhat f i := by
      unfold fhat
      exact Finset.single_le_sum (fun j _ => hf0 i j) (Finset.mem_univ j)
    have h2 : fhat f i ≤ net.m i * c i := by
      have := hfc i
      rw [div_le_iff₀ (hm i)] at this
      linarith
    have h3 : c i ≤ 1 := (hc1 i (Set.mem_univ i)).2
    have h4 : net.m i * c i ≤ net.m i := by
      have := (hm i).le
      nlinarith
    linarith
  have hKcompact : IsCompact K := by
    refine IsCompact.of_isClosed_subset ?_ hKclosed hKsub
    exact (isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hRimage : R = (fun x => Φ x.1) '' K := by
    ext a
    constructor
    · rintro ⟨ha0, f, ⟨hf0, hfa, hfV⟩, c, hc, hfc⟩
      refine ⟨(f, c), ⟨hc, hf0, hfV, hfc, ?_⟩, ?_⟩
      · intro p
        have := hfa p
        simp only [Φ]
        linarith [ha0 p]
      · funext p
        simp only [Φ]
        exact (hfa p).symm
    · rintro ⟨⟨f, c⟩, ⟨hc, hf0, hfV, hfc, hΦ⟩, rfl⟩
      exact ⟨hΦ, f, ⟨hf0, fun p => rfl, hfV⟩, c, hc, hfc⟩
  have hRclosed : IsClosed R := by
    rw [hRimage]
    exact (hKcompact.image (hΦc.comp continuous_fst)).isClosed
  apply Set.Subset.antisymm
  · apply closure_minimal _ hRclosed
    rintro a ⟨ha0, f, hf, c, hc, hfc⟩
    refine ⟨ha0, f, hf, c, hc, fun i => ?_⟩
    by_cases hpos : 0 < fhat f i
    · exact ((hfc i).1 hpos).le
    · have hf0 : fhat f i = 0 := by
        have : 0 ≤ fhat f i := Finset.sum_nonneg (fun j _ => hf.1 i j)
        linarith
      rw [hf0, zero_div]
      exact (hcube hc i (Set.mem_univ i)).1
  · rintro a ⟨ha0, f, ⟨hf0, hfa, hfV⟩, c, hc, hfc⟩
    let s : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
    have hs0 : ∀ n, 0 ≤ s n := by
      intro n
      simp only [s]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hs1 : ∀ n, s n < 1 := by
      intro n; simp only [s]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hmem : ∀ n, s n • a ∈ Cprime net := by
      intro n
      refine ⟨fun p => ?_, fun i j => s n * f i j, ⟨?_, ?_, ?_⟩, c, hc, fun i => ⟨?_, ?_⟩⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (hs0 n) (ha0 p)
      · intro i j; exact mul_nonneg (hs0 n) (hf0 i j)
      · intro p
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hfa p, mul_sub, Finset.mul_sum, Finset.mul_sum]
      · intro i j hq; simp [hfV i j hq]
      · intro hpos
        have hfh : fhat (fun i j => s n * f i j) i = s n * fhat f i := by
          unfold fhat; rw [Finset.mul_sum]
        rw [hfh] at hpos ⊢
        have hfpos : 0 < fhat f i := by
          by_contra hneg
          push Not at hneg
          have : s n * fhat f i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hs0 n) hneg
          linarith
        have hdiv : 0 < fhat f i / net.m i := div_pos hfpos (hm i)
        have := hfc i
        rw [mul_div_assoc]
        have : s n * (fhat f i / net.m i) < fhat f i / net.m i := by
          have := hs1 n
          nlinarith
        linarith
      · intro hc0
        have hfh : fhat (fun i j => s n * f i j) i = s n * fhat f i := by
          unfold fhat; rw [Finset.mul_sum]
        rw [hfh]
        have h1 := hfc i
        rw [hc0, div_le_iff₀ (hm i), zero_mul] at h1
        have h2 : 0 ≤ fhat f i := Finset.sum_nonneg (fun j _ => hf0 i j)
        have : fhat f i = 0 := le_antisymm h1 h2
        rw [this, mul_zero]
    have hlim : Filter.Tendsto (fun n => s n • a) Filter.atTop (nhds a) := by
      have hs : Filter.Tendsto s Filter.atTop (nhds 1) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
        simpa [s] using this
      simpa using hs.smul_const a
    exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hmem)
