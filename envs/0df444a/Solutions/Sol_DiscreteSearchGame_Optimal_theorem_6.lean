-- Prove2me | solution 1 for DiscreteSearchGame.Optimal.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T11:18:05.250836+00:00
-- url     : https://prove2.me/submissions/52fab522-68bf-4789-8687-d4be378fd051

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

set_option autoImplicit false

open AllocationIndices Filter Topology

open AllocationIndices in
lemma p2m66_sc_eq {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ k i = ∑ t ∈ Finset.range k, if σ t = i then 1 else 0 := by
  unfold searchCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if σ t = i then 1 else 0) k

open AllocationIndices in
lemma p2m66_sc_succ {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ (k + 1) i = searchCount σ k i + if σ k = i then 1 else 0 := by
  rw [p2m66_sc_eq, p2m66_sc_eq, Finset.sum_range_succ]

open AllocationIndices in
lemma p2m66_sc_congr {n : ℕ} {σ σ' : ℕ → Fin n} {k : ℕ} (h : ∀ j < k, σ j = σ' j)
    (i : Fin n) : searchCount σ k i = searchCount σ' k i := by
  rw [p2m66_sc_eq, p2m66_sc_eq]
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

/-- A function of a search sequence that depends only on its first `k + 1` entries is
continuous (product topology). -/
lemma p2m66_cont_of_local {n : ℕ} {X : Type*} [TopologicalSpace X] (k : ℕ)
    (G : (ℕ → Fin n) → X) (hG : ∀ ξ ξ' : ℕ → Fin n, (∀ j ≤ k, ξ j = ξ' j) → G ξ = G ξ') :
    Continuous G := by
  let r : (ℕ → Fin n) → (Fin (k + 1) → Fin n) := fun ξ j => ξ j
  let ext : (Fin (k + 1) → Fin n) → (ℕ → Fin n) := fun a j =>
    if h : j < k + 1 then a ⟨j, h⟩ else a 0
  have hr : Continuous r := continuous_pi fun j => continuous_apply _
  have hGeq : G = (G ∘ ext) ∘ r := by
    funext ξ
    simp only [Function.comp]
    apply hG
    intro j hj
    simp [ext, r]
    intro h; omega
  rw [hGeq]
  exact continuous_of_discreteTopology.comp hr

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m66_V_lsc {n : ℕ} (t q : Fin n → ℝ) (i : Fin n) :
    LowerSemicontinuous (fun ξ : ℕ → Fin n => V t q i ξ) := by
  unfold V
  refine lowerSemicontinuous_tsum fun m => (p2m66_cont_of_local m _ ?_).lowerSemicontinuous
  intro ξ ξ' h
  rw [h m le_rfl, p2m66_sc_congr (fun j hj => h j hj.le) i]

open AllocationIndices in
lemma p2m66_cost_lsc {n : ℕ} (p q t : Fin n → ℝ) :
    LowerSemicontinuous (fun ξ : ℕ → Fin n => searchCost p q t ξ) := by
  unfold searchCost notFoundProb
  refine lowerSemicontinuous_tsum fun m => (p2m66_cont_of_local m _ ?_).lowerSemicontinuous
  intro ξ ξ' h
  simp only [h m le_rfl, p2m66_sc_congr (fun j hj => h j hj.le)]

open AllocationIndices in
lemma p2m66_conf_closed {n : ℕ} (p q t : Fin n → ℝ) :
    IsClosed {ξ : ℕ → Fin n | ConformsToSearchIndex p q t ξ} := by
  classical
  have : {ξ : ℕ → Fin n | ConformsToSearchIndex p q t ξ} =
      ⋂ k, (fun ξ : ℕ → Fin n =>
        decide (∀ i, searchIndex p q t ξ k i ≤ searchIndex p q t ξ k (ξ k))) ⁻¹' {true} := by
    ext ξ; simp [ConformsToSearchIndex]
  rw [this]
  refine isClosed_iInter fun k =>
    IsClosed.preimage (p2m66_cont_of_local k _ ?_) (isClosed_discrete _)
  intro ξ ξ' h
  have hiff : (∀ i, searchIndex p q t ξ k i ≤ searchIndex p q t ξ k (ξ k)) ↔
      (∀ i, searchIndex p q t ξ' k i ≤ searchIndex p q t ξ' k (ξ' k)) := by
    simp only [searchIndex, h k le_rfl, p2m66_sc_congr (fun j hj => h j hj.le)]
  exact decide_eq_decide.2 hiff

lemma p2m66_nested {n : ℕ} (S : ℕ → Set (ℕ → Fin n)) (hcl : ∀ k, IsClosed (S k))
    (hmono : ∀ k, S (k + 1) ⊆ S k) (hne : ∀ k, (S k).Nonempty) : ∃ ξ, ∀ k, ξ ∈ S k := by
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono
    hne (hcl 0).isCompact hcl
  exact ⟨ξ, Set.mem_iInter.1 hξ⟩

lemma p2m66_tsum_top (f : ℕ → ENNReal) (c : ENNReal) (hc : c ≠ 0) (k : ℕ)
    (h : ∀ m, k ≤ m → c ≤ f m) : ∑' m, f m = ⊤ := by
  have h1 : ∑' m, f (m + k) ≤ ∑' m, f m :=
    ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective k) f
  have h2 : ∑' _ : ℕ, c ≤ ∑' m, f (m + k) :=
    ENNReal.tsum_le_tsum fun m => h _ (Nat.le_add_left k m)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hc] at h2
  exact top_le_iff.1 (h2.trans h1)

open AllocationIndices in
lemma p2m66_nf_succ {n : ℕ} (p q : Fin n → ℝ) (ξ : ℕ → Fin n) (a : ℕ) :
    notFoundProb p q ξ (a + 1) = notFoundProb p q ξ a -
      p (ξ a) * (1 - q (ξ a)) ^ searchCount ξ a (ξ a) * q (ξ a) := by
  unfold notFoundProb
  have : ∀ i, p i * (1 - q i) ^ searchCount ξ (a + 1) i =
      p i * (1 - q i) ^ searchCount ξ a i -
        (if ξ a = i then p i * (1 - q i) ^ searchCount ξ a i * q i else 0) := by
    intro i
    rw [p2m66_sc_succ]
    split_ifs with h
    · ring
    · simp
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

open AllocationIndices in
lemma p2m66_nf_nonneg {n : ℕ} (p q : Fin n → ℝ) (hq1 : ∀ i, q i < 1) (hp0 : ∀ i, 0 ≤ p i)
    (ξ : ℕ → Fin n) (m : ℕ) : 0 ≤ notFoundProb p q ξ m := by
  unfold notFoundProb
  refine Finset.sum_nonneg fun i _ => ?_
  have := hp0 i; have : 0 ≤ 1 - q i := by linarith [hq1 i]
  positivity

open AllocationIndices in
/-- Exchanging two adjacent searches of different boxes that are in the wrong index order
strictly lowers a finite search cost. -/
lemma p2m66_swap {n : ℕ} (p q t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq1 : ∀ i, q i < 1)
    (hp0 : ∀ i, 0 ≤ p i) (ξ : ℕ → Fin n) (a : ℕ) (hne : ξ a ≠ ξ (a + 1))
    (hlt : searchIndex p q t ξ a (ξ a) < searchIndex p q t ξ (a + 1) (ξ (a + 1)))
    (hfin : searchCost p q t ξ ≠ ⊤) :
    searchCost p q t (fun m => ξ (Equiv.swap a (a + 1) m)) < searchCost p q t ξ := by
  set ξ' : ℕ → Fin n := fun m => ξ (Equiv.swap a (a + 1) m) with hξ'
  have hτa : ξ' a = ξ (a + 1) := by simp [ξ']
  have hτb : ξ' (a + 1) = ξ a := by simp [ξ']
  have hτo : ∀ m, m ≠ a → m ≠ a + 1 → ξ' m = ξ m := by
    intro m h1 h2; simp [ξ', Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hlow : ∀ m ≤ a, ∀ i, searchCount ξ' m i = searchCount ξ m i := by
    intro m hm i
    exact p2m66_sc_congr (fun j hj => hτo j (by omega) (by omega)) i
  have hhigh : ∀ d i, searchCount ξ' (d + (a + 1 + 1)) i = searchCount ξ (d + (a + 1 + 1)) i := by
    intro d i
    induction d with
    | zero =>
      rw [zero_add, p2m66_sc_succ ξ' (a + 1) i, p2m66_sc_succ ξ' a i, p2m66_sc_succ ξ (a + 1) i,
        p2m66_sc_succ ξ a i, hlow a le_rfl, hτa, hτb]
      ring
    | succ d ih =>
      rw [show d + 1 + (a + 1 + 1) = d + (a + 1 + 1) + 1 by ring, p2m66_sc_succ ξ',
        p2m66_sc_succ ξ, ih, hτo _ (by omega) (by omega)]
  have hnf : ∀ m, (∀ i, searchCount ξ' m i = searchCount ξ m i) →
      notFoundProb p q ξ' m = notFoundProb p q ξ m := by
    intro m h; unfold notFoundProb; simp_rw [h]
  let F : (ℕ → Fin n) → ℕ → ENNReal := fun ζ m =>
    ENNReal.ofReal (t (ζ m) * notFoundProb p q ζ m)
  have hsplit : ∀ ζ, searchCost p q t ζ = (∑ m ∈ Finset.range a, F ζ m) +
      (F ζ a + F ζ (a + 1)) + ∑' m, F ζ (m + (a + 1 + 1)) := by
    intro ζ
    rw [← add_assoc, ← Finset.sum_range_succ, ← Finset.sum_range_succ]
    exact (ENNReal.summable.sum_add_tsum_nat_add').symm
  have hA : ∑ m ∈ Finset.range a, F ξ' m = ∑ m ∈ Finset.range a, F ξ m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    simp only [F, hτo m (by omega) (by omega), hnf m (hlow m hm'.le)]
  have hR : ∑' m, F ξ' (m + (a + 1 + 1)) = ∑' m, F ξ (m + (a + 1 + 1)) := by
    congr 1; funext m
    simp only [F, hτo (m + (a + 1 + 1)) (by omega) (by omega), hnf _ (hhigh m)]
  have hcv : searchCount ξ (a + 1) (ξ (a + 1)) = searchCount ξ a (ξ (a + 1)) := by
    rw [p2m66_sc_succ, if_neg hne, add_zero]
  set N := notFoundProb p q ξ a with hN
  set Pu := p (ξ a) * (1 - q (ξ a)) ^ searchCount ξ a (ξ a) * q (ξ a) with hPu
  set Pv := p (ξ (a + 1)) * (1 - q (ξ (a + 1))) ^ searchCount ξ a (ξ (a + 1)) * q (ξ (a + 1))
    with hPv
  have e1 : F ξ a = ENNReal.ofReal (t (ξ a) * N) := rfl
  have e2 : F ξ (a + 1) = ENNReal.ofReal (t (ξ (a + 1)) * (N - Pu)) := by
    simp only [F]; rw [p2m66_nf_succ]
  have e3 : F ξ' a = ENNReal.ofReal (t (ξ (a + 1)) * N) := by
    simp only [F]; rw [hτa, hnf a (hlow a le_rfl)]
  have e4 : F ξ' (a + 1) = ENNReal.ofReal (t (ξ a) * (N - Pv)) := by
    simp only [F]; rw [hτb, p2m66_nf_succ, hnf a (hlow a le_rfl), hτa, hlow a le_rfl]
  have hN0 : 0 ≤ N := p2m66_nf_nonneg p q hq1 hp0 ξ a
  have hNu : 0 ≤ N - Pu := by
    rw [hN, hPu, ← p2m66_nf_succ]; exact p2m66_nf_nonneg p q hq1 hp0 ξ (a + 1)
  have hNv : 0 ≤ N - Pv := by
    have := p2m66_nf_nonneg p q hq1 hp0 ξ' (a + 1)
    rw [p2m66_nf_succ, hnf a (hlow a le_rfl), hτa, hlow a le_rfl] at this
    exact this
  have hlt' : Pu * t (ξ (a + 1)) < Pv * t (ξ a) := by
    have h := hlt
    simp only [searchIndex] at h
    rw [hcv, div_lt_div_iff₀ (ht _) (ht _)] at h
    exact h
  have htu := ht (ξ a); have htv := ht (ξ (a + 1))
  have hX : F ξ' a + F ξ' (a + 1) < F ξ a + F ξ (a + 1) := by
    rw [e1, e2, e3, e4, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith)]
    nlinarith
  have hfinξ := hfin
  rw [hsplit ξ] at hfinξ
  have hAfin : ∑ m ∈ Finset.range a, F ξ m ≠ ⊤ := fun h => hfinξ (by rw [h]; simp)
  have hRfin : ∑' m, F ξ (m + (a + 1 + 1)) ≠ ⊤ := fun h => hfinξ (by rw [h]; simp)
  rw [hsplit ξ', hsplit ξ, hA, hR]
  exact ENNReal.add_lt_add_right hRfin (ENNReal.add_lt_add_left hAfin hX)

open AllocationIndices in
/-- An optimal search sequence with finite cost conforms to the search index. -/
lemma p2m66_opt_conforms {n : ℕ} (p q t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hp0 : ∀ i, 0 ≤ p i) (ξ : ℕ → Fin n)
    (hfin : searchCost p q t ξ ≠ ⊤) (hopt : ∀ ξ', searchCost p q t ξ ≤ searchCost p q t ξ') :
    ConformsToSearchIndex p q t ξ := by
  have hidx0 : ∀ k i, 0 ≤ searchIndex p q t ξ k i := fun k i => by
    unfold searchIndex
    have := hp0 i; have := ht i; have := hq0 i; have : 0 ≤ 1 - q i := by linarith [hq1 i]
    positivity
  have hdec : ∀ a, searchIndex p q t ξ (a + 1) (ξ (a + 1)) ≤ searchIndex p q t ξ a (ξ a) := by
    intro a
    by_cases he : ξ a = ξ (a + 1)
    · rw [← he]
      unfold searchIndex
      rw [p2m66_sc_succ, if_pos rfl, pow_succ]
      have := hp0 (ξ a); have := hq0 (ξ a)
      have h1 : 0 ≤ 1 - q (ξ a) := by linarith [hq1 (ξ a)]
      have h2 : 1 - q (ξ a) ≤ 1 := by linarith
      have key : p (ξ a) * ((1 - q (ξ a)) ^ searchCount ξ a (ξ a) * (1 - q (ξ a))) * q (ξ a) =
          (p (ξ a) * (1 - q (ξ a)) ^ searchCount ξ a (ξ a) * q (ξ a)) * (1 - q (ξ a)) := by ring
      rw [key]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) h2) (ht _).le
    · by_contra hlt
      push Not at hlt
      exact absurd (hopt _) (not_le.2 (p2m66_swap p q t ht hq1 hp0 ξ a he hlt hfin))
  have hanti : Antitone (fun a => searchIndex p q t ξ a (ξ a)) := antitone_nat_of_succ_le hdec
  intro k i
  by_contra hlt
  push Not at hlt
  have hidx : ∀ m, searchCount ξ m i = searchCount ξ k i →
      searchIndex p q t ξ m i = searchIndex p q t ξ k i := by
    intro m hm; simp only [searchIndex, hm]
  have hstay : ∀ d, searchCount ξ (k + d) i = searchCount ξ k i := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have hne : ξ (k + d) ≠ i := by
        intro he
        have h1 := hanti (Nat.le_add_right k d)
        simp only at h1
        rw [he, hidx _ ih] at h1
        linarith
      rw [← add_assoc, p2m66_sc_succ, if_neg hne, add_zero, ih]
  have hpi : 0 < p i := by
    rcases (hp0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : searchIndex p q t ξ k i = 0 := by simp [searchIndex, ← h]
      linarith [hidx0 k (ξ k)]
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ t ⟨i, Finset.mem_univ _⟩
  have hqi : 0 < 1 - q i := by linarith [hq1 i]
  apply hfin
  refine p2m66_tsum_top _ (ENNReal.ofReal (t j0 * (p i * (1 - q i) ^ searchCount ξ k i)))
    (by have := ht j0; exact (ENNReal.ofReal_pos.2 (by positivity)).ne') k ?_
  intro m hm
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hsl : p i * (1 - q i) ^ searchCount ξ k i ≤ notFoundProb p q ξ (k + d) := by
    unfold notFoundProb
    rw [← hstay d]
    exact Finset.single_le_sum (f := fun j => p j * (1 - q j) ^ searchCount ξ (k + d) j)
      (fun j _ => by have := hp0 j; have : 0 ≤ 1 - q j := (by linarith [hq1 j]); positivity)
      (Finset.mem_univ i)
  have := ht j0
  exact mul_le_mul (hj0 _ (Finset.mem_univ _)) hsl (by positivity) (ht _).le

open AllocationIndices in
lemma p2m66_sc_mono {n : ℕ} (σ : ℕ → Fin n) (i : Fin n) {k k' : ℕ} (h : k ≤ k') :
    searchCount σ k i ≤ searchCount σ k' i := by
  rw [p2m66_sc_eq, p2m66_sc_eq]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m66_ruleCounts {n : ℕ} [NeZero n] (t q p : Fin n → ℝ) (r : Rule n) (k : ℕ)
    (i : Fin n) : ruleCounts t q p r k i = searchCount (ruleSeq t q r p) k i := by
  induction k generalizing i with
  | zero => simp [ruleCounts, searchCount]
  | succ k ih =>
    have h1 : ruleCounts t q p r (k + 1) i =
        ruleCounts t q p r k i + (Pi.single (ruleSeq t q r p k) 1 : Fin n → ℕ) i := rfl
    rw [h1, ih, p2m66_sc_succ, Pi.single_apply]
    by_cases h : ruleSeq t q r p k = i
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

open DiscreteSearchGame.Optimal in
lemma p2m66_tieBreak_max {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (f : Fin n → ℝ)
    (i : Fin n) : f i ≤ f (tieBreak σ f) := by
  unfold tieBreak
  set S := Finset.univ.filter fun j : Fin n => ∀ i, f i ≤ f (σ j) with hS
  have hm : ∀ H, S.min' H ∈ S := fun H => Finset.min'_mem S H
  exact (Finset.mem_filter.1 (hm _)).2 i

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m66_simple_conforms {n : ℕ} [NeZero n] (t q p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ConformsToSearchIndex p q t (simpleSeq t q σ p) := by
  intro k i
  have hc : ∀ j, searchIndex p q t (simpleSeq t q σ p) k j =
      gittinsIndex t q p (ruleCounts t q p (fun _ => σ) k) j := by
    intro j
    simp only [searchIndex, gittinsIndex, p2m66_ruleCounts]
    rfl
  rw [hc, hc]
  exact p2m66_tieBreak_max σ _ i

open AllocationIndices DiscreteSearchGame.Optimal in
/-- Every box is cheap to find under a Gittins sequence against `p` with `p i > 0`. -/
lemma p2m66_V_lt_top {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hp0 : ∀ i, 0 ≤ p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (i : Fin n) (hpi : 0 < p i) :
    V t q i ξ < ⊤ := by
  set c : ℝ := t i / (p i * q i) with hc
  have hc0 : 0 ≤ c := by have := ht i; have := hq0 i; positivity
  let h : Fin n × ℕ → ℝ := fun x => p x.1 * q x.1 * (1 - q x.1) ^ x.2
  have h0 : ∀ x, 0 ≤ h x := by
    intro x; have := hp0 x.1; have := hq0 x.1; have : 0 ≤ 1 - q x.1 := by linarith [hq1 x.1]
    positivity
  let φ : ℕ → Fin n × ℕ := fun k => (ξ k, searchCount ξ k (ξ k))
  have hpt : ∀ k, ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) ≤
      ENNReal.ofReal c * ENNReal.ofReal (h (φ k)) := by
    intro k
    rw [← ENNReal.ofReal_mul hc0]
    apply ENNReal.ofReal_le_ofReal
    have hk := hξ k i
    simp only [searchIndex] at hk
    rw [div_le_div_iff₀ (ht i) (ht (ξ k))] at hk
    simp only [h, φ, hc]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by have := hpi; have := hq0 i; positivity)]
    nlinarith [hk]
  have hinj : Function.Injective φ := by
    intro k k' hkk
    simp only [φ, Prod.mk.injEq] at hkk
    obtain ⟨h1, h2⟩ := hkk
    by_contra hne
    have key : ∀ a b, a < b → ξ a = ξ b →
        searchCount ξ a (ξ a) < searchCount ξ b (ξ b) := by
      intro a b hab he
      have hm := p2m66_sc_mono ξ (ξ a) (Nat.succ_le_of_lt hab)
      rw [p2m66_sc_succ, if_pos rfl] at hm
      rw [← he]; omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := key k k' hl h1; omega
    · have := key k' k hl h1.symm; omega
  have hsum : Summable h := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun j => ?_, Summable.of_finite⟩
    show Summable fun m : ℕ => p j * q j * (1 - q j) ^ m
    exact (summable_geometric_of_lt_one (by linarith [hq1 j]) (by linarith [hq0 j])).mul_left _
  calc V t q i ξ = ∑' k, ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) := rfl
    _ ≤ ∑' k, ENNReal.ofReal c * ENNReal.ofReal (h (φ k)) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal c * ∑' k, ENNReal.ofReal (h (φ k)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal c * ∑' x, ENNReal.ofReal (h x) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj _
    _ = ENNReal.ofReal c * ENNReal.ofReal (∑' x, h x) := by
        rw [ENNReal.ofReal_tsum_of_nonneg h0 hsum]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

open AllocationIndices DiscreteSearchGame.Optimal in
/-- A uniform bound on `V_i` over Gittins sequences against `p` with `p i > 0`. -/
lemma p2m66_V_le {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (hp0 : ∀ i, 0 ≤ p i) (ξ : ℕ → Fin n)
    (hξ : ConformsToSearchIndex p q t ξ) (i : Fin n) (hpi : 0 < p i) :
    V t q i ξ ≤ ENNReal.ofReal (t i / (p i * q i) *
      ∑' x : Fin n × ℕ, p x.1 * q x.1 * (1 - q x.1) ^ x.2) := by
  set c : ℝ := t i / (p i * q i) with hc
  have hc0 : 0 ≤ c := by have := ht i; have := hq0 i; positivity
  let h : Fin n × ℕ → ℝ := fun x => p x.1 * q x.1 * (1 - q x.1) ^ x.2
  have h0 : ∀ x, 0 ≤ h x := by
    intro x; have := hp0 x.1; have := hq0 x.1; have : 0 ≤ 1 - q x.1 := by linarith [hq1 x.1]
    positivity
  let φ : ℕ → Fin n × ℕ := fun k => (ξ k, searchCount ξ k (ξ k))
  have hpt : ∀ k, ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) ≤
      ENNReal.ofReal c * ENNReal.ofReal (h (φ k)) := by
    intro k
    rw [← ENNReal.ofReal_mul hc0]
    apply ENNReal.ofReal_le_ofReal
    have hk := hξ k i
    simp only [searchIndex] at hk
    rw [div_le_div_iff₀ (ht i) (ht (ξ k))] at hk
    simp only [h, φ, hc]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by have := hpi; have := hq0 i; positivity)]
    nlinarith [hk]
  have hinj : Function.Injective φ := by
    intro k k' hkk
    simp only [φ, Prod.mk.injEq] at hkk
    obtain ⟨h1, h2⟩ := hkk
    by_contra hne
    have key : ∀ a b, a < b → ξ a = ξ b →
        searchCount ξ a (ξ a) < searchCount ξ b (ξ b) := by
      intro a b hab he
      have hm := p2m66_sc_mono ξ (ξ a) (Nat.succ_le_of_lt hab)
      rw [p2m66_sc_succ, if_pos rfl] at hm
      rw [← he]; omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := key k k' hl h1; omega
    · have := key k' k hl h1.symm; omega
  have hsum : Summable h := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun j => ?_, Summable.of_finite⟩
    show Summable fun m : ℕ => p j * q j * (1 - q j) ^ m
    exact (summable_geometric_of_lt_one (by linarith [hq1 j]) (by linarith [hq0 j])).mul_left _
  calc V t q i ξ = ∑' k, ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) := rfl
    _ ≤ ∑' k, ENNReal.ofReal c * ENNReal.ofReal (h (φ k)) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal c * ∑' k, ENNReal.ofReal (h (φ k)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal c * ∑' x, ENNReal.ofReal (h x) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj _
    _ = ENNReal.ofReal c * ENNReal.ofReal (∑' x, h x) := by
        rw [ENNReal.ofReal_tsum_of_nonneg h0 hsum]
    _ = ENNReal.ofReal (c * ∑' x, h x) := (ENNReal.ofReal_mul hc0).symm

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m66_searchCost {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq1 : ∀ i, q i < 1) (hp0 : ∀ i, 0 ≤ p i) (ξ : ℕ → Fin n) :
    searchCost p q t ξ = ∑ i, ENNReal.ofReal (p i) * V t q i ξ := by
  unfold searchCost notFoundProb V
  have hk : ∀ k, ENNReal.ofReal (t (ξ k) * ∑ i, p i * (1 - q i) ^ searchCount ξ k i) =
      ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (t (ξ k) * (1 - q i) ^ searchCount ξ k i) := by
    intro k
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ENNReal.ofReal_mul (hp0 i)]
      congr 1
      ring
    · intro i _
      have := ht (ξ k); have := hp0 i; have : 0 ≤ 1 - q i := by linarith [hq1 i]
      positivity
  simp_rw [hk]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_congr rfl fun i _ => ENNReal.tsum_mul_left


lemma p2m66_lim {r : ℝ} (hr : 0 ≤ r) (x : ENNReal)
    (h : ∀ k : ℕ, x ≤ ENNReal.ofReal (r + 1 / ((k : ℝ) + 1))) : x ≤ ENNReal.ofReal r := by
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h 0)
  rw [← ENNReal.ofReal_toReal hx]
  apply ENNReal.ofReal_le_ofReal
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) (h k)
  linarith

lemma p2m66_inv_mono (k : ℕ) : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
  one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2m66_value_ne_top {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) : gameValue t q ≠ ⊤ := by
  set u : Fin n → ℝ := fun _ => 1 / (n : ℝ) with hu
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hu0 : ∀ i, 0 < u i := fun i => by simp only [u]; positivity
  set ξ := simpleSeq t q 1 u
  have hc := p2m66_simple_conforms t q u 1
  have hV : ∀ i, V t q i ξ ≠ ⊤ := fun i =>
    (p2m66_V_lt_top t q u ht hq0 hq1 (fun i => (hu0 i).le) ξ hc i (hu0 i)).ne
  refine ne_top_of_le_ne_top (b := ∑ i, V t q i ξ) (ENNReal.sum_ne_top.2 fun i _ => hV i) ?_
  refine iSup₂_le fun p hp => ?_
  show (⨅ ξ', searchCost p q t ξ') ≤ _
  refine (iInf_le _ ξ).trans ?_
  rw [p2m66_searchCost t q p ht hq1 (fun i => hp.1 i) ξ]
  refine Finset.sum_le_sum fun i _ => ?_
  have hp1 : p i ≤ 1 := hp.2 ▸ Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
  calc ENNReal.ofReal (p i) * V t q i ξ ≤ 1 * V t q i ξ := by
        gcongr; exact ENNReal.ofReal_le_one.2 hp1
    _ = V t q i ξ := one_mul _

set_option maxHeartbeats 1000000 in
open AllocationIndices DiscreteSearchGame.Optimal in
/-- Against an optimal hider `p`, every hiding strategy `l` is answered by a Gittins search
sequence against `p` whose cost under `l` is at most the value. -/
lemma p2m66_stepA {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (p : Fin n → ℝ) (hp : IsOptimalHider t q p)
    (hfin : gameValue t q ≠ ⊤) (l : Fin n → ℝ) (hl : l ∈ stdSimplex ℝ (Fin n)) :
    ∃ ξ, ConformsToSearchIndex p q t ξ ∧ searchCost l q t ξ ≤ gameValue t q := by
  set W := (gameValue t q).toReal with hW
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hWeq : gameValue t q = ENNReal.ofReal W := (ENNReal.ofReal_toReal hfin).symm
  have hp0 : ∀ i, 0 ≤ p i := hp.1.1
  have hl0 : ∀ i, 0 ≤ l i := hl.1
  have hG : ∀ ξ, ENNReal.ofReal W ≤ searchCost p q t ξ := fun ξ => by
    rw [← hWeq, ← hp.2]; exact iInf_le _ ξ
  let S : ℕ → Set (ℕ → Fin n) := fun k =>
    {ξ | searchCost p q t ξ ≤ ENNReal.ofReal (W + 1 / ((k : ℝ) + 1))} ∩
      {ξ | searchCost l q t ξ ≤ ENNReal.ofReal (W + 1 / ((k : ℝ) + 1))}
  have hcl : ∀ k, IsClosed (S k) := fun k =>
    ((p2m66_cost_lsc p q t).isClosed_preimage _).inter ((p2m66_cost_lsc l q t).isClosed_preimage _)
  have hmono : ∀ k, S (k + 1) ⊆ S k := by
    intro k ξ hξ
    have hle : ENNReal.ofReal (W + 1 / (((k + 1 : ℕ) : ℝ) + 1)) ≤
        ENNReal.ofReal (W + 1 / ((k : ℝ) + 1)) := by
      apply ENNReal.ofReal_le_ofReal
      linarith [p2m66_inv_mono k]
    exact ⟨le_trans hξ.1 hle, le_trans hξ.2 hle⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    set θ : ℝ := ε / (ε + W + 1) with hθ
    have hθ0 : 0 < θ := by positivity
    have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; linarith
    have hθe : θ * (ε + W + 1) = ε := by rw [hθ]; field_simp
    set pθ : Fin n → ℝ := fun i => (1 - θ) * p i + θ * l i with hpθ
    have hpθ0 : ∀ i, 0 ≤ pθ i := fun i =>
      add_nonneg (mul_nonneg (by linarith) (hp0 i)) (mul_nonneg hθ0.le (hl0 i))
    have hpθs : pθ ∈ stdSimplex ℝ (Fin n) := by
      refine ⟨hpθ0, ?_⟩
      simp only [pθ, Finset.sum_add_distrib, ← Finset.mul_sum, hp.1.2, hl.2]
      ring
    have hgle : hiderGuarantee t q pθ < ENNReal.ofReal (W + θ * ε) := by
      calc hiderGuarantee t q pθ ≤ gameValue t q :=
            le_iSup₂ (f := fun p (_ : p ∈ stdSimplex ℝ (Fin n)) => hiderGuarantee t q p) pθ hpθs
        _ = ENNReal.ofReal W := hWeq
        _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
            (by have := mul_pos hθ0 hε0; linarith)
    obtain ⟨ξ, hξ⟩ := iInf_lt_iff.1 hgle
    have hlin : searchCost pθ q t ξ = ENNReal.ofReal (1 - θ) * searchCost p q t ξ +
        ENNReal.ofReal θ * searchCost l q t ξ := by
      rw [p2m66_searchCost t q pθ ht hq1 hpθ0, p2m66_searchCost t q p ht hq1 hp0,
        p2m66_searchCost t q l ht hq1 hl0, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← mul_assoc, ← add_mul, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_mul hθ0.le,
        ← ENNReal.ofReal_add (mul_nonneg (by linarith) (hp0 i)) (mul_nonneg hθ0.le (hl0 i))]
    rw [hlin] at hξ
    set A := searchCost p q t ξ with hA
    set B := searchCost l q t ξ with hB
    have hA1 : ENNReal.ofReal W ≤ A := hG ξ
    have h1θ : ENNReal.ofReal (1 - θ) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
    have hθ' : ENNReal.ofReal θ ≠ 0 := (ENNReal.ofReal_pos.2 hθ0).ne'
    have hAt : A ≠ ⊤ := by
      intro h; rw [h, ENNReal.mul_top h1θ] at hξ; simp at hξ
    have hBt : B ≠ ⊤ := by
      intro h; rw [h, ENNReal.mul_top hθ'] at hξ; simp at hξ
    have hA0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
    have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal hAt, ← ENNReal.ofReal_toReal hBt,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hθ0.le,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) hA0) (mul_nonneg hθ0.le hB0),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hξ
    have hA1' : W ≤ A.toReal := by
      rw [← ENNReal.ofReal_le_ofReal_iff hA0, ENNReal.ofReal_toReal hAt]; exact hA1
    refine ⟨ξ, ?_, ?_⟩
    · show A ≤ _
      rw [← ENNReal.ofReal_toReal hAt]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1 - θ) * A.toReal < (1 - θ) * (W + ε) := by
        nlinarith [mul_le_mul_of_nonneg_left hε1 hθ0.le, mul_nonneg hθ0.le hB0]
      exact (lt_of_mul_lt_mul_left h1 (by linarith)).le
    · show B ≤ _
      rw [← ENNReal.ofReal_toReal hBt]
      apply ENNReal.ofReal_le_ofReal
      have h2 : θ * B.toReal < θ * (W + ε) := by
        nlinarith [mul_le_mul_of_nonneg_left hA1' (sub_nonneg.2 hθ1.le)]
      exact (lt_of_mul_lt_mul_left h2 hθ0.le).le
  obtain ⟨ξ, hξ⟩ := p2m66_nested S hcl hmono hne
  have h1 := p2m66_lim hW0 _ fun k => (hξ k).1
  have h2 := p2m66_lim hW0 _ fun k => (hξ k).2
  refine ⟨ξ, p2m66_opt_conforms p q t ht hq0 hq1 hp0 ξ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) fun ξ' => h1.trans (hG ξ'), ?_⟩
  rw [hWeq]; exact h2

open AllocationIndices DiscreteSearchGame.Optimal in
/-- Proposition 3 [1.]: an optimal hiding strategy is interior. -/
lemma p2m66_pos {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (p : Fin n → ℝ) (hp : IsOptimalHider t q p)
    (hfin : gameValue t q ≠ ⊤) : ∀ i, 0 < p i := by
  classical
  intro i
  by_contra hpi
  have hpi0 : p i = 0 := le_antisymm (not_lt.1 hpi) (hp.1.1 i)
  have hl : (Pi.single i 1 : Fin n → ℝ) ∈ stdSimplex ℝ (Fin n) :=
    ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩
  obtain ⟨ξ, hξc, hξ⟩ := p2m66_stepA t q ht hq0 hq1 p hp hfin _ hl
  rw [p2m66_searchCost t q _ ht hq1 hl.1,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ i) h)] at hξ
  simp only [Pi.single_eq_same, ENNReal.ofReal_one, one_mul] at hξ
  obtain ⟨j, hj⟩ : ∃ j, 0 < p j := by
    by_contra h
    push Not at h
    have h1 := hp.1.2
    have : ∑ j, p j ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith
  have hnot : ∀ m, ξ m ≠ i := by
    intro m he
    have h1 := hξc m j
    rw [he] at h1
    simp only [searchIndex, hpi0, zero_mul, zero_div] at h1
    have hqj : 0 < 1 - q j := by linarith [hq1 j]
    have := ht j; have := hq0 j
    have : 0 < p j * (1 - q j) ^ searchCount ξ m j * q j / t j := by positivity
    linarith
  have hc0 : ∀ m, searchCount ξ m i = 0 := by
    intro m; rw [p2m66_sc_eq]; exact Finset.sum_eq_zero fun k _ => if_neg (hnot k)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ t ⟨i, Finset.mem_univ _⟩
  have htop : V t q i ξ = ⊤ := by
    unfold V
    refine p2m66_tsum_top _ (ENNReal.ofReal (t j0)) (ENNReal.ofReal_pos.2 (ht j0)).ne' 0
      fun m _ => ?_
    rw [hc0 m, pow_zero, mul_one]
    exact ENNReal.ofReal_le_ofReal (hj0 _ (Finset.mem_univ _))
  rw [htop] at hξ
  exact hfin (top_le_iff.1 hξ)

lemma p2m66_sum_emb {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M] (e : ι ↪ κ)
    (G : κ → M) (hG : ∀ j, (¬ ∃ a, e a = j) → G j = 0) : ∑ j, G j = ∑ a, G (e a) := by
  classical
  rw [← Finset.sum_map Finset.univ e G]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hG
  rintro ⟨a, rfl⟩
  exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ a))

/-- The convex hull of a compact set in `ℝⁿ` is compact (Carathéodory). -/
lemma p2m66_isCompact_convexHull {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | ⟨z0, hz0⟩
  · simp
  let Φ : (Fin (n + 1) → (Fin n → ℝ)) × (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
    fun x => ∑ j, x.2 j • x.1 j
  have hΦ : Continuous Φ := continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp continuous_snd).smul ((continuous_apply j).comp continuous_fst)
  have hdom : IsCompact ((Set.univ.pi fun _ : Fin (n + 1) => K) ×ˢ stdSimplex ℝ (Fin (n + 1))) :=
    (isCompact_univ_pi fun _ => hK).prod (isCompact_stdSimplex ℝ (Fin (n + 1)))
  convert hdom.image hΦ using 1
  ext x
  constructor
  · intro hx
    obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ n + 1 := by
      have h1 := hai.card_le_finrank_succ
      have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      rw [Module.finrank_fin_fun] at h2
      omega
    obtain ⟨e⟩ : Nonempty (ι ↪ Fin (n + 1)) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    refine ⟨(Function.extend e z (fun _ => z0), Function.extend e w 0), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j _
      by_cases h : ∃ a, e a = j
      · obtain ⟨a, rfl⟩ := h
        simp only
        rw [e.injective.extend_apply]
        exact hzK ⟨a, rfl⟩
      · simp only
        rw [Function.extend_apply' _ _ _ h]
        exact hz0
    · intro j
      dsimp only
      by_cases h : ∃ a, e a = j
      · obtain ⟨a, rfl⟩ := h
        rw [e.injective.extend_apply]
        exact (hw0 a).le
      · rw [Function.extend_apply' _ _ _ h]
        simp
    · show ∑ j, Function.extend e w 0 j = 1
      rw [p2m66_sum_emb e _ (fun j h => by rw [Function.extend_apply' _ _ _ h]; simp)]
      simp only [e.injective.extend_apply]
      exact hw1
    · show ∑ j, Function.extend e w 0 j • Function.extend e z (fun _ => z0) j = x
      rw [p2m66_sum_emb e _ (fun j h => by rw [Function.extend_apply' _ _ _ h]; simp)]
      simp only [e.injective.extend_apply]
      exact hwx
  · rintro ⟨⟨zz, ww⟩, ⟨hz, hw⟩, rfl⟩
    exact (convex_convexHull ℝ K).sum_mem (fun j _ => hw.1 j) hw.2
      (fun j _ => subset_convexHull ℝ K (hz j (Set.mem_univ j)))

set_option maxHeartbeats 1000000 in
open AllocationIndices DiscreteSearchGame.Optimal in
/-- The minimax step: some mixture of Gittins payoff vectors against `p` is at most `v*` in every
coordinate. -/
lemma p2m66_minimax {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (p : Fin n → ℝ) (hp : IsOptimalHider t q p)
    (hpos : ∀ i, 0 < p i) (hfinv : gameValue t q ≠ ⊤) :
    ∃ w ∈ convexHull ℝ (payoffSet t q p), ∀ i, w i ≤ (gameValue t q).toReal := by
  classical
  set v := (gameValue t q).toReal with hv
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hpos i).le
  have hfin : ∀ ξ, ConformsToSearchIndex p q t ξ → ∀ i, V t q i ξ ≠ ⊤ := fun ξ hξ i =>
    (p2m66_V_lt_top t q p ht hq0 hq1 hp0 ξ hξ i (hpos i)).ne
  set Y := payoffSet t q p with hY
  set B : Fin n → ℝ := fun i =>
    t i / (p i * q i) * ∑' x : Fin n × ℕ, p x.1 * q x.1 * (1 - q x.1) ^ x.2 with hB
  have hB0 : ∀ i, 0 ≤ B i := fun i => by
    refine mul_nonneg (by have := ht i; have := hpos i; have := hq0 i; positivity)
      (tsum_nonneg fun x => ?_)
    have := hp0 x.1; have := hq0 x.1; have : 0 ≤ 1 - q x.1 := (by linarith [hq1 x.1])
    positivity
  have hYB : Y ⊆ Set.Icc 0 B := by
    rintro y ⟨ξ, hξ, rfl⟩
    exact ⟨fun i => ENNReal.toReal_nonneg, fun i =>
      ENNReal.toReal_le_of_le_ofReal (hB0 i) (p2m66_V_le t q p ht hq0 hq1 hp0 ξ hξ i (hpos i))⟩
  set K := closure Y with hK
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      ((Metric.isBounded_Icc 0 B).subset hYB).closure
  have hK0 : K ⊆ Set.Icc 0 B := closure_minimal hYB isClosed_Icc
  -- points of the closure dominate actual payoff vectors
  have hKY : ∀ z ∈ K, ∃ ξ, ConformsToSearchIndex p q t ξ ∧ ∀ i, vecReal t q ξ i ≤ z i := by
    intro z hz
    have hz0 : ∀ i, 0 ≤ z i := fun i => (hK0 hz).1 i
    let S : ℕ → Set (ℕ → Fin n) := fun k => {ξ | ConformsToSearchIndex p q t ξ} ∩
      ⋂ i, (fun ξ => V t q i ξ) ⁻¹' Set.Iic (ENNReal.ofReal (z i + 1 / ((k : ℝ) + 1)))
    have hcl : ∀ k, IsClosed (S k) := fun k =>
      (p2m66_conf_closed p q t).inter
        (isClosed_iInter fun i => (p2m66_V_lsc t q i).isClosed_preimage _)
    have hmono : ∀ k, S (k + 1) ⊆ S k := by
      intro k ξ hξ
      refine ⟨hξ.1, Set.mem_iInter.2 fun i => ?_⟩
      have h3 := Set.mem_iInter.1 hξ.2 i
      simp only [Set.mem_preimage, Set.mem_Iic] at h3 ⊢
      refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [p2m66_inv_mono k]
    have hne : ∀ k, (S k).Nonempty := by
      intro k
      obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.1 hz (1 / ((k : ℝ) + 1)) (by positivity)
      obtain ⟨ξ, hξ, rfl⟩ := hb
      refine ⟨ξ, hξ, Set.mem_iInter.2 fun i => ?_⟩
      simp only [Set.mem_preimage, Set.mem_Iic]
      rw [← ENNReal.ofReal_toReal (hfin ξ hξ i)]
      apply ENNReal.ofReal_le_ofReal
      have h4 := (dist_le_pi_dist z (vecReal t q ξ) i).trans_lt hd
      rw [Real.dist_eq] at h4
      have h5 := (abs_lt.1 h4).1
      show vecReal t q ξ i ≤ _
      linarith
    obtain ⟨ξ, hξ⟩ := p2m66_nested S hcl hmono hne
    refine ⟨ξ, (hξ 0).1, fun i => ?_⟩
    have h6 := p2m66_lim (hz0 i) _ fun k => Set.mem_iInter.1 (hξ k).2 i
    exact ENNReal.toReal_le_of_le_ofReal (hz0 i) h6
  have hHc : IsCompact (convexHull ℝ K) := p2m66_isCompact_convexHull hKc
  by_contra hcon
  push Not at hcon
  set D := {x : Fin n → ℝ | ∃ y ∈ convexHull ℝ Y, y ≤ x} with hD
  have hDconv : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    obtain ⟨x', hx', hxx⟩ := hx
    obtain ⟨y', hy', hyy⟩ := hy
    refine ⟨a • x' + b • y', convex_convexHull ℝ Y hx' hy' ha hb hab, fun i => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hxx i) ha, mul_le_mul_of_nonneg_left (hyy i) hb]
  have hKD : K ⊆ D := by
    intro z hz
    obtain ⟨ξ, hξ, hle⟩ := hKY z hz
    exact ⟨vecReal t q ξ, subset_convexHull ℝ Y ⟨ξ, hξ, rfl⟩, fun i => hle i⟩
  have hHD : convexHull ℝ K ⊆ D := convexHull_min hKD hDconv
  set c : Fin n → ℝ := fun _ => v with hc
  have hdisj : Disjoint (convexHull ℝ K) (Set.Iic c) := by
    rw [Set.disjoint_left]
    intro x hx hxv
    obtain ⟨y, hy, hyx⟩ := hHD hx
    obtain ⟨i, hi⟩ := hcon y hy
    exact absurd ((hyx i).trans (hxv i)) (not_le.2 hi)
  obtain ⟨f, u0, v0, hfa, huv, hfb⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ K) hHc (convex_Iic c) isClosed_Iic hdisj
  have hf : ∀ x, f x = ∑ i, x i * f (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Pi.single i (x i) : Fin n → ℝ) = x i • (Pi.single i 1 : Fin n → ℝ) := by
      ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
    rw [this, map_smul, smul_eq_mul]
  set lam : Fin n → ℝ := fun i => - f (Pi.single i 1) with hlam
  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    by_contra h
    push Not at h
    have hpos' : 0 < f (Pi.single i 1) := by simp only [lam] at h; linarith
    set s := (|f c - v0| + 1) / f (Pi.single i 1) with hs
    have hs0 : 0 ≤ s := by positivity
    have hb : c - s • (Pi.single i 1 : Fin n → ℝ) ∈ Set.Iic c := by
      intro j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ (Pi.single i 1 : Fin n → ℝ) j := by
        by_cases h : j = i <;> simp [Pi.single_apply, h]
      nlinarith
    have h7 := hfb _ hb
    rw [map_sub, map_smul, smul_eq_mul, hs, div_mul_cancel₀ _ hpos'.ne'] at h7
    linarith [le_abs_self (f c - v0)]
  have hYK : Y ⊆ convexHull ℝ K := subset_closure.trans (subset_convexHull ℝ K)
  have hlamY : ∀ y ∈ Y, v * ∑ i, lam i < ∑ i, lam i * y i := by
    intro y hy
    have h1 := hfa y (hYK hy)
    have h2 := hfb c (le_refl c)
    have e : ∑ i, lam i * y i - v * ∑ i, lam i = f c - f y := by
      rw [hf c, hf y, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [lam, c]
      ring
    linarith
  obtain ⟨y0, hy0⟩ : Y.Nonempty := ⟨_, ⟨simpleSeq t q 1 p, p2m66_simple_conforms t q p 1, rfl⟩⟩
  set L := ∑ i, lam i with hL
  have hLpos : 0 < L := by
    by_contra h
    push Not at h
    have hz : ∀ i, lam i = 0 := fun i => le_antisymm (by
      have := Finset.single_le_sum (fun j _ => hlam0 j) (Finset.mem_univ i)
      linarith) (hlam0 i)
    have hL0 : L = 0 := by rw [hL]; exact Finset.sum_eq_zero fun i _ => hz i
    have := hlamY y0 hy0
    rw [hL0, mul_zero] at this
    simp [hz] at this
  set l : Fin n → ℝ := fun i => lam i / L with hl
  have hls : l ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun i => div_nonneg (hlam0 i) hLpos.le, ?_⟩
    simp only [l, ← Finset.sum_div]
    exact div_self hLpos.ne'
  obtain ⟨ξ, hξc, hξ⟩ := p2m66_stepA t q ht hq0 hq1 p hp hfinv l hls
  have hy : vecReal t q ξ ∈ Y := ⟨ξ, hξc, rfl⟩
  have h1 := hlamY _ hy
  rw [p2m66_searchCost t q l ht hq1 hls.1] at hξ
  have hsum : ∑ i, ENNReal.ofReal (l i) * V t q i ξ =
      ENNReal.ofReal (∑ i, l i * vecReal t q ξ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun i => l i * vecReal t q ξ i)
      (fun i _ => mul_nonneg (hls.1 i) ENNReal.toReal_nonneg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul (hls.1 i), vecReal, ENNReal.ofReal_toReal (hfin ξ hξc i)]
  rw [hsum, ← ENNReal.ofReal_toReal hfinv,
    ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at hξ
  have h8 : ∑ i, lam i * vecReal t q ξ i = L * ∑ i, l i * vecReal t q ξ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [l]
    field_simp
  rw [h8] at h1
  nlinarith [mul_le_mul_of_nonneg_left hξ hLpos.le]

set_option maxHeartbeats 1000000 in
open AllocationIndices Filter Topology DiscreteSearchGame.Optimal in
theorem solution {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : IsOptimalHider t q p) :
    ∃ η : PMF (ℕ → Fin n), IsOptimalSearcher t q η ∧
      ∃ s : Finset (ℕ → Fin n), s.card ≤ n ∧
        (↑s : Set (ℕ → Fin n)) ⊆ {ξ | ConformsToSearchIndex p q t ξ} ∧ η.support ⊆ ↑s := by
  classical
  have hn1 : n ≠ 0 := by
    rintro rfl
    have := hp.1.2
    simp at this
  haveI : NeZero n := ⟨hn1⟩
  have hv : gameValue t q ≠ ⊤ := p2m66_value_ne_top t q ht hq0 hq1
  have hpos : ∀ i, 0 < p i := p2m66_pos t q ht hq0 hq1 p hp hv
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hpos i).le
  set v : ℝ := (gameValue t q).toReal with hvdef
  have hfin : ∀ ξ, ConformsToSearchIndex p q t ξ → ∀ i, V t q i ξ ≠ ⊤ := fun ξ hξ i =>
    (p2m66_V_lt_top t q p ht hq0 hq1 hp0 ξ hξ i (hpos i)).ne
  obtain ⟨w, hwS, hwle⟩ := p2m66_minimax t q ht hq0 hq1 p hp hpos hv
  rw [convexHull_eq_union] at hwS
  simp only [Set.mem_iUnion] at hwS
  obtain ⟨T, hTS, hTai, hwT⟩ := hwS
  rw [Finset.mem_convexHull] at hwT
  obtain ⟨μ, hμ0, hμ1, hμw⟩ := hwT
  rw [Finset.centerMass_eq_of_sum_1 _ _ hμ1] at hμw
  simp only [id] at hμw
  -- each point of `T` is the payoff vector of a simple Gittins sequence
  have hTS' : ∀ y ∈ T, ∃ ξ, ConformsToSearchIndex p q t ξ ∧ vecReal t q ξ = y := by
    intro y hy
    obtain ⟨ξ, h1, h2⟩ := hTS hy
    exact ⟨ξ, h1, h2.symm⟩
  choose! g hgS hgy using hTS'
  have hgC : ∀ y ∈ T, ConformsToSearchIndex p q t (g y) := hgS
  have hgV : ∀ y ∈ T, ∀ i, V t q i (g y) = ENNReal.ofReal (y i) := by
    intro y hy i
    rw [← hgy y hy]; simp only [vecReal]
    rw [ENNReal.ofReal_toReal (hfin _ (hgC y hy) i), hgy y hy]
  -- the linear functional `x ↦ ∑ pᵢ xᵢ`
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, p i • LinearMap.proj i
  have hf : ∀ x, f x = ∑ i, p i * x i := by intro x; simp [f]
  have hfy : ∀ y ∈ T, v ≤ f y := by
    intro y hy
    have hsc := p2m66_searchCost t q p ht hq1 hp0 (g y)
    have hne : searchCost p q t (g y) ≠ ⊤ := by
      rw [hsc]
      exact ENNReal.sum_ne_top.2 fun i _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ (hgC y hy) i)
    have hle : gameValue t q ≤ searchCost p q t (g y) := by
      rw [← hp.2]; exact iInf_le _ _
    have h1 := ENNReal.toReal_mono hne hle
    rw [hsc, ENNReal.toReal_sum (fun i _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ (hgC y hy) i))] at h1
    rw [hf]
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp0 i), hgV y hy i,
      ENNReal.toReal_ofReal]
    rw [← hgy y hy]; exact ENNReal.toReal_nonneg
  have hfw : f w ≤ v := by
    rw [hf]
    calc ∑ i, p i * w i ≤ ∑ i, p i * v :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hwle i) (hp0 i)
      _ = v := by rw [← Finset.sum_mul, hp.1.2, one_mul]
  have hzero2 : ∑ y ∈ T, μ y * (f y - v) = 0 := by
    apply le_antisymm
    · have : ∑ y ∈ T, μ y * (f y - v) = f w - v := by
        rw [← hμw, map_sum]
        simp only [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          hμ1, one_mul]
      rw [this]; linarith
    · exact Finset.sum_nonneg fun y hy => mul_nonneg (hμ0 y hy) (by linarith [hfy y hy])
  have hTH : ∀ y ∈ T, 0 < μ y → f y = v := by
    intro y hy hμy
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
      mul_nonneg (hμ0 y hy) (by linarith [hfy y hy]))).1 hzero2 y hy
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  -- the positive-weight points
  set T' := T.filter (fun y => 0 < μ y) with hT'
  have hT'T : ∀ y ∈ T', y ∈ T := fun y hy => (Finset.mem_filter.1 hy).1
  have hT'pos : ∀ y ∈ T', 0 < μ y := fun y hy => (Finset.mem_filter.1 hy).2
  have hμ1' : ∑ y ∈ T', μ y = 1 := by
    rw [hT', Finset.sum_filter_of_ne]; exact hμ1
    intro y hy hne; exact lt_of_le_of_ne (hμ0 y hy) (Ne.symm hne)
  have hwi : ∀ i, w i = ∑ y ∈ T', μ y * y i := by
    intro i
    rw [← hμw, Finset.sum_apply, hT', Finset.sum_filter_of_ne]
    · rfl
    · intro y hy hne
      exact lt_of_le_of_ne (hμ0 y hy) (fun h => hne (by simp [← h]))
  -- Carathéodory in the hyperplane `f = v`: at most `n` points
  have hcard : T'.card ≤ n := by
    rcases Nat.eq_zero_or_pos T'.card with h0 | h0
    · omega
    let emb : {x // x ∈ T'} ↪ {x // x ∈ T} :=
      ⟨fun x => ⟨x.1, hT'T x.1 x.2⟩, by
        intro a b hab; exact Subtype.ext (by simpa using congrArg Subtype.val hab)⟩
    have hai : AffineIndependent ℝ (((↑) : {x // x ∈ T} → (Fin n → ℝ)) ∘ emb) :=
      hTai.comp_embedding emb
    have hcc : Fintype.card {x // x ∈ T'} = (T'.card - 1) + 1 := by
      rw [Fintype.card_coe]; omega
    have hfr := hai.finrank_vectorSpan hcc
    have hspan : vectorSpan ℝ (Set.range (((↑) : {x // x ∈ T} → (Fin n → ℝ)) ∘ emb)) ≤
        LinearMap.ker f := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro x ⟨a, ⟨a', rfl⟩, b, ⟨b', rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub, Function.comp_apply]
      have ha := hTH a'.1 (hT'T _ a'.2) (hT'pos _ a'.2)
      have hb := hTH b'.1 (hT'T _ b'.2) (hT'pos _ b'.2)
      show f a'.1 - f b'.1 = 0
      rw [ha, hb, sub_self]
    have hsurj : LinearMap.range f = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro r
      refine ⟨Pi.single (0 : Fin n) (r / p 0), ?_⟩
      rw [hf]
      simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      field_simp [(hpos 0).ne']
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrk
    have := Submodule.finrank_mono hspan
    omega
  -- the new search strategy
  set s' := T'.image g with hs'
  have hginj : Set.InjOn g ↑T' := by
    intro a ha b hb hab
    rw [← hgy a (hT'T a ha), ← hgy b (hT'T b hb), hab]
  have hsum' : ∑ ξ ∈ s', (if ξ ∈ s' then ENNReal.ofReal (μ (vecReal t q ξ)) else 0) = 1 := by
    rw [Finset.sum_congr rfl (fun ξ hξ => if_pos hξ), hs', Finset.sum_image hginj]
    rw [Finset.sum_congr rfl (fun y hy => by rw [hgy y (hT'T y hy)]),
      ← ENNReal.ofReal_sum_of_nonneg (fun y hy => (hT'pos y hy).le), hμ1', ENNReal.ofReal_one]
  let η' : PMF (ℕ → Fin n) := PMF.ofFinset
    (fun ξ => if ξ ∈ s' then ENNReal.ofReal (μ (vecReal t q ξ)) else 0) s' hsum'
    (fun ξ hξ => if_neg hξ)
  refine ⟨η', ?_, s', (Finset.card_image_le).trans hcard, ?_, ?_⟩
  · intro i
    have hV' : Vmix t q i η' = ∑ ξ ∈ s', ENNReal.ofReal (μ (vecReal t q ξ)) * V t q i ξ := by
      unfold Vmix
      rw [tsum_eq_sum (s := s') (fun ξ hξ => by
        simp only [η', PMF.ofFinset_apply, if_neg hξ, zero_mul])]
      exact Finset.sum_congr rfl fun ξ hξ => by simp only [η', PMF.ofFinset_apply, if_pos hξ]
    rw [hV', hs', Finset.sum_image hginj]
    rw [Finset.sum_congr rfl (fun y hy => by rw [hgy y (hT'T y hy), hgV y (hT'T y hy) i])]
    rw [Finset.sum_congr rfl (fun y hy => (ENNReal.ofReal_mul (hT'pos y hy).le).symm)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y hy => mul_nonneg (hT'pos y hy).le (by
      rw [← hgy y (hT'T y hy)]; exact ENNReal.toReal_nonneg))]
    rw [← hwi i]
    calc ENNReal.ofReal (w i) ≤ ENNReal.ofReal v := ENNReal.ofReal_le_ofReal (hwle i)
      _ = gameValue t q := ENNReal.ofReal_toReal hv
  · intro ξ hξ
    rw [hs', Finset.coe_image] at hξ
    obtain ⟨y, hy, rfl⟩ := hξ
    exact hgS y (hT'T y hy)
  · intro ξ hξ
    rw [PMF.mem_support_iff] at hξ
    by_contra h
    exact hξ (by simp only [η', PMF.ofFinset_apply]; exact if_neg h)
