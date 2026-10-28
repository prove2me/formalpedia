-- Prove2me | solution 1 for DiscreteSearchGame.Optimal.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T12:01:53.698851+00:00
-- url     : https://prove2.me/submissions/9465e0f2-2d54-48c0-bcc5-50099a74a26f

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model
import Theorems.Thm_DiscreteSearchGame_Optimal_theorem_6
import Theorems.Thm_DiscreteSearchGame_Optimal_lemma_9
import Theorems.Thm_DiscreteSearchGame_Optimal_proposition_3_1

set_option autoImplicit false

open AllocationIndices Filter Topology

open AllocationIndices in
lemma p2mbad6_sc_eq {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ k i = ∑ t ∈ Finset.range k, if σ t = i then 1 else 0 := by
  unfold searchCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if σ t = i then 1 else 0) k

open AllocationIndices in
lemma p2mbad6_sc_succ {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ (k + 1) i = searchCount σ k i + if σ k = i then 1 else 0 := by
  rw [p2mbad6_sc_eq, p2mbad6_sc_eq, Finset.sum_range_succ]

open AllocationIndices in
lemma p2mbad6_sc_mono {n : ℕ} (σ : ℕ → Fin n) (i : Fin n) {k k' : ℕ} (h : k ≤ k') :
    searchCount σ k i ≤ searchCount σ k' i := by
  rw [p2mbad6_sc_eq, p2mbad6_sc_eq]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2mbad6_ruleCounts {n : ℕ} [NeZero n] (t q p : Fin n → ℝ) (r : Rule n) (k : ℕ)
    (i : Fin n) : ruleCounts t q p r k i = searchCount (ruleSeq t q r p) k i := by
  induction k generalizing i with
  | zero => simp [ruleCounts, searchCount]
  | succ k ih =>
    have h1 : ruleCounts t q p r (k + 1) i =
        ruleCounts t q p r k i + (Pi.single (ruleSeq t q r p k) 1 : Fin n → ℕ) i := rfl
    rw [h1, ih, p2mbad6_sc_succ, Pi.single_apply]
    by_cases h : ruleSeq t q r p k = i
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

open DiscreteSearchGame.Optimal in
lemma p2mbad6_tieBreak_max {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (f : Fin n → ℝ)
    (i : Fin n) : f i ≤ f (tieBreak σ f) := by
  unfold tieBreak
  set S := Finset.univ.filter fun j : Fin n => ∀ i, f i ≤ f (σ j) with hS
  have hm : ∀ H, S.min' H ∈ S := fun H => Finset.min'_mem S H
  exact (Finset.mem_filter.1 (hm _)).2 i

open AllocationIndices DiscreteSearchGame.Optimal in
lemma p2mbad6_simple_conforms {n : ℕ} [NeZero n] (t q p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ConformsToSearchIndex p q t (simpleSeq t q σ p) := by
  intro k i
  have hc : ∀ j, searchIndex p q t (simpleSeq t q σ p) k j =
      gittinsIndex t q p (ruleCounts t q p (fun _ => σ) k) j := by
    intro j
    simp only [searchIndex, gittinsIndex, p2mbad6_ruleCounts]
    rfl
  rw [hc, hc]
  exact p2mbad6_tieBreak_max σ _ i

open AllocationIndices DiscreteSearchGame.Optimal in
/-- Every box is cheap to find under a Gittins sequence against `p` with `p i > 0`. -/
lemma p2mbad6_V_lt_top {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
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
      have hm := p2mbad6_sc_mono ξ (ξ a) (Nat.succ_le_of_lt hab)
      rw [p2mbad6_sc_succ, if_pos rfl] at hm
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
lemma p2mbad6_searchCost {n : ℕ} (t q p : Fin n → ℝ) (ht : ∀ i, 0 < t i)
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

open AllocationIndices Filter Topology DiscreteSearchGame.Optimal in
theorem solution {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : IsOptimalHider t q p) :
    ∃ η : PMF (ℕ → Fin n), IsOptimalSearcher t q η ∧
      ∃ s : Finset (ℕ → Fin n), s.card ≤ n ∧
        (↑s : Set (ℕ → Fin n)) ⊆ simpleGittins t q p ∧ η.support ⊆ ↑s := by
  classical
  have hpos : ∀ i, 0 < p i := proposition_3_1 t q ht hq0 hq1 p hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hpos i).le
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  by_cases hv : gameValue t q = ⊤
  · refine ⟨PMF.pure (simpleSeq t q 1 p), fun i => by rw [hv]; exact le_top,
      {simpleSeq t q 1 p}, by simpa using hn1, ?_, ?_⟩
    · simp only [Finset.coe_singleton, Set.singleton_subset_iff]; exact ⟨1, rfl⟩
    · simp [PMF.support_pure]
  obtain ⟨η, hη, s, -, hsC, hηs⟩ := theorem_6 t q ht hq0 hq1 p hp
  set v : ℝ := (gameValue t q).toReal with hvdef
  have hfin : ∀ ξ, ConformsToSearchIndex p q t ξ → ∀ i, V t q i ξ ≠ ⊤ := fun ξ hξ i =>
    (p2mbad6_V_lt_top t q p ht hq0 hq1 hp0 ξ hξ i (hpos i)).ne
  -- the payoff vector `w` of `η`
  set w : Fin n → ℝ := fun i => (Vmix t q i η).toReal with hwdef
  have hzero : ∀ ξ ∉ s, η ξ = 0 := by
    intro ξ hξ; by_contra h; exact hξ (hηs ((PMF.mem_support_iff _ _).2 h))
  have hηsum : ∑ ξ ∈ s, η ξ = 1 := by
    rw [← η.tsum_coe]; symm; exact tsum_eq_sum (fun ξ hξ => hzero ξ hξ)
  have hVmix : ∀ i, Vmix t q i η = ∑ ξ ∈ s, η ξ * V t q i ξ := by
    intro i; unfold Vmix
    exact tsum_eq_sum (fun ξ hξ => by rw [hzero ξ hξ, zero_mul])
  have hw : w = ∑ ξ ∈ s, (η ξ).toReal • vecReal t q ξ := by
    funext i
    simp only [w, hVmix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecReal]
    rw [ENNReal.toReal_sum]
    · simp [ENNReal.toReal_mul]
    · intro ξ hξ; exact ENNReal.mul_ne_top (PMF.apply_ne_top η ξ) (hfin ξ (hsC hξ) i)
  have hwsum : ∑ ξ ∈ s, (η ξ).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun ξ _ => PMF.apply_ne_top η ξ), hηsum]; simp
  have hwC : w ∈ convexHull ℝ (payoffSet t q p) := by
    rw [hw]
    refine (convex_convexHull ℝ _).sum_mem (fun ξ _ => ENNReal.toReal_nonneg) hwsum ?_
    intro ξ hξ; exact subset_convexHull ℝ _ ⟨ξ, hsC hξ, rfl⟩
  have hwle : ∀ i, w i ≤ v := fun i => ENNReal.toReal_mono hv (hη i)
  -- Lemma 9 moves `w` into the hull of the simple Gittins payoff vectors
  have hwS : w ∈ convexHull ℝ (simplePayoffSet t q p) := by
    rw [← lemma_9 t q ht hq0 hq1 p hp.1 hpos]; exact hwC
  rw [convexHull_eq_union] at hwS
  simp only [Set.mem_iUnion] at hwS
  obtain ⟨T, hTS, hTai, hwT⟩ := hwS
  rw [Finset.mem_convexHull] at hwT
  obtain ⟨μ, hμ0, hμ1, hμw⟩ := hwT
  rw [Finset.centerMass_eq_of_sum_1 _ _ hμ1] at hμw
  simp only [id] at hμw
  -- each point of `T` is the payoff vector of a simple Gittins sequence
  have hTS' : ∀ y ∈ T, ∃ ξ, ξ ∈ simpleGittins t q p ∧ vecReal t q ξ = y :=
    fun y hy => hTS hy
  choose! g hgS hgy using hTS'
  have hgC : ∀ y ∈ T, ConformsToSearchIndex p q t (g y) := by
    intro y hy; obtain ⟨σ, hσ⟩ := hgS y hy; rw [← hσ]; exact p2mbad6_simple_conforms t q p σ
  have hgV : ∀ y ∈ T, ∀ i, V t q i (g y) = ENNReal.ofReal (y i) := by
    intro y hy i
    rw [← hgy y hy]; simp only [vecReal]
    rw [ENNReal.ofReal_toReal (hfin _ (hgC y hy) i), hgy y hy]
  -- the linear functional `x ↦ ∑ pᵢ xᵢ`
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, p i • LinearMap.proj i
  have hf : ∀ x, f x = ∑ i, p i * x i := by intro x; simp [f]
  have hfy : ∀ y ∈ T, v ≤ f y := by
    intro y hy
    have hsc := p2mbad6_searchCost t q p ht hq1 hp0 (g y)
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
