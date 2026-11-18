-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:30:19.577161+00:00
-- url     : https://prove2.me/submissions/b68ea0d4-f786-4133-bc75-267d10147568

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace CutProof

def expect {Ω : Type*} [Fintype Ω] (mu : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ s, mu s * f s

lemma expect_sum {Ω ι : Type*} [Fintype Ω] (mu : Ω → ℝ)
    (s : Finset ι) (f : ι → Ω → ℝ) :
    expect mu (fun w => ∑ i ∈ s, f i w) = ∑ i ∈ s, expect mu (f i) := by
  unfold expect
  simp_rw [mul_sum]
  exact sum_comm

lemma expect_add {Ω : Type*} [Fintype Ω] (mu : Ω → ℝ) (f g : Ω → ℝ) :
    expect mu (fun w => f w + g w) = expect mu f + expect mu g := by
  simp [expect, mul_add, sum_add_distrib]

lemma expect_mul {Ω : Type*} [Fintype Ω] (mu : Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    expect mu (fun w => c * f w) = c * expect mu f := by
  unfold expect
  simp_rw [← mul_assoc, mul_comm (mu _) c, mul_assoc]
  exact (mul_sum ..).symm

lemma second_moment {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (mu : Ω → ℝ) (I : ι → Ω → ℝ)
    (hdiag : ∀ a, expect mu (fun s => I a s * I a s) = expect mu (I a))
    (hind : ∀ a b, a ≠ b → expect mu (fun s => I a s * I b s) =
      expect mu (I a) * expect mu (I b)) :
    expect mu (fun s => (∑ a, I a s)^2) ≤
      (∑ a, expect mu (I a))^2 + ∑ a, expect mu (I a) := by
  have heq : expect mu (fun s => (∑ a, I a s)^2) =
      ∑ a, ∑ b, expect mu (fun s => I a s * I b s) := by
    simp_rw [pow_two, sum_mul, mul_sum]
    rw [expect_sum]
    apply sum_congr rfl
    intro a _
    exact expect_sum mu univ _
  rw [heq]
  calc
    _ ≤ ∑ a, ∑ b, (expect mu (I a) * expect mu (I b) +
        if a = b then expect mu (I a) else 0) := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      by_cases hab : a = b
      · subst b
        rw [hdiag, if_pos rfl]
        nlinarith [sq_nonneg (expect mu (I a))]
      · rw [hind a b hab, if_neg hab, add_zero]
    _ = _ := by
      simp [sum_add_distrib, ← mul_sum, ← sum_mul, pow_two]

variable {N : ℕ} {p : Pairing N} (B : BlockAssignment p)

def labels (a : Copy p) (v : Fin N) : Finset (Copy p) :=
  (block B a).filter (fun c => c.1 = v)

def indicator (v : Fin N) (a : Copy p) (s : Copy p → Copy p) : ℝ :=
  if B a = some a ∧ (s a).1 = v then 1 else 0

lemma indicator_sq (v : Fin N) (a : Copy p) (s : Copy p → Copy p) :
    indicator B v a s * indicator B v a s = indicator B v a s := by
  unfold indicator
  split_ifs <;> norm_num

lemma indicator_sum (v : Fin N) (a : Copy p) (ha : B a = some a)
    (s : Copy p → Copy p) (hs : ValidCuts B s) :
    indicator B v a s = ∑ c ∈ labels B a v, if s a = c then (1 : ℝ) else 0 := by
  have hsa := hs a ha
  simp [indicator,ha,labels, sum_ite_eq, hsa]

lemma marginal (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (v : Fin N) (a : Copy p) :
    expect mu (indicator B v a) =
      if B a = some a then (labels B a v).card / ((block B a).card : ℝ) else 0 := by
  by_cases ha : B a = some a
  · rw [if_pos ha]
    calc
      _ = expect mu (fun s => ∑ c ∈ labels B a v, if s a = c then (1 : ℝ) else 0) := by
        apply sum_congr rfl
        intro s _
        by_cases hs : mu s = 0
        · simp [hs]
        · rw [indicator_sum B v a ha s (hmu.2.2.1 s hs)]
      _ = ∑ c ∈ labels B a v, 1 / ((block B a).card : ℝ) := by
        rw [expect_sum]
        apply sum_congr rfl
        intro c hc
        unfold expect
        simp_rw [mul_ite, mul_one, mul_zero]
        exact hmu.2.2.2.1 a ha c (mem_filter.mp hc).1
      _ = _ := by simp [div_eq_mul_inv]
  · simp [indicator,ha,expect]

lemma joint (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (v : Fin N) (a b : Copy p) (hab : a ≠ b) :
    expect mu (fun s => indicator B v a s * indicator B v b s) =
      expect mu (indicator B v a) * expect mu (indicator B v b) := by
  by_cases ha : B a = some a
  · by_cases hb : B b = some b
    · calc
        _ = expect mu (fun s => ∑ c ∈ labels B a v, ∑ d ∈ labels B b v,
            if s a = c ∧ s b = d then (1 : ℝ) else 0) := by
          apply sum_congr rfl
          intro s _
          dsimp only
          by_cases hs : mu s = 0
          · simp [hs]
          · rw [indicator_sum B v a ha s (hmu.2.2.1 s hs),
              indicator_sum B v b hb s (hmu.2.2.1 s hs)]
            congr 1
            simp_rw [sum_mul, mul_sum]
            apply sum_congr rfl
            intro c _
            apply sum_congr rfl
            intro d _
            split_ifs <;> simp_all
        _ = ∑ c ∈ labels B a v, ∑ d ∈ labels B b v,
            1 / (((block B a).card : ℝ) * (block B b).card) := by
          rw [expect_sum]
          apply sum_congr rfl
          intro c hc
          rw [expect_sum]
          apply sum_congr rfl
          intro d hd
          unfold expect
          simp_rw [mul_ite, mul_one, mul_zero]
          exact hmu.2.2.2.2 a b ha hb hab c (mem_filter.mp hc).1 d (mem_filter.mp hd).1
        _ = _ := by
          rw [marginal B mu hmu v a, marginal B mu hmu v b, if_pos ha, if_pos hb]
          simp only [sum_const, nsmul_eq_mul]
          rw [div_eq_mul_inv, mul_inv]
          ring
    · simp [indicator,hb,expect]
  · simp [indicator,ha,expect]

lemma indicators_eq_count (v : Fin N) (s : Copy p → Copy p) :
    (∑ a, indicator B v a s) = (cutCount B s v : ℝ) := by
  simp only [indicator,cutCount,card_eq_sum_ones,sum_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma count_second_moment (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (v : Fin N) :
    expect mu (fun s => (cutCount B s v : ℝ)^2) ≤
      (expect mu (fun s => (cutCount B s v : ℝ)))^2 +
        expect mu (fun s => (cutCount B s v : ℝ)) := by
  have h := second_moment mu (indicator B v)
    (fun a => by simp only [indicator_sq]) (joint B mu hmu v)
  simp_rw [← expect_sum, indicators_eq_count] at h
  exact h

lemma labels_sum_bound (v : Fin N) :
    (∑ a : Copy p, (labels B a v).card) ≤ (p v).length := by
  have hd : ((univ : Finset (Copy p)) : Set (Copy p)).PairwiseDisjoint (fun a => labels B a v) := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro c hc hd
    have hc' : B c = some a := (mem_filter.mp (mem_filter.mp hc).1).2
    have hd' : B c = some b := (mem_filter.mp (mem_filter.mp hd).1).2
    exact hab (Option.some.inj (hc'.symm.trans hd'))
  rw [← card_biUnion hd]
  calc
    _ ≤ (univ.filter (fun c : Copy p => c.1 = v)).card := by
      apply card_le_card
      intro c hc
      obtain ⟨a,_,ha⟩ := mem_biUnion.mp hc
      exact mem_filter.mpr ⟨mem_univ c,(mem_filter.mp ha).2⟩
    _ = _ := by
      simp only [card_eq_sum_ones,sum_filter]
      rw [Fintype.sum_sigma]
      change (∑ u : Fin N, ∑ i : Fin (p u).length, if u = v then 1 else 0) = _
      calc
        _ = ∑ u : Fin N, if u = v then (p u).length else 0 := by
          apply sum_congr rfl
          intro u _
          by_cases hu : u = v <;> simp [hu]
        _ = _ := by simp

lemma copies_le_active (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (q : ℝ) (hp : ValidPairing G x q p) (v : Fin N) :
    (p v).length ≤ activeDegree G x q v := by
  have hn (i : Fin (p v).length) : (group p ⟨v,i⟩).Nonempty := by
    have h := hp.1 ⟨v,i⟩
    apply card_pos.mp
    omega
  let pick (i : Fin (p v).length) := (hn i).choose
  have hpick (i : Fin (p v).length) : pick i ∈ group p ⟨v,i⟩ := (hn i).choose_spec
  have hinj : Function.Injective pick := by
    intro i j hij
    have hactive := hp.2.2.1 ⟨v,i⟩ (pick i) (hpick i)
    have hunique := (hp.2.1 v (pick i)).mp hactive
    have hi : pick i ∈ (p v).get i := hpick i
    have hj : pick i ∈ (p v).get j := hij ▸ hpick j
    exact (hunique.unique hi hj)
  let f : Fin (p v).length → ↥((G.neighborFinset v).filter (fun w => x s(v,w) = q)) :=
    fun i => ⟨pick i, by
      apply mem_filter.mpr
      have h := hp.2.2.1 ⟨v,i⟩ (pick i) (hpick i)
      exact ⟨by simpa using h.1,h.2⟩⟩
  have hf : Function.Injective f := fun i j hij => hinj (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  change (p v).length ≤ ((G.neighborFinset v).filter (fun w => x s(v,w) = q)).card
  simpa only [Fintype.card_fin,Fintype.card_coe] using hcard

lemma count_mean_bound (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B)
    (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (v : Fin N) :
    0 ≤ expect mu (fun s => (cutCount B s v : ℝ)) ∧
      expect mu (fun s => (cutCount B s v : ℝ)) ≤ (activeDegree G x q v : ℝ) / ell := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  constructor
  · exact sum_nonneg fun s _ => mul_nonneg (hmu.1 s) (Nat.cast_nonneg _)
  · simp_rw [← indicators_eq_count B v]
    rw [expect_sum]
    calc
      _ ≤ ∑ a : Copy p, (labels B a v).card / (ell : ℝ) := by
        apply sum_le_sum
        intro a _
        rw [marginal B mu hmu v a]
        by_cases ha : B a = some a
        · rw [if_pos ha]
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hl
          exact_mod_cast (hB.2 a a ha).2.1
        · rw [if_neg ha]; positivity
      _ = (∑ a : Copy p, (labels B a v).card : ℕ) / (ell : ℝ) := by
        simp [sum_div]
      _ ≤ (activeDegree G x q v : ℝ) / ell := by
        apply div_le_div_of_nonneg_right _ hl.le
        exact_mod_cast (labels_sum_bound B v).trans (copies_le_active G x q hp v)

section Physical
variable (G : SimpleGraph (Fin N))

lemma load_as_edges (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G x v = ∑ e ∈ G.edgeFinset, if v ∈ e then x e else 0 := by
  unfold load RandomOrderCRS.fracDegree
  rw [G.incidenceFinset_eq_filter]
  exact sum_filter ..

lemma sum_loads (x : Sym2 (Fin N) → ℝ) :
    (∑ v : Fin N, load G x v) = 2 * totalWeight G x := by
  simp_rw [load_as_edges]
  rw [sum_comm]
  unfold totalWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro e he
  obtain ⟨⟨u,w⟩,rfl⟩ := e.exists_rep
  have huw : u ≠ w := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
  have hh (v : Fin N) :
      (if v ∈ s(u,w) then x s(u,w) else 0) =
        (if v = u then x s(u,w) else 0) + (if v = w then x s(u,w) else 0) := by
    simp only [Sym2.mem_iff]
    by_cases h1 : v = u <;> by_cases h2 : v = w <;> simp_all
  simp_rw [hh, sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, if_true]
  ring

lemma load_as_neighbors (x : Sym2 (Fin N) → ℝ) (v : Fin N) :
    load G x v = ∑ w ∈ G.neighborFinset v, x s(v,w) := by
  unfold load RandomOrderCRS.fracDegree
  symm
  apply sum_bij (fun w _ => s(v,w))
  · intro w hw
    simpa using hw
  · intro a ha b hb hab
    exact Sym2.congr_right.mp hab
  · intro e he
    have hi := (G.mem_incidenceFinset v e).mp he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hi.2
    exact ⟨w, by simpa using hi.1, rfl⟩
  · intro w hw
    rfl


lemma active_load (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (q : ℝ) (v : Fin N) :
    q * (activeDegree G x q v : ℝ) ≤ load G x v := by
  rw [load_as_neighbors]
  calc
    _ = ∑ w ∈ (G.neighborFinset v).filter (fun w => x s(v,w) = q), x s(v,w) := by
      rw [activeDegree]
      symm
      calc
        _ = ∑ w ∈ (G.neighborFinset v).filter (fun w => x s(v,w) = q), q := by
          apply sum_congr rfl
          intro w hw
          exact (mem_filter.mp hw).2
        _ = _ := by simp [mul_comm]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun w _ _ => hx _)

end Physical

lemma expanded_moment (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (v : Fin N) (r : ℝ) :
    expect mu (fun s => (2 * (cutCount B s v : ℝ) + r)^2) =
      4 * expect mu (fun s => (cutCount B s v : ℝ)^2) +
      4 * r * expect mu (fun s => (cutCount B s v : ℝ)) + r^2 := by
  have hh (s : Copy p → Copy p) : (2 * (cutCount B s v : ℝ) + r)^2 =
      4 * (cutCount B s v : ℝ)^2 + 4*r*(cutCount B s v : ℝ) + r^2 := by ring
  simp_rw [hh, expect_add, expect_mul]
  have hc : expect mu (fun _ => r^2) = r^2 := by
    unfold expect
    rw [← sum_mul, hmu.2.1, one_mul]
  rw [hc]

lemma vertex_moment_bound (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B)
    (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) (q : ℝ)
    (hp : ValidPairing G x q p) (v : Fin N) :
    expect mu (fun s => (2 * (cutCount B s v : ℝ) +
      (activeDegree G x q v % 2 : ℕ))^2) ≤
        4 * ((activeDegree G x q v : ℝ) / ell)^2 + 9 * activeDegree G x q v := by
  have hm := count_mean_bound B ell hell hB mu hmu G x q hp v
  have hs := count_second_moment B mu hmu v
  have he : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hd : (0 : ℝ) ≤ activeDegree G x q v := Nat.cast_nonneg _
  have hle : (activeDegree G x q v : ℝ) / ell ≤ activeDegree G x q v :=
    div_le_self hd he
  have hr0 : (0 : ℝ) ≤ (activeDegree G x q v % 2 : ℕ) := Nat.cast_nonneg _
  have hr1 : ((activeDegree G x q v % 2 : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast (show activeDegree G x q v % 2 ≤ 1 by omega)
  have hrd : ((activeDegree G x q v % 2 : ℕ) : ℝ) ≤ activeDegree G x q v := by
    exact_mod_cast Nat.mod_le (activeDegree G x q v) 2
  have hsquare := mul_self_le_mul_self hm.1 hm.2
  have hmul := mul_nonneg (sub_nonneg.mpr hr1) hm.1
  have hrsq := mul_nonneg hr0 (sub_nonneg.mpr hr1)
  rw [expanded_moment B mu hmu]
  nlinarith

lemma vertex_cost_bound (ell : ℕ) (hell : 2 ≤ ell) (hB : ValidBlocks ell B)
    (mu : (Copy p → Copy p) → ℝ) (hmu : PairwiseUniformCuts B mu)
    (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (hx : NonnegativeAssignment G x) (q : ℝ) (hq : 0 < q)
    (hp : ValidPairing G x q p) (v : Fin N) :
    2 * q^2 * expect mu (fun s => (2 * (cutCount B s v : ℝ) +
      (activeDegree G x q v % 2 : ℕ))^2) ≤
        8 * (load G x v)^2 / (ell : ℝ)^2 + 18 * q * load G x v := by
  have hm := vertex_moment_bound B ell hell hB mu hmu G x q hp v
  have ha := active_load G x hx.1 q v
  have hqd : 0 ≤ q * (activeDegree G x q v : ℝ) := mul_nonneg hq.le (Nat.cast_nonneg _)
  have hsq := mul_self_le_mul_self hqd ha
  have hquad : q^2 * ((activeDegree G x q v : ℝ) / ell)^2 ≤
      (load G x v)^2 / (ell : ℝ)^2 := by
    rw [div_pow]
    calc
      _ = (q * (activeDegree G x q v : ℝ))^2 / (ell : ℝ)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hsq]) (sq_nonneg _)
  have hlin : q^2 * (activeDegree G x q v : ℝ) ≤ q * load G x v := by
    nlinarith only [mul_le_mul_of_nonneg_left ha hq.le]
  calc
    _ ≤ 2*q^2 * (4 * ((activeDegree G x q v : ℝ) / ell)^2 + 9 * activeDegree G x q v) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 8 * (q^2 * ((activeDegree G x q v : ℝ) / ell)^2) +
        18 * (q^2 * (activeDegree G x q v : ℝ)) := by ring
    _ ≤ 8 * ((load G x v)^2 / (ell : ℝ)^2) + 18 * (q * load G x v) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hquad (by norm_num))
        (mul_le_mul_of_nonneg_left hlin (by norm_num))
    _ = _ := by ring

end CutProof

theorem solution (N : ℕ) (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (hx : NonnegativeAssignment G x) (q : ℝ) (hq : 0 < q) (ell : ℕ) (hell : 2 ≤ ell)
    (p : Pairing N) (hp : ValidPairing G x q p) (B : BlockAssignment p)
    (hB : ValidBlocks ell B) (mu : (Copy p → Copy p) → ℝ)
    (hmu : PairwiseUniformCuts B mu) :
    (∑ s, mu s * cutCost G x q B s) ≤
      4 * penalty G x / (ell : ℝ) ^ 2 + 36 * q * totalWeight G x := by
  change CutProof.expect mu (fun s => cutCost G x q B s) ≤ _
  unfold cutCost
  rw [CutProof.expect_mul, CutProof.expect_sum, mul_sum]
  calc
    _ ≤ ∑ v : Fin N, (8 * (load G x v)^2 / (ell : ℝ)^2 + 18 * q * load G x v) :=
      sum_le_sum fun v _ => CutProof.vertex_cost_bound B ell hell hB mu hmu G x hx q hq hp v
    _ = _ := by
      rw [sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum, CutProof.sum_loads G x]
      unfold penalty
      ring

