-- Prove2me | solution 1 for ExplicitExpanders.Delete.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T06:04:33.4064+00:00
-- url     : https://prove2.me/submissions/5a76a57e-5b17-491b-b833-bbd52f93b18e

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

set_option autoImplicit false

namespace P2MEq11

open ExplicitExpanders.Delete

section tree
variable {V : Type*} (H : SimpleGraph V)

lemma adj_lvl {z x y : V} {k : ℕ} (h : H.Adj x y) (hx : H.edist z x = k) :
    ∃ j : ℕ, H.edist z y = j ∧ j ≤ k + 1 ∧ k ≤ j + 1 := by
  have h1 : H.edist z y ≤ H.edist z x + H.edist x y := H.edist_triangle
  have h2 : H.edist z x ≤ H.edist z y + H.edist y x := H.edist_triangle
  rw [SimpleGraph.edist_eq_one_iff_adj.2 h] at h1
  rw [SimpleGraph.edist_eq_one_iff_adj.2 h.symm] at h2
  rw [hx] at h1 h2
  have hne : H.edist z y ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
  refine ⟨j, hj.symm, ?_, ?_⟩
  · rw [← hj] at h1; exact_mod_cast h1
  · rw [← hj] at h2; exact_mod_cast h2

lemma tri_le {x y w : V} {a b c : ℕ} (h1 : H.edist x y = a) (h2 : H.edist y w = b)
    (h3 : H.edist x w = c) : c ≤ a + b := by
  have := H.edist_triangle (u := x) (v := y) (w := w)
  rw [h1, h2, h3] at this
  exact_mod_cast this

lemma lift_walk (S : Set V) : ∀ {x y : V} (p : H.Walk x y) (hs : ∀ v ∈ p.support, v ∈ S),
    ∃ q : (H.induce S).Walk ⟨x, hs x p.start_mem_support⟩ ⟨y, hs y p.end_mem_support⟩,
      q.support.map Subtype.val = p.support
  | _, _, .nil, hs => ⟨.nil, by simp⟩
  | _, _, .cons h p, hs => by
    obtain ⟨q, hq⟩ := lift_walk S p (fun v hv => hs v (by simp [hv]))
    refine ⟨.cons (by simpa using h) q, ?_⟩
    simp [hq]

lemma supp_unique {S : Set V} (hT : (H.induce S).IsAcyclic) {x y : V} (p q : H.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) (hps : ∀ v ∈ p.support, v ∈ S)
    (hqs : ∀ v ∈ q.support, v ∈ S) : p.support = q.support := by
  obtain ⟨p', hp'⟩ := lift_walk H S p hps
  obtain ⟨q', hq'⟩ := lift_walk H S q hqs
  have hp'' : p'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    apply List.Nodup.of_map Subtype.val
    rw [hp']; exact hp.support_nodup
  have hq'' : q'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    apply List.Nodup.of_map Subtype.val
    rw [hq']; exact hq.support_nodup
  have h1 := hT.path_unique ⟨p', hp''⟩ ⟨q', hq''⟩
  have h2 : p' = q' := congrArg Subtype.val h1
  rw [← hp', ← hq', h2]

lemma geo {x y : V} {k : ℕ} (h : H.edist x y = k) : ∃ p : H.Walk x y, p.length = k ∧ p.IsPath := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h
  refine ⟨p, hp, p.isPath_of_length_eq_dist ?_⟩
  simp [SimpleGraph.dist, h, hp]

lemma supp_ball {z x : V} {R : ℕ} (p : H.Walk x z) (hp : p.length ≤ R) :
    ∀ v ∈ p.support, v ∈ ball H z R := by
  classical
  intro v hv
  show H.edist z v ≤ (R : ℕ∞)
  rw [SimpleGraph.edist_comm]
  refine (SimpleGraph.edist_le (p.dropUntil v hv)).trans ?_
  exact_mod_cast (p.length_dropUntil_le_length hv).trans hp

/-- unique lower neighbour in a tree-like ball -/
lemma F2 {z w y1 y2 : V} {k R : ℕ} (hT : NoCycleOn H (ball H z R)) (hk : k + 1 ≤ R)
    (hw : H.edist z w = ((k + 1 : ℕ) : ℕ∞)) (h1 : H.Adj w y1) (h2 : H.Adj w y2)
    (hy1 : H.edist z y1 = k) (hy2 : H.edist z y2 = k) : y1 = y2 := by
  rw [SimpleGraph.edist_comm] at hw hy1 hy2
  obtain ⟨g1, hg1, -⟩ := geo H hy1
  obtain ⟨g2, hg2, -⟩ := geo H hy2
  have hl1 : (SimpleGraph.Walk.cons h1 g1).length = k + 1 := by simp [hg1]
  have hl2 : (SimpleGraph.Walk.cons h2 g2).length = k + 1 := by simp [hg2]
  have hp1 : (SimpleGraph.Walk.cons h1 g1).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [hl1, SimpleGraph.dist, hw, ENat.toNat_coe])
  have hp2 : (SimpleGraph.Walk.cons h2 g2).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [hl2, SimpleGraph.dist, hw, ENat.toNat_coe])
  have := supp_unique H hT _ _ hp1 hp2 (supp_ball H _ (by omega)) (supp_ball H _ (by omega))
  simp only [SimpleGraph.Walk.support_cons] at this
  rw [g1.support_eq_cons, g2.support_eq_cons] at this
  exact (List.cons.inj (List.cons.inj this).2).1

/-- no edge inside a level of a tree-like ball -/
lemma F1 {z w1 w2 : V} {k R : ℕ} (hT : NoCycleOn H (ball H z R)) (hk : k + 1 ≤ R)
    (h : H.Adj w1 w2) (hw1 : H.edist z w1 = k) (hw2 : H.edist z w2 = k) : False := by
  classical
  obtain ⟨g1, hg1, hp1⟩ := geo H hw1
  obtain ⟨g2, hg2, hp2⟩ := geo H hw2
  have hne : w2 ≠ w1 := h.ne.symm
  have hnot : w2 ∉ g1.support := by
    intro hm
    have h3 := SimpleGraph.Walk.length_takeUntil_lt_length hm hne
    have h4 := SimpleGraph.edist_le (g1.takeUntil w2 hm)
    rw [hw2] at h4
    have : k ≤ (g1.takeUntil w2 hm).length := by exact_mod_cast h4
    omega
  have hpath : (SimpleGraph.Walk.cons h.symm g1.reverse).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.isPath_reverse_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact ⟨hp1, hnot⟩
  have := supp_unique H hT _ _ hpath ((SimpleGraph.Walk.isPath_reverse_iff _).2 hp2)
    (supp_ball H _ (by simp [hg1]; omega)) (supp_ball H _ (by simp [hg2]; omega))
  have := congrArg List.length this
  simp [SimpleGraph.Walk.length_support, hg1, hg2] at this

end tree

section layers
variable {V : Type*} [Fintype V] (H : SimpleGraph V)

noncomputable def lay (z a : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun w => H.edist z w = ((i + 1 : ℕ) : ℕ∞) ∧ H.edist a w = (i : ℕ∞)

lemma mem_lay {z a w : V} {i : ℕ} :
    w ∈ lay H z a i ↔ H.edist z w = ((i + 1 : ℕ) : ℕ∞) ∧ H.edist a w = (i : ℕ∞) := by
  simp [lay]

lemma lay_zero {z a w : V} (hza : H.Adj z a) : w ∈ lay H z a 0 ↔ w = a := by
  rw [mem_lay]
  constructor
  · rintro ⟨-, h⟩
    exact ((SimpleGraph.edist_eq_zero_iff (G := H)).1 (by simpa using h)).symm
  · rintro rfl
    refine ⟨?_, by simp⟩
    simpa using SimpleGraph.edist_eq_one_iff_adj.2 hza

/-- P1: every vertex of layer `i+1` has a neighbour in layer `i` -/
lemma par_ex {z a w : V} {i : ℕ} (hza : H.Adj z a) (hw : w ∈ lay H z a (i + 1)) :
    ∃ y, H.Adj w y ∧ y ∈ lay H z a i := by
  rw [mem_lay] at hw
  obtain ⟨hzw, haw⟩ := hw
  have haw' := haw
  rw [SimpleGraph.edist_comm] at haw'
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe haw'
  cases p with
  | nil => simp at hp
  | cons h q =>
    rename_i y
    refine ⟨y, h, ?_⟩
    simp only [SimpleGraph.Walk.length_cons, add_left_inj] at hp
    obtain ⟨j, hj, hj1, hj2⟩ := adj_lvl H h haw
    have hle : H.edist a y ≤ q.length := by
      rw [SimpleGraph.edist_comm]; exact SimpleGraph.edist_le q
    rw [hj, hp] at hle
    have hji : j ≤ i := by exact_mod_cast hle
    obtain ⟨j', hj', hj'1, hj'2⟩ := adj_lvl H h hzw
    have hza1 : H.edist z a = ((1 : ℕ) : ℕ∞) := by simpa using SimpleGraph.edist_eq_one_iff_adj.2 hza
    have := tri_le H hza1 hj hj'
    rw [mem_lay]
    refine ⟨?_, ?_⟩
    · rw [hj']; congr 1; omega
    · rw [hj]; congr 1; omega

/-- P3: higher neighbours of layer `i` lie in layer `i+1` -/
lemma child_mem {z a w c : V} {i : ℕ} (hza : H.Adj z a) (hw : w ∈ lay H z a i) (h : H.Adj w c)
    (hc : H.edist z c = ((i + 2 : ℕ) : ℕ∞)) : c ∈ lay H z a (i + 1) := by
  rw [mem_lay] at hw ⊢
  obtain ⟨j, hj, hj1, hj2⟩ := adj_lvl H h hw.2
  have hza1 : H.edist z a = ((1 : ℕ) : ℕ∞) := by simpa using SimpleGraph.edist_eq_one_iff_adj.2 hza
  have := tri_le H hza1 hj hc
  refine ⟨hc, ?_⟩
  rw [hj]; congr 1; omega

variable {R : ℕ}

/-- P2: a lower neighbour of layer `i+1` is in layer `i` -/
lemma low_mem {z a w y : V} {i : ℕ} (hT : NoCycleOn H (ball H z R)) (hR : i + 2 ≤ R)
    (hza : H.Adj z a) (hw : w ∈ lay H z a (i + 1)) (h : H.Adj w y)
    (hy : H.edist z y = ((i + 1 : ℕ) : ℕ∞)) : y ∈ lay H z a i := by
  obtain ⟨y', hy', hy'm⟩ := par_ex H hza hw
  have e := F2 H (k := i + 1) hT hR ((mem_lay H).1 hw).1 h hy' hy ((mem_lay H).1 hy'm).1
  rw [e]; exact hy'm

/-- P4: neighbours of layer `i` are one level down or one level up -/
lemma nbr_lvl {z a w y : V} {i : ℕ} (hT : NoCycleOn H (ball H z R)) (hR : i + 2 ≤ R)
    (hw : w ∈ lay H z a i) (h : H.Adj w y) :
    H.edist z y = (i : ℕ∞) ∨ H.edist z y = ((i + 2 : ℕ) : ℕ∞) := by
  obtain ⟨j, hj, hj1, hj2⟩ := adj_lvl H h ((mem_lay H).1 hw).1
  rcases (by omega : j = i ∨ j = i + 1 ∨ j = i + 2) with e | e | e
  · left; rw [hj, e]
  · exfalso
    exact F1 H (k := i + 1) hT hR h ((mem_lay H).1 hw).1 (by rw [hj, e])
  · right; rw [hj, e]

/-- P5: unique parent of a vertex of layer `i+1` within layer `i` -/
lemma par_uniq {z a c w w' : V} {i : ℕ} (hT : NoCycleOn H (ball H z R)) (hR : i + 2 ≤ R)
    (hc : c ∈ lay H z a (i + 1)) (hw : w ∈ lay H z a i) (hw' : w' ∈ lay H z a i)
    (h : H.Adj c w) (h' : H.Adj c w') : w = w' :=
  F2 H (k := i + 1) hT hR ((mem_lay H).1 hc).1 h h' ((mem_lay H).1 hw).1 ((mem_lay H).1 hw').1

/-- layers of two different neighbours of `z` are disjoint -/
lemma lay_disj {z a a' w : V} (hT : NoCycleOn H (ball H z R)) (hza : H.Adj z a)
    (hza' : H.Adj z a') : ∀ i : ℕ, i + 1 ≤ R → w ∈ lay H z a i → w ∈ lay H z a' i → a = a' := by
  intro i
  induction i generalizing w with
  | zero =>
    intro _ h1 h2
    rw [lay_zero H hza] at h1; rw [lay_zero H hza'] at h2
    rw [← h1, ← h2]
  | succ i ih =>
    intro hR h1 h2
    obtain ⟨y, hy, hym⟩ := par_ex H hza h1
    have hym' := low_mem H hT hR hza' h2 hy ((mem_lay H).1 hym).1
    exact ih (by omega) hym hym'

end layers

section analytic

lemma mink1 {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    √(∑ i ∈ s, (x i + y i) ^ 2) ≤ √(∑ i ∈ s, x i ^ 2) + √(∑ i ∈ s, y i ^ 2) := by
  have hx : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hy : 0 ≤ ∑ i ∈ s, y i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s x y
  have e : ∑ i ∈ s, (x i + y i) ^ 2 = ∑ i ∈ s, x i ^ 2 + 2 * ∑ i ∈ s, x i * y i + ∑ i ∈ s, y i ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc √(∑ i ∈ s, (x i + y i) ^ 2) ≤ √((√(∑ i ∈ s, x i ^ 2) + √(∑ i ∈ s, y i ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [e, add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
        nlinarith [hcs]
    _ = √(∑ i ∈ s, x i ^ 2) + √(∑ i ∈ s, y i ^ 2) := Real.sqrt_sq (by positivity)

lemma mink2 {V : Type*} (A B : Finset V) (s1 p1 s2 p2 : V → ℝ) :
    √(∑ w ∈ A, (s1 w + p1 w) ^ 2 + ∑ w ∈ B, (s2 w + p2 w) ^ 2) ≤
      √(∑ w ∈ A, s1 w ^ 2 + ∑ w ∈ B, s2 w ^ 2) + √(∑ w ∈ A, p1 w ^ 2 + ∑ w ∈ B, p2 w ^ 2) := by
  have := mink1 (A.disjSum B) (Sum.elim s1 s2) (Sum.elim p1 p2)
  simpa [Finset.sum_disjSum] using this

lemma mono_core (X : ℕ → ℝ) (q μa : ℝ) (r : ℕ) (hq : 1 ≤ q) (hμ : 2 * q ≤ μa)
    (hX : ∀ i, 0 ≤ X i)
    (h0 : 1 ≤ r - 1 → μa * X 0 ≤ q * X 1 + X 0)
    (hs : ∀ i, i + 2 ≤ r - 1 → μa * X (i + 1) ≤ q * X (i + 2) + q * X i) :
    ∀ i, i ≤ r - 1 → X 0 ≤ X i := by
  have step : ∀ i, i + 1 ≤ r - 1 → X i ≤ X (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h
      have h1 := h0 h
      have h2 : q * X 0 ≤ q * X 1 := by nlinarith [mul_le_mul_of_nonneg_right hμ (hX 0), hX 0]
      exact le_of_mul_le_mul_left h2 (by linarith)
    | succ i ih =>
      intro h
      have h1 := ih (by omega)
      have h3 := hs i h
      have h2 : q * X (i + 1) ≤ q * X (i + 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hμ (hX (i + 1)),
          mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ q)]
      exact le_of_mul_le_mul_left h2 (by linarith)
  intro i
  induction i with
  | zero => intro _; exact le_refl _
  | succ i ih => intro h; exact (ih (by omega)).trans (step i h)

end analytic

section side
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

noncomputable def ch (z w : V) : Finset V :=
  (H.neighborFinset w).filter (fun c => H.edist z c = H.edist z w + 1)

noncomputable def pa (z w : V) : Finset V :=
  (H.neighborFinset w).filter (fun c => ¬ H.edist z c = H.edist z w + 1)

lemma ch_lvl {z a w c : V} {i : ℕ} (hw : w ∈ lay H z a i) (hc : c ∈ ch H z w) :
    H.Adj w c ∧ H.edist z c = ((i + 2 : ℕ) : ℕ∞) := by
  rw [ch, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hc
  refine ⟨hc.1, ?_⟩
  rw [hc.2, ((mem_lay H).1 hw).1]; push_cast; ring

lemma ch_card {d : ℕ} (hreg : H.IsRegularOfDegree d) {z a w : V} {i : ℕ} (hza : H.Adj z a)
    (hw : w ∈ lay H z a i) : (ch H z w).card ≤ d - 1 := by
  have hlt : (ch H z w).card < (H.neighborFinset w).card := by
    apply Finset.card_lt_card
    rw [ch, Finset.filter_ssubset]
    cases i with
    | zero =>
      rw [lay_zero H hza] at hw; subst hw
      refine ⟨z, by simpa using hza.symm, ?_⟩
      rw [SimpleGraph.edist_self, SimpleGraph.edist_eq_one_iff_adj.2 hza]; norm_num
    | succ i =>
      obtain ⟨y, hy, hym⟩ := par_ex H hza hw
      refine ⟨y, by simpa using hy, ?_⟩
      rw [((mem_lay H).1 hym).1, ((mem_lay H).1 hw).1]
      intro h
      have : i + 1 = i + 1 + 1 + 1 := by exact_mod_cast h
      omega
  rw [SimpleGraph.card_neighborFinset_eq_degree, hreg w] at hlt
  omega

lemma ch_card_real {d : ℕ} (hd : 1 ≤ d) (hreg : H.IsRegularOfDegree d) {z a w : V} {i : ℕ}
    (hza : H.Adj z a) (hw : w ∈ lay H z a i) : ((ch H z w).card : ℝ) ≤ (d : ℝ) - 1 := by
  have h1 := ch_card H hreg hza hw
  have h2 : ((ch H z w).card : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast h1
  rwa [Nat.cast_sub hd, Nat.cast_one] at h2

variable {R : ℕ}

lemma S_bound {d : ℕ} (hd : 1 ≤ d) (hreg : H.IsRegularOfDegree d) {z a : V}
    (hT : NoCycleOn H (ball H z R)) (hza : H.Adj z a) (g : V → ℝ) {i : ℕ} (hR : i + 2 ≤ R) :
    ∑ w ∈ lay H z a i, (∑ c ∈ ch H z w, g c) ^ 2 ≤
      ((d : ℝ) - 1) * ∑ w ∈ lay H z a (i + 1), g w ^ 2 := by
  have hdisj : ((lay H z a i : Finset V) : Set V).PairwiseDisjoint (ch H z) := by
    intro w hw w' hw' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨h1, h2⟩ := ch_lvl H hw hc
    obtain ⟨h1', -⟩ := ch_lvl H hw' hc'
    have hcm := child_mem H hza hw h1 h2
    exact hne (par_uniq H hT hR hcm hw hw' h1.symm h1'.symm)
  have hsub : (lay H z a i).biUnion (ch H z) ⊆ lay H z a (i + 1) := by
    intro c hc
    rw [Finset.mem_biUnion] at hc
    obtain ⟨w, hw, hc⟩ := hc
    obtain ⟨h1, h2⟩ := ch_lvl H hw hc
    exact child_mem H hza hw h1 h2
  calc ∑ w ∈ lay H z a i, (∑ c ∈ ch H z w, g c) ^ 2
      ≤ ∑ w ∈ lay H z a i, ((ch H z w).card : ℝ) * ∑ c ∈ ch H z w, g c ^ 2 :=
        Finset.sum_le_sum (fun w _ => sq_sum_le_card_mul_sum_sq)
    _ ≤ ∑ w ∈ lay H z a i, ((d : ℝ) - 1) * ∑ c ∈ ch H z w, g c ^ 2 :=
        Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_right (ch_card_real H hd hreg hza hw)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = ((d : ℝ) - 1) * ∑ c ∈ (lay H z a i).biUnion (ch H z), g c ^ 2 := by
        rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    _ ≤ ((d : ℝ) - 1) * ∑ w ∈ lay H z a (i + 1), g w ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
        · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith

lemma pa_lvl {z a w y : V} {j : ℕ} (hT : NoCycleOn H (ball H z R)) (hR : j + 3 ≤ R)
    (hza : H.Adj z a) (hw : w ∈ lay H z a (j + 1)) (hy : y ∈ pa H z w) :
    H.Adj w y ∧ y ∈ lay H z a j := by
  rw [pa, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
  refine ⟨hy.1, ?_⟩
  rcases nbr_lvl H hT (by omega) hw hy.1 with e | e
  · exact low_mem H hT (by omega) hza hw hy.1 e
  · exfalso; apply hy.2
    rw [e, ((mem_lay H).1 hw).1]; push_cast; ring

lemma P_bound {d : ℕ} (hd : 1 ≤ d) (hreg : H.IsRegularOfDegree d) {z a : V}
    (hT : NoCycleOn H (ball H z R)) (hza : H.Adj z a) (g : V → ℝ) {j : ℕ} (hR : j + 3 ≤ R) :
    ∑ w ∈ lay H z a (j + 1), (∑ y ∈ pa H z w, g y) ^ 2 ≤
      ((d : ℝ) - 1) * ∑ w ∈ lay H z a j, g w ^ 2 := by
  have hcard : ∀ w ∈ lay H z a (j + 1), (pa H z w).card ≤ 1 := by
    intro w hw
    rw [Finset.card_le_one]
    intro y hy y' hy'
    obtain ⟨h1, h2⟩ := pa_lvl H hT hR hza hw hy
    obtain ⟨h1', h2'⟩ := pa_lvl H hT hR hza hw hy'
    exact par_uniq H hT (by omega) hw h2 h2' h1 h1'
  have hcomm : ∑ w ∈ lay H z a (j + 1), ∑ y ∈ pa H z w, g y ^ 2 =
      ∑ y ∈ lay H z a j, ∑ w ∈ (lay H z a (j + 1)).filter (fun w => y ∈ pa H z w), g y ^ 2 := by
    apply Finset.sum_comm'
    intro w y
    constructor
    · rintro ⟨hw, hy⟩
      exact ⟨Finset.mem_filter.2 ⟨hw, hy⟩, (pa_lvl H hT hR hza hw hy).2⟩
    · rintro ⟨hw, -⟩
      exact Finset.mem_filter.1 hw
  have hsub : ∀ y ∈ lay H z a j,
      (lay H z a (j + 1)).filter (fun w => y ∈ pa H z w) ⊆ ch H z y := by
    intro y hy w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨h1, -⟩ := pa_lvl H hT hR hza hw.1 hw.2
    rw [ch, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    refine ⟨h1.symm, ?_⟩
    rw [((mem_lay H).1 hw.1).1, ((mem_lay H).1 hy).1]; push_cast; ring
  calc ∑ w ∈ lay H z a (j + 1), (∑ y ∈ pa H z w, g y) ^ 2
      ≤ ∑ w ∈ lay H z a (j + 1), ∑ y ∈ pa H z w, g y ^ 2 := by
        apply Finset.sum_le_sum
        intro w hw
        have h1 := sq_sum_le_card_mul_sum_sq (s := pa H z w) (f := g)
        have h2 : ((pa H z w).card : ℝ) ≤ 1 := by exact_mod_cast hcard w hw
        have h3 : 0 ≤ ∑ y ∈ pa H z w, g y ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        nlinarith
    _ = ∑ y ∈ lay H z a j, ∑ w ∈ (lay H z a (j + 1)).filter (fun w => y ∈ pa H z w), g y ^ 2 :=
        hcomm
    _ ≤ ∑ y ∈ lay H z a j, ((d : ℝ) - 1) * g y ^ 2 := by
        apply Finset.sum_le_sum
        intro y hy
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have h1 : (((lay H z a (j + 1)).filter (fun w => y ∈ pa H z w)).card : ℝ) ≤
            (ch H z y).card := by exact_mod_cast Finset.card_le_card (hsub y hy)
        exact h1.trans (ch_card_real H hd hreg hza hy)
    _ = ((d : ℝ) - 1) * ∑ w ∈ lay H z a j, g w ^ 2 := by rw [Finset.mul_sum]

end side

section pairsec

lemma pair {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {d r : ℕ} (hd : 3 ≤ d) (hreg : H.IsRegularOfDegree d) (g : V → ℝ) (μ : ℝ)
    (hμ : 2 * Real.sqrt ((d : ℝ) - 1) ≤ |μ|)
    {z a z' b : V} (hza : H.Adj z a) (hzb : H.Adj z' b)
    (hT : NoCycleOn H (ball H z (r + 1))) (hT' : NoCycleOn H (ball H z' (r + 1)))
    (hPa : μ * g a - ∑ c ∈ ch H z a, g c = g b) (hPb : μ * g b - ∑ c ∈ ch H z' b, g c = g a)
    (hPA : ∀ j, j + 2 ≤ r → ∀ w ∈ lay H z a (j + 1),
      μ * g w - ∑ c ∈ ch H z w, g c = ∑ y ∈ pa H z w, g y)
    (hPB : ∀ j, j + 2 ≤ r → ∀ w ∈ lay H z' b (j + 1),
      μ * g w - ∑ c ∈ ch H z' w, g c = ∑ y ∈ pa H z' w, g y) :
    (r : ℝ) * (g a ^ 2 + g b ^ 2) ≤
      ∑ i ∈ Finset.range r, (∑ w ∈ lay H z a i, g w ^ 2 + ∑ w ∈ lay H z' b i, g w ^ 2) := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = √((d : ℝ) - 1) := ⟨_, rfl⟩
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.2 (by linarith)
  rw [← hq] at hμ
  obtain ⟨T, hTd⟩ : ∃ T : ℕ → ℝ,
      T = fun i => ∑ w ∈ lay H z a i, g w ^ 2 + ∑ w ∈ lay H z' b i, g w ^ 2 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ, X = fun i => √(T i) := ⟨_, rfl⟩
  have hTnn : ∀ i, 0 ≤ T i := by
    intro i; rw [hTd]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hXnn : ∀ i, 0 ≤ X i := by intro i; rw [hX]; exact Real.sqrt_nonneg _
  have hlay0 : lay H z a 0 = {a} := by ext w; rw [lay_zero H hza, Finset.mem_singleton]
  have hlay0' : lay H z' b 0 = {b} := by ext w; rw [lay_zero H hzb, Finset.mem_singleton]
  have hT0 : T 0 = g a ^ 2 + g b ^ 2 := by rw [hTd]; simp [hlay0, hlay0']
  have e2 : ∀ x w : V, (∑ c ∈ ch H x w, g c) + (μ * g w - ∑ c ∈ ch H x w, g c) = μ * g w :=
    fun _ _ => by ring
  have hrec : ∀ i, i + 2 ≤ r → |μ| * X i ≤ q * X (i + 1) +
      √(∑ w ∈ lay H z a i, (μ * g w - ∑ c ∈ ch H z w, g c) ^ 2 +
        ∑ w ∈ lay H z' b i, (μ * g w - ∑ c ∈ ch H z' w, g c) ^ 2) := by
    intro i hi
    have hm := mink2 (lay H z a i) (lay H z' b i) (fun w => ∑ c ∈ ch H z w, g c)
      (fun w => μ * g w - ∑ c ∈ ch H z w, g c) (fun w => ∑ c ∈ ch H z' w, g c)
      (fun w => μ * g w - ∑ c ∈ ch H z' w, g c)
    simp only [e2] at hm
    have e : |μ| * X i =
        √(∑ w ∈ lay H z a i, (μ * g w) ^ 2 + ∑ w ∈ lay H z' b i, (μ * g w) ^ 2) := by
      rw [show ∑ w ∈ lay H z a i, (μ * g w) ^ 2 + ∑ w ∈ lay H z' b i, (μ * g w) ^ 2
          = μ ^ 2 * T i by rw [hTd]; simp only [mul_pow, ← Finset.mul_sum]; ring]
      rw [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq_eq_abs, hX]
    have hS : √(∑ w ∈ lay H z a i, (∑ c ∈ ch H z w, g c) ^ 2 +
        ∑ w ∈ lay H z' b i, (∑ c ∈ ch H z' w, g c) ^ 2) ≤ q * X (i + 1) := by
      have h1 := S_bound H (by omega) hreg hT hza g (i := i) (by omega)
      have h2 := S_bound H (by omega) hreg hT' hzb g (i := i) (by omega)
      rw [hX, hq]
      simp only
      rw [← Real.sqrt_mul (by linarith)]
      apply Real.sqrt_le_sqrt
      rw [hTd]; simp only; rw [mul_add]; linarith
    rw [e]; linarith [hm, hS]
  have hY0 : √(∑ w ∈ lay H z a 0, (μ * g w - ∑ c ∈ ch H z w, g c) ^ 2 +
      ∑ w ∈ lay H z' b 0, (μ * g w - ∑ c ∈ ch H z' w, g c) ^ 2) = X 0 := by
    rw [hlay0, hlay0', Finset.sum_singleton, Finset.sum_singleton, hPa, hPb, hX]
    simp only; rw [hT0, add_comm]
  have hY : ∀ j, j + 3 ≤ r → √(∑ w ∈ lay H z a (j + 1), (μ * g w - ∑ c ∈ ch H z w, g c) ^ 2 +
      ∑ w ∈ lay H z' b (j + 1), (μ * g w - ∑ c ∈ ch H z' w, g c) ^ 2) ≤ q * X j := by
    intro j hj
    have eA : ∑ w ∈ lay H z a (j + 1), (μ * g w - ∑ c ∈ ch H z w, g c) ^ 2 =
        ∑ w ∈ lay H z a (j + 1), (∑ y ∈ pa H z w, g y) ^ 2 :=
      Finset.sum_congr rfl (fun w hw => by rw [hPA j (by omega) w hw])
    have eB : ∑ w ∈ lay H z' b (j + 1), (μ * g w - ∑ c ∈ ch H z' w, g c) ^ 2 =
        ∑ w ∈ lay H z' b (j + 1), (∑ y ∈ pa H z' w, g y) ^ 2 :=
      Finset.sum_congr rfl (fun w hw => by rw [hPB j (by omega) w hw])
    rw [eA, eB]
    have h1 := P_bound H (by omega) hreg hT hza g (j := j) (by omega)
    have h2 := P_bound H (by omega) hreg hT' hzb g (j := j) (by omega)
    rw [hX, hq]
    simp only
    rw [← Real.sqrt_mul (by linarith)]
    apply Real.sqrt_le_sqrt
    rw [hTd]; simp only; rw [mul_add]; linarith
  have hmono := mono_core X q |μ| r hq1 hμ hXnn
    (fun h => by have := hrec 0 (by omega); rw [hY0] at this; linarith)
    (fun i hi => by
      have h1 := hrec (i + 1) (by omega)
      have h2 := hY i (by omega)
      linarith)
  have hTmono : ∀ i ∈ Finset.range r, T 0 ≤ T i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h := hmono i (by omega)
    rw [hX] at h
    exact (Real.sqrt_le_sqrt_iff (hTnn i)).1 h
  have key : ∑ i ∈ Finset.range r, T 0 ≤ ∑ i ∈ Finset.range r, T i := Finset.sum_le_sum hTmono
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hT0] at key
  rw [hTd] at key
  exact key

end pairsec

section mainsec
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma ch_pa_split (H : SimpleGraph V) [DecidableRel H.Adj] (g : V → ℝ) (z w : V) :
    ∑ y ∈ H.neighborFinset w, g y = ∑ c ∈ ch H z w, g c + ∑ y ∈ pa H z w, g y := by
  unfold ch pa
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma main_V (H : SimpleGraph V) [DecidableRel H.Adj] (d r : ℕ) (hd : 3 ≤ d)
    (hreg : H.IsRegularOfDegree d) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m)
    (g : V → ℝ) (hgU : ∀ v ∈ U, g v = 0) (μ : ℝ) (hμ : 2 * Real.sqrt ((d : ℝ) - 1) ≤ |μ|)
    (hE : ∀ w, w ∉ U → μ * g w =
      ∑ y ∈ H.neighborFinset w, g y + (if w ∈ nbrSet H U then g (m w) else 0)) :
    (r : ℝ) * ∑ v ∈ nbrSet H U, g v ^ 2 ≤ ∑ v, g v ^ 2 := by
  have memN : ∀ x, x ∈ nbrSet H U ↔ ∃ z ∈ U, H.Adj z x := by
    intro x; simp [nbrSet]
  have far : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ∀ (w : V) (k k' : ℕ), H.edist z w = k →
      H.edist z' w = k' → k + k' < 2 * r + 3 → False := by
    intro z hz z' hz' hne w k k' hk hk' hlt
    have h1 := H.edist_triangle (u := z) (v := w) (w := z')
    rw [hk, SimpleGraph.edist_comm (u := w) (v := z'), hk'] at h1
    have h2 := (hU3 z hz z' hz' hne).trans h1
    have : 2 * r + 3 ≤ k + k' := by exact_mod_cast h2
    omega
  have notU : ∀ z ∈ U, ∀ (w : V) (k : ℕ), H.edist z w = k → 1 ≤ k → k ≤ 2 * r + 2 → w ∉ U := by
    intro z hz w k hk h1 h2 hw
    have hne : z ≠ w := by
      rintro rfl; rw [SimpleGraph.edist_self] at hk
      have : k = 0 := by exact_mod_cast hk.symm
      omega
    have := hU3 z hz w hw hne
    rw [hk] at this
    have : 2 * r + 3 ≤ k := by exact_mod_cast this
    omega
  have notN : ∀ z ∈ U, ∀ (w : V) (k : ℕ), H.edist z w = k → 2 ≤ k → k ≤ 2 * r + 1 →
      w ∉ nbrSet H U := by
    intro z hz w k hk h1 h2 hw
    obtain ⟨z', hz', hzw⟩ := (memN w).1 hw
    by_cases hzz : z = z'
    · subst hzz
      rw [SimpleGraph.edist_eq_one_iff_adj.2 hzw] at hk
      have : k = 1 := by exact_mod_cast hk.symm
      omega
    · exact far z hz z' hz' hzz w k 1 hk (by simpa using SimpleGraph.edist_eq_one_iff_adj.2 hzw)
        (by omega)
  have hzex : ∀ a : V, ∃ z : V, a ∈ nbrSet H U → (z ∈ U ∧ H.Adj z a) := by
    intro a
    by_cases ha : a ∈ nbrSet H U
    · obtain ⟨z, hz, hza⟩ := (memN a).1 ha
      exact ⟨z, fun _ => ⟨hz, hza⟩⟩
    · exact ⟨a, fun h => absurd h ha⟩
  choose zf hzf using hzex
  -- the partner equation at a matched vertex
  have hP0 : ∀ a ∈ nbrSet H U, μ * g a - ∑ c ∈ ch H (zf a) a, g c = g (m a) := by
    intro a ha
    obtain ⟨hz, hza⟩ := hzf a ha
    have h1 : H.edist (zf a) a = ((1 : ℕ) : ℕ∞) := by
      simpa using SimpleGraph.edist_eq_one_iff_adj.2 hza
    have haU := notU _ hz a 1 h1 le_rfl (by omega)
    have hE' := hE a haU
    rw [if_pos ha, ch_pa_split H g (zf a) a] at hE'
    have hpa : ∑ y ∈ pa H (zf a) a, g y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hal : a ∈ lay H (zf a) a 0 := (lay_zero H hza).2 rfl
      rw [pa, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
      rcases nbr_lvl H (hU2 _ hz) (by omega) hal hy.1 with e | e
      · have : y = zf a := ((SimpleGraph.edist_eq_zero_iff (G := H)).1 (by simpa using e)).symm
        rw [this]; exact hgU _ hz
      · exfalso; apply hy.2
        rw [e, h1]; norm_num
    rw [hpa] at hE'
    linarith
  have hPj : ∀ a ∈ nbrSet H U, ∀ j, j + 2 ≤ r → ∀ w ∈ lay H (zf a) a (j + 1),
      μ * g w - ∑ c ∈ ch H (zf a) w, g c = ∑ y ∈ pa H (zf a) w, g y := by
    intro a ha j hj w hw
    obtain ⟨hz, hza⟩ := hzf a ha
    have hl := ((mem_lay H).1 hw).1
    have hwU := notU _ hz w (j + 1 + 1) hl (by omega) (by omega)
    have hwN := notN _ hz w (j + 1 + 1) hl (by omega) (by omega)
    have hE' := hE w hwU
    rw [if_neg hwN, ch_pa_split H g (zf a) w] at hE'
    linarith
  -- W a = mass of the layers of a
  obtain ⟨W, hW⟩ : ∃ W : V → ℝ,
      W = fun a => ∑ i ∈ Finset.range r, ∑ w ∈ lay H (zf a) a i, g w ^ 2 := ⟨_, rfl⟩
  have hpair : ∀ a ∈ nbrSet H U, (r : ℝ) * (g a ^ 2 + g (m a) ^ 2) ≤ W a + W (m a) := by
    intro a ha
    obtain ⟨hz, hza⟩ := hzf a ha
    have hma := (hm a ha).1
    obtain ⟨hz', hzb⟩ := hzf (m a) hma
    have h := pair H hd hreg g μ hμ hza hzb (hU2 _ hz) (hU2 _ hz') (hP0 a ha)
      (by rw [hP0 (m a) hma, (hm a ha).2.1]) (hPj a ha) (hPj (m a) hma)
    rw [Finset.sum_add_distrib] at h
    rw [hW]; exact h
  have hsum := Finset.sum_le_sum hpair
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hswap : ∀ φ : V → ℝ, ∑ a ∈ nbrSet H U, φ (m a) = ∑ a ∈ nbrSet H U, φ a := by
    intro φ
    exact Finset.sum_nbij' m m (fun a ha => (hm a ha).1) (fun a ha => (hm a ha).1)
      (fun a ha => (hm a ha).2.1) (fun a ha => (hm a ha).2.1) (fun a _ => rfl)
  rw [hswap (fun v => g v ^ 2), hswap W] at hsum
  -- the layers are disjoint
  have hWle : ∑ a ∈ nbrSet H U, W a ≤ ∑ v, g v ^ 2 := by
    have hdisj : ((nbrSet H U ×ˢ Finset.range r : Finset (V × ℕ)) : Set (V × ℕ)).PairwiseDisjoint
        (fun p => lay H (zf p.1) p.1 p.2) := by
      rintro ⟨a, i⟩ hp ⟨a', i'⟩ hp' hne
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_range,
        Set.mem_Iio] at hp hp'
      rw [Function.onFun, Finset.disjoint_left]
      intro w hw hw'
      obtain ⟨hz, hza⟩ := hzf a hp.1
      obtain ⟨hz', hza'⟩ := hzf a' hp'.1
      have e1 := ((mem_lay H).1 hw).1
      have e2 := ((mem_lay H).1 hw').1
      by_cases hzz : zf a = zf a'
      · rw [hzz] at e1 hw
        have hii : i = i' := by
          rw [e1] at e2
          have : i + 1 = i' + 1 := by exact_mod_cast e2
          omega
        subst hii
        rw [hzz] at hza
        have haa := lay_disj H (hU2 _ hz') hza hza' i (by omega) hw hw'
        exact hne (by rw [haa])
      · exact far _ hz _ hz' hzz w (i + 1) (i' + 1) e1 e2 (by omega)
    rw [hW]
    simp only
    rw [← Finset.sum_product' (f := fun a i => ∑ w ∈ lay H (zf a) a i, g w ^ 2)]
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  linarith

end mainsec

end P2MEq11

namespace P2MEq11CR

open ExplicitExpanders.Delete

lemma edist_cast_lt {V : Type*} (H : SimpleGraph V) {a b : V} {r k : ℕ} (hk : k < 2 * r + 3)
    (h : ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist a b) (p : H.Walk a b) (hp : p.length = k) : False := by
  have h1 := SimpleGraph.edist_le p
  rw [hp] at h1
  have := h.trans h1
  exact absurd (by exact_mod_cast this) (not_le.mpr hk)

/-- two `U`-vertices sharing a neighbour coincide -/
lemma uniq_nbr {V : Type*} (H : SimpleGraph V) (r : ℕ) (U : Finset V)
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    {z z' x : V} (hz : z ∈ U) (hz' : z' ∈ U) (h1 : H.Adj z x) (h2 : H.Adj z' x) : z = z' := by
  by_contra hne
  exact edist_cast_lt H (k := 2) (by omega) (hU3 z hz z' hz' hne)
    (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil)) rfl

/-- a neighbour of a `U`-vertex is not in `U` -/
lemma nbr_not_mem {V : Type*} (H : SimpleGraph V) (r : ℕ) (U : Finset V)
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    {z x : V} (hz : z ∈ U) (h1 : H.Adj z x) : x ∉ U := by
  intro hx
  exact edist_cast_lt H (k := 1) (by omega) (hU3 z hz x hx h1.ne)
    (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil) rfl

/-- matched vertices are not adjacent in `H` -/
lemma match_not_adj {V : Type*} (H : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r) (U : Finset V)
    (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    {z z' x y : V} (hz : z ∈ U) (hz' : z' ∈ U) (h1 : H.Adj z x) (h2 : H.Adj z' y) (hxy : x ≠ y) :
    ¬ H.Adj x y := by
  intro hadj
  by_cases hzz : z = z'
  · subst hzz
    have hb : ∀ w, H.Adj z w → w ∈ ball H z (r + 1) := by
      intro w hw
      show H.edist z w ≤ ((r + 1 : ℕ) : ℕ∞)
      have := SimpleGraph.edist_le (SimpleGraph.Walk.cons hw SimpleGraph.Walk.nil)
      refine this.trans ?_
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      exact_mod_cast (by omega : 0 + 1 ≤ r + 1)
    have hz0 : z ∈ ball H z (r + 1) := by
      show H.edist z z ≤ ((r + 1 : ℕ) : ℕ∞)
      simp
    have e1 : (H.induce (ball H z (r + 1))).Adj ⟨z, hz0⟩ ⟨x, hb x h1⟩ := by simpa using h1
    have e2 : (H.induce (ball H z (r + 1))).Adj ⟨x, hb x h1⟩ ⟨y, hb y h2⟩ := by simpa using hadj
    have e3 : (H.induce (ball H z (r + 1))).Adj ⟨y, hb y h2⟩ ⟨z, hz0⟩ := by simpa using h2.symm
    apply hU2 z hz (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2
      (SimpleGraph.Walk.cons e3 SimpleGraph.Walk.nil)))
    have hzx : z ≠ x := h1.ne
    have hzy : z ≠ y := h2.ne
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, hxy, hzy.symm, hzx.symm]
    · simp [SimpleGraph.Walk.edges_cons, hxy, hzx, hzy]
  · exact edist_cast_lt H (k := 3) (by omega) (hU3 z hz z' hz' hzz)
      (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons hadj
        (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil))) rfl

end P2MEq11CR

open Classical ExplicitExpanders.Delete Matrix in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (d r : ℕ) (hd : 3 ≤ d) (hreg : H.IsRegularOfDegree d) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m)
    (f : Kept U → ℝ) (μ : ℝ) (heig : (deleteAndMatch H U m).adjMatrix ℝ *ᵥ f = μ • f)
    (hμ : 2 * Real.sqrt ((d : ℝ) - 1) ≤ |μ|) :
    ∑ x, ((matchGraph H U m).degree x : ℝ) * f x ^ 2 ≤ (1 / (r : ℝ)) * ∑ x, f x ^ 2 := by
  obtain rfl : ‹DecidableRel H.Adj› = (fun a b => Classical.propDecidable (H.Adj a b)) :=
    Subsingleton.elim _ _
  classical
  have memN : ∀ x, x ∈ nbrSet H U ↔ ∃ z ∈ U, H.Adj z x := by
    intro x; simp [nbrSet]
  have hMadj : ∀ v w : Kept U, (matchGraph H U m).Adj v w ↔ (v.1 ∈ nbrSet H U ∧ w.1 = m v.1) := by
    intro v w
    simp only [matchGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, h | ⟨hw, hv⟩⟩
      · exact h
      · refine ⟨?_, ?_⟩
        · rw [hv]; exact (hm w.1 hw).1
        · rw [hv, (hm w.1 hw).2.1]
    · rintro ⟨hv, hw⟩
      refine ⟨?_, Or.inl ⟨hv, hw⟩⟩
      intro hvw
      apply (hm v.1 hv).2.2
      rw [← hw, hvw]
  have hmU : ∀ x ∈ nbrSet H U, x ∉ U := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := (memN x).1 hx
    exact P2MEq11CR.nbr_not_mem H r U hU3 hz hzx
  obtain ⟨g, hg⟩ : ∃ g : V → ℝ, g = fun v => if h : v ∈ U then 0 else f ⟨v, h⟩ := ⟨_, rfl⟩
  have hgK : ∀ x : Kept U, g x.1 = f x := by
    intro x; rw [hg]; simp only; rw [dif_neg x.2]
  have hgU : ∀ v ∈ U, g v = 0 := by
    intro v hv; rw [hg]; simp only; rw [dif_pos hv]
  have hconv : ∀ φ : V → ℝ, (∀ v ∈ U, φ v = 0) → ∑ x : Kept U, φ x.1 = ∑ v, φ v := by
    intro φ hφ
    rw [← Finset.sum_subtype (Finset.univ.filter (fun v => v ∉ U)) (p := fun v => v ∉ U)
      (by simp) φ]
    apply Finset.sum_filter_of_ne
    intro v _ hv hU; exact hv (hφ v hU)
  have hEk : ∀ v : Kept U, μ * g v.1 = ∑ y ∈ H.neighborFinset v.1, g y +
      (if v.1 ∈ nbrSet H U then g (m v.1) else 0) := by
    intro v
    set T : Finset V := ((H.neighborFinset v.1).filter (fun w => w ∉ U)) ∪
      (if v.1 ∈ nbrSet H U then {m v.1} else ∅) with hT
    have hmap : ((deleteAndMatch H U m).neighborFinset v).map
        (Function.Embedding.subtype _) = T := by
      ext w
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype,
        hT, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨w', hw', rfl⟩
        rcases hw' with h | h
        · exact Or.inl ⟨h, w'.2⟩
        · rw [hMadj] at h
          right; rw [if_pos h.1]; simp [h.2]
      · rintro (⟨h, hwU⟩ | h)
        · exact ⟨⟨w, hwU⟩, Or.inl h, rfl⟩
        · by_cases hv : v.1 ∈ nbrSet H U
          · rw [if_pos hv, Finset.mem_singleton] at h
            subst h
            have hmN := (hm v.1 hv).1
            have hmU : m v.1 ∉ U := by
              obtain ⟨z, hz, hzm⟩ := (memN _).1 hmN
              exact P2MEq11CR.nbr_not_mem H r U hU3 hz hzm
            exact ⟨⟨m v.1, hmU⟩, Or.inr ((hMadj _ _).2 ⟨hv, rfl⟩), rfl⟩
          · rw [if_neg hv] at h; simp at h
    have h1 := congrFun heig v
    rw [Pi.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_mulVec_apply, ← hgK v] at h1
    have h2 : ∑ y ∈ (deleteAndMatch H U m).neighborFinset v, f y = ∑ u ∈ T, g u := by
      rw [← hmap, Finset.sum_map]
      exact Finset.sum_congr rfl (fun y _ => (hgK y).symm)
    rw [h2] at h1
    rw [← h1, hT]
    have hdis : Disjoint ((H.neighborFinset v.1).filter (fun w => w ∉ U))
        (if v.1 ∈ nbrSet H U then {m v.1} else ∅) := by
      by_cases hv : v.1 ∈ nbrSet H U
      · rw [if_pos hv, Finset.disjoint_singleton_right]
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, not_and]
        intro hadj
        obtain ⟨z, hz, hzv⟩ := (memN _).1 hv
        obtain ⟨z', hz', hzm⟩ := (memN _).1 (hm v.1 hv).1
        exact absurd hadj (P2MEq11CR.match_not_adj H r hr U hU2 hU3 hz hz' hzv hzm
          (fun h => (hm v.1 hv).2.2 h.symm))
      · rw [if_neg hv]; exact Finset.disjoint_empty_right _
    have hf : ∑ x ∈ (H.neighborFinset v.1).filter (fun w => w ∉ U), g x =
        ∑ y ∈ H.neighborFinset v.1, g y := Finset.sum_filter_of_ne (fun u _ hu hU => hu (hgU u hU))
    rw [Finset.sum_union hdis, hf]
    split_ifs <;> simp
  have hdeg : ∀ x : Kept U, ((matchGraph H U m).degree x : ℝ) * f x ^ 2 =
      (if x.1 ∈ nbrSet H U then g x.1 ^ 2 else 0) := by
    intro x
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hgK]
    by_cases hx : x.1 ∈ nbrSet H U
    · have : (matchGraph H U m).neighborFinset x = {⟨m x.1, hmU _ (hm x.1 hx).1⟩} := by
        ext y
        rw [SimpleGraph.mem_neighborFinset, hMadj, Finset.mem_singleton, Subtype.ext_iff]
        simp [hx]
      rw [this, if_pos hx]; simp
    · have : (matchGraph H U m).neighborFinset x = ∅ := by
        ext y
        rw [SimpleGraph.mem_neighborFinset, hMadj]
        simp [hx]
      rw [this, if_neg hx]; simp
  have hL : ∑ x, ((matchGraph H U m).degree x : ℝ) * f x ^ 2 = ∑ v ∈ nbrSet H U, g v ^ 2 := by
    rw [Finset.sum_congr rfl (fun x _ => hdeg x)]
    rw [hconv (fun v => if v ∈ nbrSet H U then g v ^ 2 else 0) (fun v hv => by simp [hgU v hv])]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hR : ∑ x, f x ^ 2 = ∑ v, g v ^ 2 := by
    rw [← hconv (fun v => g v ^ 2) (fun v hv => by simp [hgU v hv])]
    exact Finset.sum_congr rfl (fun x _ => by rw [hgK])
  have hmain := P2MEq11.main_V H d r hd hreg hr U hU2 hU3 m hm g hgU μ hμ
    (fun w hw => hEk ⟨w, hw⟩)
  rw [hL, hR]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hrpos]
  linarith
