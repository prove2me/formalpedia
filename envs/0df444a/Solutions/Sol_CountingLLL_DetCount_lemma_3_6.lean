-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:12:27.079521+00:00
-- url     : https://prove2.me/submissions/c77ef9b3-14c6-4aa4-a1ce-fc1e50707465

import Definitions.Def_CountingLLL_DetCount_Expansion
import Theorems.Thm_CountingLLL_DetCount_theorem_2_2
import Theorems.Thm_CountingLLL_DetCount_condition11_partition_positive
import Theorems.Thm_CountingLLL_DetCount_claim_3_7
import Theorems.Thm_CountingLLL_DetCount_lemma_3_2


set_option autoImplicit false
open CountingLLL.DetCount CountingLLL.DetCount.CSP
open scoped Classical

private theorem p_nonneg (Φ : CSP) : 0 ≤ Φ.pmax := by
  unfold CSP.pmax
  exact NNReal.coe_nonneg _

private theorem p_bad (Φ : CSP) (c : Fin Φ.m) : Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ Φ.pmax := by
  classical
  have h : Φ.violProb c ≤ Finset.univ.sup Φ.violProb := Finset.le_sup (Finset.mem_univ c)
  have hr : ((Φ.violProb c : NNReal) : ℝ) ≤ ((Finset.univ.sup Φ.violProb : NNReal) : ℝ) := by exact_mod_cast h
  have heq : Φ.prob (fun σ => ¬ Φ.Sat c σ) = (Φ.violProb c : ℝ) := by
    unfold CSP.prob CSP.violProb
    push_cast
    congr 1
    congr 1
    apply congrArg Finset.card
    exact Finset.filter_congr_decidable Finset.univ (fun σ : Φ.Config => ¬ Φ.Sat c σ) (fun σ => Classical.propDecidable _)
  rw [heq]
  exact hr

private theorem numeric_lll (p D : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (h : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1) :
    0 ≤ 6*p/5 ∧ 6*p/5 < 1 ∧ 6*p/5*D ≤ 1/10 := by
  have he : 2 < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hd4 : 0 ≤ p * ((D+1)^2 - 4*D) := by
    have hs : 0 ≤ (D-1)^2 := sq_nonneg _
    have : 0 ≤ (D+1)^2 - 4*D := by nlinarith
    exact mul_nonneg hp this
  have hegap : 0 ≤ 4 * p * (Real.exp 1 - 2) * (D+1)^2 := by positivity
  have hs : 0 ≤ p * ((D+1)^2 - 1) := by
    have : 0 ≤ (D+1)^2 - 1 := by nlinarith [sq_nonneg D]
    exact mul_nonneg hp this
  constructor
  · positivity
  constructor
  · nlinarith
  · nlinarith

private theorem degree_subfamily (Φ : CSP) (E : Finset (Fin Φ.m)) (c : Fin Φ.m) :
    (Φ.nbr E c).card ≤ Φ.Dmax := by
  classical
  have hsub : Φ.nbr E c ⊆ Φ.nbr Finset.univ c := by
    intro j hj
    simp only [CSP.nbr, Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, hj.2⟩
  apply le_trans (Finset.card_le_card hsub)
  unfold CSP.Dmax CSP.Dsub
  exact Finset.le_sup (f := fun j => (Φ.nbr Finset.univ j).card) (Finset.mem_univ c)

private theorem base_power (p : ℝ) (D : ℕ) (hp : 0 ≤ p) (hx : 6*p/5 < 1)
    (hsmall : 6*p/5 * (D : ℝ) ≤ 1/10) :
    (9/10 : ℝ) ≤ (1 - 6*p/5)^D := by
  have hbern := one_add_mul_le_pow (a := -(6*p/5)) (by linarith : (-2:ℝ) ≤ -(6*p/5)) D
  have hbern' : 1 + (D:ℝ)*(-(6*p/5)) ≤ (1 - 6*p/5)^D := by simpa only [sub_eq_add_neg] using hbern
  nlinarith

private theorem local_condition (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m))
    (c : Fin Φ.m) :
    Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ (6*Φ.pmax/5) *
      ∏ j ∈ Φ.nbr E c, (1 - 6*Φ.pmax/5) := by
  have hp := p_nonneg Φ
  have hd : (0:ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have hn := numeric_lll Φ.pmax (Φ.Dmax : ℝ) hp hd hΦ
  have hb : (0:ℝ) ≤ 1 - 6*Φ.pmax/5 := by linarith [hn.2.1]
  have hb1 : (1:ℝ) - 6*Φ.pmax/5 ≤ 1 := by linarith [hn.1]
  have hpow := base_power Φ.pmax Φ.Dmax hp hn.2.1 hn.2.2
  have hdeg := degree_subfamily Φ E c
  have hpow' : (1 - 6*Φ.pmax/5)^Φ.Dmax ≤
      (1 - 6*Φ.pmax/5)^(Φ.nbr E c).card :=
    pow_le_pow_of_le_one hb hb1 hdeg
  have hprod : (9/10:ℝ) ≤ ∏ j ∈ Φ.nbr E c, (1 - 6*Φ.pmax/5) := by
    simpa only [Finset.prod_const] using hpow.trans hpow'
  have hpbound := p_bad Φ c
  have hmul := mul_le_mul_of_nonneg_left hprod hn.1
  nlinarith


namespace CountingLLL.DetCount
private noncomputable def swapCoords {V : Type} [DecidableEq V] (Q : V → Type)
    (S : Finset V) (z : ((v : V) → Q v) × ((v : V) → Q v)) :
    ((v : V) → Q v) × ((v : V) → Q v) :=
  (fun v => if v ∈ S then z.1 v else z.2 v,
   fun v => if v ∈ S then z.2 v else z.1 v)

private theorem swapCoords_inv {V : Type} [DecidableEq V] (Q : V → Type)
    (S : Finset V) : Function.Involutive (swapCoords Q S) := by
  intro z
  apply Prod.ext <;> funext u <;> by_cases hu : u ∈ S <;> simp [swapCoords, hu]

/-- Finite-product counting independence for heterogeneous coordinate domains.
The swap-bijection argument adapts the accepted platform proof of
`OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample`
(https://prove2.me), generalized here to dependent coordinate domains. -/
theorem audit_dependent_disjoint_card {V : Type} [Fintype V] [DecidableEq V]
    (Q : V → Type) [∀ v, Fintype (Q v)] [∀ v, DecidableEq (Q v)]
    (S T : Finset V) (A B : Finset ((v : V) → Q v))
    (hA : ∀ x y, (∀ v ∈ S, x v = y v) → (x ∈ A ↔ y ∈ A))
    (hB : ∀ x y, (∀ v ∈ T, x v = y v) → (x ∈ B ↔ y ∈ B))
    (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card ((v : V) → Q v) = A.card * B.card := by
  classical
  have hforward : ∀ z ∈ (A ∩ B).product (Finset.univ : Finset ((v : V) → Q v)),
      swapCoords Q S z ∈ A.product B := by
    rintro ⟨x, y⟩ hz
    have hxA := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).1
    have hxB := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).2
    apply Finset.mem_product.mpr
    constructor
    · apply (hA _ x ?_).mpr hxA
      intro u hu
      simp [swapCoords, hu]
    · apply (hB _ x ?_).mpr hxB
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [swapCoords, huS]
  have hreverse : ∀ z ∈ A.product B,
      swapCoords Q S z ∈ (A ∩ B).product (Finset.univ : Finset ((v : V) → Q v)) := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_inter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · apply (hA _ x ?_).mpr hx
      intro u hu
      simp [swapCoords, hu]
    · apply (hB _ y ?_).mpr hy
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [swapCoords, huS]
  have hc := Finset.card_nbij' (swapCoords Q S) (swapCoords Q S)
    hforward hreverse (fun z _ => swapCoords_inv Q S z) (fun z _ => swapCoords_inv Q S z)
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ] using hc


end CountingLLL.DetCount

private theorem independent_events (Φ : CSP) (A B : Φ.Config → Prop)
    (S T : Finset (Fin Φ.n))
    (hA : ∀ x y : Φ.Config, (∀ v ∈ S, x v = y v) → (A x ↔ A y))
    (hB : ∀ x y : Φ.Config, (∀ v ∈ T, x v = y v) → (B x ↔ B y))
    (hST : Disjoint S T) :
    Φ.prob (fun σ => A σ ∧ B σ) = Φ.prob A * Φ.prob B := by
  classical
  let P : Finset Φ.Config := Finset.univ.filter A
  let Q : Finset Φ.Config := Finset.univ.filter B
  have hP : ∀ x y : Φ.Config, (∀ v ∈ S, x v = y v) → (x ∈ P ↔ y ∈ P) := by
    intro x y h
    simpa [P] using hA x y h
  have hQ : ∀ x y : Φ.Config, (∀ v ∈ T, x v = y v) → (x ∈ Q ↔ y ∈ Q) := by
    intro x y h
    simpa [Q] using hB x y h
  have hc := CountingLLL.DetCount.audit_dependent_disjoint_card (fun v => Fin (Φ.q v)) S T P Q hP hQ hST
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  have hC : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))
  have hcR : ((P ∩ Q).card : ℝ) * (Fintype.card Φ.Config : ℝ) =
      (P.card : ℝ) * (Q.card : ℝ) := by exact_mod_cast hc
  letI : DecidablePred (fun σ : Φ.Config => A σ ∧ B σ) := fun _ => Classical.propDecidable _
  have hab : P ∩ Q = Finset.univ.filter (fun σ => A σ ∧ B σ) := by
    ext σ
    simp [P, Q]
  have hPQ : ((P ∩ Q).card : ℝ) / (Fintype.card Φ.Config : ℝ) =
      ((P.card : ℝ) / (Fintype.card Φ.Config : ℝ)) * ((Q.card : ℝ) / (Fintype.card Φ.Config : ℝ)) := by
    field_simp
    nlinarith
  unfold CSP.prob
  rw [← hab]
  exact hPQ

private theorem viol_insert_factor (Φ : CSP) (c : Fin Φ.m) (T : Finset (Fin Φ.m))
    (hdisj : ∀ j ∈ T, Disjoint (Φ.scope c) (Φ.scope j)) :
    Φ.prob (Φ.ViolAll (insert c T)) =
      Φ.prob (fun σ => ¬ Φ.Sat c σ) * Φ.prob (Φ.ViolAll T) := by
  classical
  let W : Finset (Fin Φ.n) := T.biUnion Φ.scope
  have hA : ∀ x y : Φ.Config, (∀ v ∈ Φ.scope c, x v = y v) →
      ((¬ Φ.Sat c x) ↔ (¬ Φ.Sat c y)) := by
    intro x y h
    have heq : (fun v : ↥(Φ.scope c) => x v.1) = (fun v : ↥(Φ.scope c) => y v.1) := by
      funext v; exact h v.1 v.2
    simp only [CSP.Sat, heq]
  have hB : ∀ x y : Φ.Config, (∀ v ∈ W, x v = y v) →
      (Φ.ViolAll T x ↔ Φ.ViolAll T y) := by
    intro x y h
    unfold CSP.ViolAll
    apply forall_congr'
    intro c'
    apply forall_congr'
    intro hc'
    have heq : (fun v : ↥(Φ.scope c') => x v.1) = (fun v : ↥(Φ.scope c') => y v.1) := by
      funext v
      exact h v.1 (Finset.mem_biUnion.mpr ⟨c', hc', v.2⟩)
    simp only [CSP.Sat, heq]
  have hW : Disjoint (Φ.scope c) W := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hw
    exact Finset.disjoint_left.mp (hdisj j hj) hv hvj
  have hi := independent_events Φ (fun σ => ¬ Φ.Sat c σ) (Φ.ViolAll T) (Φ.scope c) W hA hB hW
  have heq : Φ.ViolAll (insert c T) = fun σ => ¬ Φ.Sat c σ ∧ Φ.ViolAll T σ := by
    funext σ
    apply propext
    simp [CSP.ViolAll]
  rw [heq]
  exact hi

private theorem joint_viol_bound (Φ : CSP) (T : Finset (Fin Φ.m))
    (hdisj : ∀ c ∈ T, ∀ j ∈ T, c ≠ j → Disjoint (Φ.scope c) (Φ.scope j)) :
    Φ.prob (Φ.ViolAll T) ≤ Φ.pmax ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have h : Φ.ViolAll ∅ = fun _ => True := by funext σ; simp [CSP.ViolAll]
    rw [h]
    have hq : 0 < ∏ i : Fin Φ.n, (Φ.q i : ℝ) := by
      apply Finset.prod_pos
      intro i hi
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (Φ.two_le_q i))
    unfold CSP.prob
    simp [ne_of_gt hq]
  | @insert c T hc ih =>
    have hdisj' : ∀ c' ∈ T, ∀ j ∈ T, c' ≠ j → Disjoint (Φ.scope c') (Φ.scope j) := by
      intro c' hc' j hj hne
      exact hdisj c' (Finset.mem_insert_of_mem hc') j (Finset.mem_insert_of_mem hj) hne
    have hct : ∀ j ∈ T, Disjoint (Φ.scope c) (Φ.scope j) := by
      intro j hj
      exact hdisj c (Finset.mem_insert_self c T) j (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact hc hj)
    have hprob : 0 ≤ Φ.prob (Φ.ViolAll T) := by unfold CSP.prob; positivity
    have hprod : Φ.prob (fun σ => ¬ Φ.Sat c σ) * Φ.prob (Φ.ViolAll T) ≤
        Φ.pmax * Φ.pmax ^ T.card := mul_le_mul (p_bad Φ c) (ih hdisj') hprob (p_nonneg Φ)
    rw [viol_insert_factor Φ c T hct, Finset.card_insert_of_notMem hc, pow_succ]
    nlinarith

private theorem tree_pairwise_disjoint (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E r) :
    ∀ c ∈ T, ∀ j ∈ T, c ≠ j → Disjoint (Φ.scope c) (Φ.scope j) := by
  classical
  have hT' : T ⊆ E ∧ r ∈ T ∧ IsTwoTree (Φ.depGraph E) T := by
    simpa [CSP.twoTrees] using hT
  intro c hc j hj hne
  have hind := hT'.2.2.1 hc hj hne
  by_contra h
  apply hind
  exact ⟨hT'.1 hc, hT'.1 hj, hne, h⟩

private theorem tree_violation_unconditional (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E r) :
    Φ.prob (Φ.ViolAll T) ≤ Φ.pmax ^ T.card :=
  joint_viol_bound Φ T (tree_pairwise_disjoint Φ E r T hT)

private theorem viol_depend (Φ : CSP) (T : Finset (Fin Φ.m)) :
    ∀ σ σ' : Φ.Config, (∀ v ∈ T.biUnion Φ.scope, σ v = σ' v) →
      (Φ.ViolAll T σ ↔ Φ.ViolAll T σ') := by
  classical
  intro σ σ' h
  unfold CSP.ViolAll
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  have heq : (fun v : ↥(Φ.scope c) => σ v.1) = (fun v : ↥(Φ.scope c) => σ' v.1) := by
    funext v
    exact h v.1 (Finset.mem_biUnion.mpr ⟨c, hc, v.2⟩)
  simp only [CSP.Sat, heq]

private theorem free_scope_neighbor_bound (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    ((Φ.free E r T).filter (fun c => ¬ Disjoint (Φ.scope c) (T.biUnion Φ.scope))).card ≤
      Φ.Dmax * T.card := by
  classical
  have hs : (Φ.free E r T).filter (fun c => ¬ Disjoint (Φ.scope c) (T.biUnion Φ.scope)) ⊆
      T.biUnion (Φ.nbr E) := by
    intro c hc
    have hh := Finset.mem_filter.mp hc
    have hfree := Finset.mem_sdiff.mp hh.1
    obtain ⟨v, hv_c, hv_union⟩ := Finset.not_disjoint_iff.mp hh.2
    obtain ⟨t, ht, hv_t⟩ := Finset.mem_biUnion.mp hv_union
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hfree.1, ?_, ?_⟩
    · intro heq
      subst c
      exact hfree.2 (Finset.mem_union_left _ ht)
    · apply Finset.not_disjoint_iff.mpr
      exact ⟨v, hv_t, hv_c⟩
  calc
    _ ≤ (T.biUnion (Φ.nbr E)).card := Finset.card_le_card hs
    _ ≤ ∑ t ∈ T, (Φ.nbr E t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, Φ.Dmax := by
      apply Finset.sum_le_sum
      intro t ht
      exact degree_subfamily Φ E t
    _ = Φ.Dmax * T.card := by simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]


private theorem event_prob_nonneg (Φ : CSP) (A : Φ.Config → Prop) : 0 ≤ Φ.prob A := by
  unfold CSP.prob
  positivity

private theorem event_prob_mono (Φ : CSP) (A B : Φ.Config → Prop) (h : ∀ σ, A σ → B σ) : Φ.prob A ≤ Φ.prob B := by
  classical
  unfold CSP.prob
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro σ hσ
  have ha := (Finset.mem_filter.mp hσ).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h σ ha⟩

private theorem coefficient_bound (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E r) :
    Φ.treeCoeff E r T ≤ Φ.pmax ^ T.card / (1 - 1.2 * Φ.pmax) ^ (Φ.Dmax * T.card) := by
  classical
  have hT' : T ⊆ E ∧ r ∈ T ∧ IsTwoTree (Φ.depGraph E) T := by simpa [CSP.twoTrees] using hT
  have hposcard : 0 < T.card := Finset.card_pos.mpr ⟨r, hT'.2.1⟩
  have hp := p_nonneg Φ
  have hbad := tree_violation_unconditional Φ E r T hT
  by_cases hpzero : Φ.pmax = 0
  · have hpzero' : Φ.pmax ^ T.card = 0 := by simp [hpzero, Nat.ne_of_gt hposcard]
    have hbad0 : Φ.prob (Φ.ViolAll T) = 0 := by
      apply le_antisymm
      · simpa [hpzero'] using hbad
      · exact event_prob_nonneg Φ _
    have hnum0 : Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ) = 0 := by
      apply le_antisymm
      · calc
          _ ≤ Φ.prob (Φ.ViolAll T) := event_prob_mono Φ _ _ (fun _ h => h.1)
          _ = 0 := hbad0
      · exact event_prob_nonneg Φ _
    simp [CSP.treeCoeff, CSP.condProb, hnum0, hpzero']
  · have hppos : 0 < Φ.pmax := lt_of_le_of_ne hp (Ne.symm hpzero)
    let x : Fin Φ.m → ℝ := fun _ => 6*Φ.pmax/5
    let F := Φ.free E r T
    let W := T.biUnion Φ.scope
    let N := F.filter (fun c => ¬ Disjoint (Φ.scope c) W)
    have hn := numeric_lll Φ.pmax (Φ.Dmax : ℝ) hp (Nat.cast_nonneg _) hΦ
    have hx : ∀ j ∈ F, 0 < x j ∧ x j < 1 := by
      intro j hj
      dsimp [x]
      constructor <;> nlinarith [hn.2.1]
    have h6 : ∀ j ∈ F, Φ.prob (fun σ => ¬ Φ.Sat j σ) ≤
        x j * ∏ j' ∈ Φ.nbr F j, (1 - x j') := by
      intro j hj
      simpa [x] using local_condition Φ hΦ F j
    have hcond := CountingLLL.DetCount.theorem_2_2 Φ F x hx h6 (Φ.ViolAll T) W (viol_depend Φ T)
    have hcard : N.card ≤ Φ.Dmax * T.card := free_scope_neighbor_bound Φ E T r
    have hbase : (0:ℝ) < 1 - 6*Φ.pmax/5 := by linarith [hn.2.1]
    have hbase1 : 1 - 6*Φ.pmax/5 ≤ 1 := by linarith [hn.1]
    have hinv : 1 ≤ (1 - 6*Φ.pmax/5)⁻¹ := by
      apply (one_le_inv₀ hbase).2
      exact hbase1
    have hpow : ((1 - 6*Φ.pmax/5)⁻¹)^N.card ≤
        ((1 - 6*Φ.pmax/5)⁻¹)^(Φ.Dmax * T.card) := pow_le_pow_right₀ hinv hcard
    have hbound : Φ.prob (Φ.ViolAll T) * ∏ c ∈ N, (1 - x c)⁻¹ ≤
        Φ.pmax ^ T.card * ((1 - 6*Φ.pmax/5)⁻¹)^(Φ.Dmax * T.card) := by
      have hh := mul_le_mul hbad hpow (pow_nonneg (inv_nonneg.mpr hbase.le) _) (pow_nonneg hp _)
      simpa [x, Finset.prod_const] using hh
    have hs : Φ.treeCoeff E r T ≤ Φ.pmax ^ T.card * ((1 - 6*Φ.pmax/5)⁻¹)^(Φ.Dmax * T.card) := by
      exact hcond.trans hbound
    have heq : (1 - 1.2 * Φ.pmax : ℝ) = 1 - 6*Φ.pmax/5 := by ring
    rw [heq, div_eq_mul_inv, ← inv_pow]
    exact hs


set_option autoImplicit false

open CountingLLL.DetCount

/-- Claim 3.7 rewritten for the range and nonnegative supremum used by Lemma 3.6.
This version includes the zero-length and zero-radius cases. -/
theorem reciprocal_products_lipschitz (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ℓ : ℕ) (x y : ℕ → ℝ)
    (hx : ∀ i < ℓ, -t ≤ x i ∧ x i ≤ t) (hy : ∀ i < ℓ, -t ≤ y i ∧ y i ≤ t) :
    |(∏ i ∈ Finset.range ℓ, 1 / (1 - x i)) - (∏ i ∈ Finset.range ℓ, 1 / (1 - y i))| ≤
      (ℓ : ℝ) / (1 - t) ^ (ℓ + 1) *
        (((Finset.range ℓ).sup (fun i => ‖x i - y i‖₊) : NNReal) : ℝ) := by
  classical
  by_cases hℓ : ℓ = 0
  · subst ℓ; simp
  have hℓ' : 1 ≤ ℓ := by omega
  by_cases ht : t = 0
  · subst t
    have hxy : ∀ i ∈ Finset.range ℓ, x i = y i := by
      intro i hi
      have hx' := hx i (Finset.mem_range.mp hi)
      have hy' := hy i (Finset.mem_range.mp hi)
      linarith
    have hprod : (∏ i ∈ Finset.range ℓ, 1 / (1 - x i)) =
        ∏ i ∈ Finset.range ℓ, 1 / (1 - y i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hxy i hi]
    rw [hprod, sub_self, abs_zero]
    positivity
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hclaim := claim_3_7 t htpos ht1 ℓ hℓ' (fun i => x i.val) (fun i => y i.val)
      (fun i => hx i.val i.isLt) (fun i => hy i.val i.isLt)
    have hsup : (Finset.univ : Finset (Fin ℓ)).sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hℓ'⟩⟩) (fun i => |x i.val - y i.val|) ≤
        (((Finset.range ℓ).sup (fun i => ‖x i - y i‖₊) : NNReal) : ℝ) := by
      apply Finset.sup'_le
      intro i hi
      have h := Finset.le_sup (f := fun i => ‖x i - y i‖₊) (Finset.mem_range.mpr i.isLt)
      exact_mod_cast h
    have hp1 := Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 / (1 - x i)) ℓ
    have hp2 := Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 / (1 - y i)) ℓ
    rw [hp1, hp2] at hclaim
    exact hclaim.trans (mul_le_mul_of_nonneg_left hsup (by positivity))

open CountingLLL.DetCount.CSP

theorem condition11_box_radius (Φ : CSP) (hΦ : Φ.Condition11) :
    0 ≤ 2 * Φ.pmax ∧ 2 * Φ.pmax < 1 := by
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hd : (0 : ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have hsq : 1 ≤ ((Φ.Dmax : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (Φ.Dmax : ℝ)]
  have hmul : 2 < 4 * Real.exp 1 * ((Φ.Dmax : ℝ) + 1) ^ 2 := by
    have ht := mul_nonneg (show 0 ≤ Real.exp 1 - 2 by linarith) (show 0 ≤ ((Φ.Dmax : ℝ) + 1)^2 - 1 by linarith)
    nlinarith
  constructor
  · linarith
  · by_cases hz : Φ.pmax = 0
    · simp [hz]
    · have hp' : 0 < Φ.pmax := lt_of_le_of_ne hp (Ne.symm hz)
      have hm : 0 < Φ.pmax * (4 * Real.exp 1 * ((Φ.Dmax : ℝ) + 1)^2 - 2) := by positivity
      unfold CSP.Condition11 at hΦ
      nlinarith

private theorem prob_nonneg (Φ : CSP) (A : Φ.Config → Prop) : 0 ≤ Φ.prob A := by
  classical
  unfold CSP.prob
  positivity

private theorem coeff_nonneg (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) : 0 ≤ Φ.treeCoeff E c₀ T := by
  unfold CSP.treeCoeff CSP.condProb
  exact div_nonneg (prob_nonneg Φ _) (prob_nonneg Φ _)

/-- The elementary absorption inequality used after equations (15)–(16). -/
theorem linear_absorbed_by_geometric (n : ℕ) : (n : ℝ) ≤ 2.1 * (1.2 : ℝ) ^ n := by
  have hlarge : ∀ k : ℕ, ((k + 5 : ℕ) : ℝ) ≤ 2.1 * (1.2 : ℝ) ^ (k + 5) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hk : (5 : ℝ) ≤ ((k + 5 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 5 k
      have heq : k + 1 + 5 = (k + 5) + 1 := by omega
      rw [heq, pow_succ]
      push_cast
      push_cast at ih hk
      nlinarith
  by_cases hn : n < 5
  · interval_cases n <;> norm_num
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 5 ≤ n)
    simpa [Nat.add_comm] using hlarge k

/-- Arithmetic core of the estimates (13) and (14), abstracting away the CSP.
`u` and `v` are the reciprocal factors `(1-2p)⁻¹` and `(1-1.2p)⁻¹`. -/
theorem numerical_tree_bounds (p u v c : ℝ) (d n l : ℕ)
    (hp : 0 ≤ p) (hu : 1 ≤ u) (hv : 0 ≤ v ∧ v ≤ u)
    (hc : 0 ≤ c ∧ c ≤ p ^ n * v ^ (d*n))
    (hn : 1 ≤ n) (hl : l + 1 ≤ (d^2 + 1) * n) :
    let β := p * u ^ ((d+1)^2)
    c * u^l ≤ β^n ∧
    c * (l : ℝ) * u^(l+1) ≤ (2.1 * ((d : ℝ)+1)^2) * (1.2 * β)^n := by
  dsimp only
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hpN : 0 ≤ p^n := pow_nonneg hp _
  have hce : c ≤ p^n * u^(d*n) :=
    hc.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.1 hv.2 _) hpN)
  have hexp : d*n + (l+1) ≤ (d+1)^2 * n := by nlinarith
  have hexp0 : d*n + l ≤ (d+1)^2 * n := by omega
  have hpow : u ^ (d*n + l) ≤ u ^ ((d+1)^2*n) := pow_le_pow_right₀ hu hexp0
  have hpow' : u ^ (d*n + (l+1)) ≤ u ^ ((d+1)^2*n) := pow_le_pow_right₀ hu hexp
  have hbeta : (p * u ^ ((d+1)^2)) ^ n = p^n * u^((d+1)^2*n) := by rw [mul_pow, pow_mul]
  have hcore : c * u^l ≤ (p * u ^ ((d+1)^2)) ^ n := by
    calc
      _ ≤ (p^n * u^(d*n)) * u^l := mul_le_mul_of_nonneg_right hce (pow_nonneg hu0 _)
      _ = p^n * u^(d*n+l) := by rw [pow_add]; ring
      _ ≤ p^n * u^((d+1)^2*n) := mul_le_mul_of_nonneg_left hpow hpN
      _ = _ := hbeta.symm
  have hcore' : c * u^(l+1) ≤ (p * u ^ ((d+1)^2)) ^ n := by
    calc
      _ ≤ (p^n * u^(d*n)) * u^(l+1) := mul_le_mul_of_nonneg_right hce (pow_nonneg hu0 _)
      _ = p^n * u^(d*n+(l+1)) := by rw [pow_add]; ring
      _ ≤ p^n * u^((d+1)^2*n) := mul_le_mul_of_nonneg_left hpow' hpN
      _ = _ := hbeta.symm
  have hl' : (l : ℝ) ≤ ((d : ℝ)+1)^2 * n := by
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hcast : (l : ℝ) + 1 ≤ ((d : ℝ)^2 + 1) * n := by exact_mod_cast hl
    nlinarith
  have hlin := linear_absorbed_by_geometric n
  have hscale : (l : ℝ) ≤ (2.1 * ((d : ℝ)+1)^2) * (1.2 : ℝ)^n := by
    have hdpos : 0 ≤ ((d : ℝ)+1)^2 := sq_nonneg _
    nlinarith [mul_nonneg hdpos (show 0 ≤ 2.1 * (1.2 : ℝ)^n - n by linarith)]
  constructor
  · exact hcore
  · have hb0 : 0 ≤ (p * u ^ ((d+1)^2)) ^ n := pow_nonneg (mul_nonneg hp (pow_nonneg hu0 _)) _
    calc
      _ = (c * u^(l+1)) * l := by ring
      _ ≤ ((p * u ^ ((d+1)^2)) ^ n) * l := mul_le_mul_of_nonneg_right hcore' (Nat.cast_nonneg _)
      _ ≤ ((p * u ^ ((d+1)^2)) ^ n) * ((2.1 * ((d : ℝ)+1)^2) * (1.2 : ℝ)^n) :=
        mul_le_mul_of_nonneg_left hscale hb0
      _ = _ := by rw [mul_pow]; ring

private theorem coeff_nonneg2 (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (T : Finset (Fin Φ.m)) : 0 ≤ Φ.treeCoeff E r T := by
  classical
  unfold CSP.treeCoeff CSP.condProb CSP.prob
  positivity

/-- The source's estimates (15) and (16) imply the per-tree scalar bounds. -/
theorem tree_scalar_of_source_bounds (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hcoeff : ∀ T ∈ Φ.twoTrees E r,
      Φ.treeCoeff E r T ≤ Φ.pmax ^ T.card / (1 - 1.2 * Φ.pmax) ^ (Φ.Dmax * T.card))
    (hsize : ∀ T ∈ Φ.twoTrees E r,
      Φ.ell E r T + 1 ≤ (Φ.Dmax^2 + 1) * T.card) :
    let p := Φ.pmax
    let α : ℝ := 2.1 * ((Φ.Dmax : ℝ) + 1) ^ 2
    let β : ℝ := p / (1 - 2 * p) ^ ((Φ.Dmax + 1) ^ 2)
    let Box : (Finset (Fin Φ.m) → ℕ → ℝ) → Prop := fun x =>
      ∀ T ∈ Φ.twoTrees E r, ∀ i < Φ.ell E r T, -2 * p ≤ x T i ∧ x T i ≤ 2 * p
    ∀ T ∈ Φ.twoTrees E r,
      (∀ x, Box x →
        Φ.treeCoeff E r T * ∏ i ∈ Finset.range (Φ.ell E r T), 1 / (1 - x T i) ≤ β ^ T.card) ∧
      Φ.treeCoeff E r T * ((Φ.ell E r T : ℝ) / (1 - 2 * p) ^ (Φ.ell E r T + 1)) ≤
        α * (1.2 * β) ^ T.card := by
  classical
  dsimp only
  intro T hT
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have hsmall := condition11_box_radius Φ hΦ
  have hq : 0 < 1 - 2 * Φ.pmax := by linarith
  have ha : 0 < 1 - 1.2 * Φ.pmax := by linarith
  let u : ℝ := 1 / (1 - 2 * Φ.pmax)
  let v : ℝ := 1 / (1 - 1.2 * Φ.pmax)
  have hu : 1 ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ hq]
    nlinarith
  have hv : 0 ≤ v ∧ v ≤ u := by
    constructor
    · dsimp [v]; positivity
    · dsimp [v, u]
      apply one_div_le_one_div_of_le hq
      nlinarith
  have hc : 0 ≤ Φ.treeCoeff E r T ∧
      Φ.treeCoeff E r T ≤ Φ.pmax ^ T.card * v ^ (Φ.Dmax * T.card) := by
    refine ⟨coeff_nonneg2 Φ E r T, ?_⟩
    simpa [v, div_eq_mul_inv, inv_pow] using hcoeff T hT
  have hn : 1 ≤ T.card := Finset.card_pos.mpr ⟨r, (Finset.mem_filter.mp hT).2.1⟩
  have hnum := numerical_tree_bounds Φ.pmax u v (Φ.treeCoeff E r T)
    Φ.Dmax T.card (Φ.ell E r T) hp hu hv hc hn (hsize T hT)
  have hbeta : Φ.pmax * u ^ ((Φ.Dmax + 1)^2) =
      Φ.pmax / (1 - 2*Φ.pmax)^((Φ.Dmax + 1)^2) := by
    simp [u, div_eq_mul_inv, inv_pow]
  constructor
  · intro x hx
    have hprod : (∏ i ∈ Finset.range (Φ.ell E r T), 1 / (1 - x T i)) ≤ u ^ (Φ.ell E r T) := by
      calc
        _ ≤ ∏ i ∈ Finset.range (Φ.ell E r T), u := by
          apply Finset.prod_le_prod
          · intro i hi
            have hxi := hx T hT i (Finset.mem_range.mp hi)
            have : 0 < 1 - x T i := by linarith
            positivity
          · intro i hi
            have hxi := hx T hT i (Finset.mem_range.mp hi)
            dsimp [u]
            apply one_div_le_one_div_of_le hq
            linarith
        _ = _ := by simp
    calc
      _ ≤ Φ.treeCoeff E r T * u^(Φ.ell E r T) :=
          mul_le_mul_of_nonneg_left hprod (coeff_nonneg2 Φ E r T)
      _ ≤ (Φ.pmax * u^((Φ.Dmax+1)^2))^T.card := hnum.1
      _ = _ := by rw [hbeta]
  · have hh := hnum.2
    rw [hbeta] at hh
    simpa [u, div_eq_mul_inv, inv_pow, mul_assoc] using hh


namespace CountingLLL.DetCount
open CSP

private theorem step_subset (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) :
    st.1 ⊆ (Φ.treeStep E D st).1 ∧ st.2 ⊆ (Φ.treeStep E D st).2 := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs <;> simp_all [Finset.subset_insert]

private theorem step_inv (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ha : st.1 ⊆ D) (hr : st.2 ⊆ E \ D) :
    (Φ.treeStep E D st).1 ⊆ D ∧ (Φ.treeStep E D st).2 ⊆ E \ D := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with h hD
  · simp only [Prod.fst, Prod.snd, Finset.insert_subset_iff]
    exact ⟨⟨hD, ha⟩, hr⟩
  · simp only [Prod.fst, Prod.snd, Finset.insert_subset_iff]
    refine ⟨ha, ⟨?_, hr⟩⟩
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).1, hD⟩
  · exact ⟨ha, hr⟩

private theorem run_inv (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ha : st.1 ⊆ D) (hr : st.2 ⊆ E \ D) (n : ℕ) :
    ((Φ.treeStep E D)^[n] st).1 ⊆ D ∧ ((Φ.treeStep E D)^[n] st).2 ⊆ E \ D := by
  induction n with
  | zero => simpa using And.intro ha hr
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_inv Φ E D _ ih.1 ih.2

private theorem run_monotone (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (n : ℕ) :
    st.1 ⊆ ((Φ.treeStep E D)^[n] st).1 ∧ st.2 ⊆ ((Φ.treeStep E D)^[n] st).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1.trans (step_subset Φ E D _).1, ih.2.trans (step_subset Φ E D _).2⟩

private theorem inf_two_has_witness {V : Type} (G : SimpleGraph V) (S : Finset V) (v : V)
    (h : distSet G v S = 2) : ∃ w ∈ S, G.edist v w = 2 := by
  classical
  have hw : ∃ w ∈ S, G.edist v w ≤ 2 := by
    apply (Finset.inf_le_iff (ENat.natCast_lt_top 2)).mp
    change distSet G v S ≤ 2
    rw [h]
  obtain ⟨w, hw, hle⟩ := hw
  refine ⟨w, hw, le_antisymm hle ?_⟩
  have hlow := Finset.inf_le (f := fun w => G.edist v w) hw
  change distSet G v S ≤ G.edist v w at hlow
  rw [h] at hlow
  exact hlow

private def RejectWitness (Φ : CSP) (E : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) : Prop :=
  ∀ c ∈ st.2, ∃ t ∈ st.1, (Φ.depGraph E).edist c t = 2

private theorem witness_step (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (h : RejectWitness Φ E st) :
    RejectWitness Φ E (Φ.treeStep E D st) := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc hd
  · intro c hcR
    obtain ⟨t, ht, he⟩ := h c hcR
    exact ⟨t, Finset.mem_insert_of_mem ht, he⟩
  · intro c hcR
    rcases Finset.mem_insert.mp hcR with hnew | hold
    · subst c
      exact inf_two_has_witness (Φ.depGraph E) st.1 _ (Finset.mem_filter.mp (Finset.min'_mem _ hc)).2.2
    · exact h c hold
  · exact h

private theorem witness_run (Φ : CSP) (E D : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    RejectWitness Φ E (Φ.treeRun E r D) := by
  have h : ∀ n, RejectWitness Φ E ((Φ.treeStep E D)^[n] ({r}, ∅)) := by
    intro n
    induction n with
    | zero => simp [RejectWitness]
    | succ n ih => rw [Function.iterate_succ_apply']; exact witness_step Φ E D _ ih
  exact h E.card

private theorem nbr_subset_univ (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    Φ.nbr E v ⊆ Φ.nbr Finset.univ v := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hx'.2⟩

private theorem nbr_card_bound (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    (Φ.nbr E v).card ≤ Φ.Dmax := by
  classical
  apply (Finset.card_le_card (nbr_subset_univ Φ E v)).trans
  unfold CSP.Dmax CSP.Dsub
  exact Finset.le_sup (f := fun c => (Φ.nbr Finset.univ c).card) (Finset.mem_univ v)

private theorem adj_nbr (Φ : CSP) (E : Finset (Fin Φ.m)) {a b : Fin Φ.m}
    (h : (Φ.depGraph E).Adj a b) : b ∈ Φ.nbr E a := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨h.2.1, h.2.2.1.symm, h.2.2.2⟩

private theorem nbr_two_card (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    ((Φ.nbr E v).biUnion (Φ.nbr E)).card ≤ Φ.Dmax^2 := by
  classical
  calc
    _ ≤ ∑ w ∈ Φ.nbr E v, (Φ.nbr E w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ Φ.nbr E v, Φ.Dmax := by
      apply Finset.sum_le_sum
      intro w hw
      exact nbr_card_bound Φ E w
    _ = (Φ.nbr E v).card * Φ.Dmax := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Φ.Dmax^2 := by
      have h := nbr_card_bound Φ E v
      nlinarith

private theorem rejected_card_bound (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    (Φ.rejected E r T).card ≤ Φ.Dmax^2 * T.card := by
  classical
  have hfix := (lemma_3_2 Φ E r).2 T hT
  have hwit := witness_run Φ E T r
  have hsub : Φ.rejected E r T ⊆ T.biUnion (fun t => (Φ.nbr E t).biUnion (Φ.nbr E)) := by
    intro c hc
    obtain ⟨t, ht, he⟩ := hwit c hc
    have ht' : t ∈ T := by change t ∈ Φ.Tree E r T at ht; rwa [hfix] at ht
    obtain ⟨_, _, ⟨w, hw⟩⟩ := SimpleGraph.edist_eq_two_iff.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht', ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨w, adj_nbr Φ E hw.2, adj_nbr Φ E hw.1.symm⟩
  calc
    _ ≤ (T.biUnion (fun t => (Φ.nbr E t).biUnion (Φ.nbr E))).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, ((Φ.nbr E t).biUnion (Φ.nbr E)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, Φ.Dmax^2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact nbr_two_card Φ E t
    _ = Φ.Dmax^2 * T.card := by simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

/-- The source's rejected-set size estimate (16), including the finite-run invariants. -/
theorem tree_rest_card_bound (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Φ.ell E r T + 1 ≤ (Φ.Dmax^2 + 1) * T.card := by
  classical
  have hTE : T ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hrT : r ∈ T := (Finset.mem_filter.mp hT).2.1
  have hrR : Φ.rejected E r T ⊆ E \ T := by
    have hi := run_inv Φ E T ({r}, ∅) (by simpa using hrT) (by simp) E.card
    exact hi.2
  have hrest : Φ.rest E r T = (T ∪ Φ.rejected E r T).erase r := by
    ext c
    have hce : c ∈ T → c ∈ E := fun h => hTE h
    have hcr : c ∈ Φ.rejected E r T → c ∈ E := fun h => (Finset.mem_sdiff.mp (hrR h)).1
    simp only [CSP.rest, CSP.free, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_erase]
    by_cases h1 : c ∈ T <;> by_cases h2 : c ∈ Φ.rejected E r T <;>
      by_cases h3 : c = r <;> by_cases h4 : c ∈ E <;> simp_all
  have hroot : r ∈ T ∪ Φ.rejected E r T := Finset.mem_union_left _ hrT
  have hcard := Finset.card_erase_add_one hroot
  rw [← hrest] at hcard
  have hrej := rejected_card_bound Φ E T r hT
  have huni := Finset.card_union_le T (Φ.rejected E r T)
  change (Φ.rest E r T).card + 1 ≤ (Φ.Dmax^2 + 1) * T.card
  nlinarith

/-- At most D constraints in `free(T)` touch each scope in T. -/
theorem free_scope_neighbor_bound (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    ((Φ.free E r T).filter (fun c => ¬ Disjoint (Φ.scope c) (T.biUnion Φ.scope))).card ≤
      Φ.Dmax * T.card := by
  classical
  have hs : (Φ.free E r T).filter (fun c => ¬ Disjoint (Φ.scope c) (T.biUnion Φ.scope)) ⊆
      T.biUnion (Φ.nbr E) := by
    intro c hc
    have hh := Finset.mem_filter.mp hc
    have hfree := Finset.mem_sdiff.mp hh.1
    obtain ⟨v, hv_c, hv_union⟩ := Finset.not_disjoint_iff.mp hh.2
    obtain ⟨t, ht, hv_t⟩ := Finset.mem_biUnion.mp hv_union
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hfree.1, ?_, ?_⟩
    · intro heq
      subst c
      exact hfree.2 (Finset.mem_union_left _ ht)
    · apply Finset.not_disjoint_iff.mpr
      exact ⟨v, hv_t, hv_c⟩
  calc
    _ ≤ (T.biUnion (Φ.nbr E)).card := Finset.card_le_card hs
    _ ≤ ∑ t ∈ T, (Φ.nbr E t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, Φ.Dmax := by
      apply Finset.sum_le_sum
      intro t ht
      exact nbr_card_bound Φ E t
    _ = Φ.Dmax * T.card := by simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

end CountingLLL.DetCount


private theorem tree_source_bounds (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    (∀ T ∈ Φ.twoTrees E r,
      Φ.treeCoeff E r T ≤ Φ.pmax ^ T.card / (1 - 1.2 * Φ.pmax) ^ (Φ.Dmax * T.card)) ∧
    (∀ T ∈ Φ.twoTrees E r,
      Φ.ell E r T + 1 ≤ (Φ.Dmax^2 + 1) * T.card) := by
  exact ⟨(fun T hT => coefficient_bound Φ hΦ E r hr T hT), fun T hT => tree_rest_card_bound Φ E T r hT⟩

private theorem tree_terms_of_scalar (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (hc₀ : c₀ ∈ E) :
    let p := Φ.pmax
    let α : ℝ := 2.1 * ((Φ.Dmax : ℝ) + 1) ^ 2
    let β : ℝ := p / (1 - 2 * p) ^ ((Φ.Dmax + 1) ^ 2)
    let Box : (Finset (Fin Φ.m) → ℕ → ℝ) → Prop := fun x =>
      ∀ T ∈ Φ.twoTrees E c₀, ∀ i < Φ.ell E c₀ T, -2 * p ≤ x T i ∧ x T i ≤ 2 * p
    ∀ T ∈ Φ.twoTrees E c₀,
      (∀ x, Box x →
        Φ.treeCoeff E c₀ T * ∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i) ≤ β ^ T.card) ∧
      (∀ x y, Box x → Box y →
        Φ.treeCoeff E c₀ T *
          |(∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i)) -
           (∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - y T i))| ≤
          α * (1.2 * β) ^ T.card *
            (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ)) := by
  dsimp only
  intro T hT
  constructor
  · exact (tree_scalar_of_source_bounds Φ hΦ E c₀ (tree_source_bounds Φ hΦ E c₀ hc₀).1 (tree_source_bounds Φ hΦ E c₀ hc₀).2 T hT).1
  · intro x y hx hy
    have ht := condition11_box_radius Φ hΦ
    have hproduct := reciprocal_products_lipschitz (2 * Φ.pmax) ht.1 ht.2 (Φ.ell E c₀ T)
      (x T) (y T) (by simpa [neg_mul] using hx T hT) (by simpa [neg_mul] using hy T hT)
    have hs := (tree_scalar_of_source_bounds Φ hΦ E c₀ (tree_source_bounds Φ hΦ E c₀ hc₀).1 (tree_source_bounds Φ hΦ E c₀ hc₀).2 T hT).2
    have hm : 0 ≤ (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ) := NNReal.coe_nonneg _
    calc
      _ ≤ Φ.treeCoeff E c₀ T * (((Φ.ell E c₀ T : ℝ) / (1 - 2 * Φ.pmax) ^ (Φ.ell E c₀ T + 1)) *
          (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ)) :=
            mul_le_mul_of_nonneg_left hproduct (coeff_nonneg Φ E c₀ T)
      _ = (Φ.treeCoeff E c₀ T * ((Φ.ell E c₀ T : ℝ) / (1 - 2 * Φ.pmax) ^ (Φ.ell E c₀ T + 1))) *
          (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs hm


/-- Reduction of the global correlation decay bound to its source's two per-tree estimates. -/
theorem solution (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E) :
    let p := Φ.pmax
    let α : ℝ := 2.1 * ((Φ.Dmax : ℝ) + 1) ^ 2
    let β : ℝ := p / (1 - 2 * p) ^ ((Φ.Dmax + 1) ^ 2)
    let Box : (Finset (Fin Φ.m) → ℕ → ℝ) → Prop := fun x =>
      ∀ T ∈ Φ.twoTrees E c₀, ∀ i < Φ.ell E c₀ T, -2 * p ≤ x T i ∧ x T i ≤ 2 * p
    (∀ T ∈ Φ.twoTrees E c₀, ∀ x, Box x →
      Φ.treeCoeff E c₀ T * ∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i) ≤ β ^ T.card) ∧
    (∀ x y, Box x → Box y →
      |Φ.fvec E c₀ x - Φ.fvec E c₀ y| ≤
        α * ∑ T ∈ Φ.twoTrees E c₀, (1.2 * β) ^ T.card *
          (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ)) := by
  dsimp only
  constructor
  · intro T hT x hx
    exact (tree_terms_of_scalar Φ hΦ E c₀ hc₀ T hT).1 x hx
  · intro x y hx hy
    unfold CSP.fvec
    rw [← Finset.sum_sub_distrib]
    calc
      _ = |∑ T ∈ Φ.twoTrees E c₀,
          (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E c₀ T *
            ((∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i)) -
             (∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - y T i)))| := by
          congr 1
          apply Finset.sum_congr rfl
          intro T hT
          ring
      _ ≤ ∑ T ∈ Φ.twoTrees E c₀,
          |(-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E c₀ T *
            ((∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i)) -
             (∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - y T i)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ T ∈ Φ.twoTrees E c₀, Φ.treeCoeff E c₀ T *
            |(∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i)) -
             (∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - y T i))| := by
          apply Finset.sum_congr rfl
          intro T hT
          simp [abs_mul, abs_of_nonneg (coeff_nonneg Φ E c₀ T)]
      _ ≤ ∑ T ∈ Φ.twoTrees E c₀,
          (2.1 * ((Φ.Dmax : ℝ) + 1) ^ 2) *
          (1.2 * (Φ.pmax / (1 - 2 * Φ.pmax) ^ ((Φ.Dmax + 1) ^ 2))) ^ T.card *
          (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ) := by
          apply Finset.sum_le_sum
          intro T hT
          exact (tree_terms_of_scalar Φ hΦ E c₀ hc₀ T hT).2 x y hx hy
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T hT
          ring
