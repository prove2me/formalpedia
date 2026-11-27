-- Prove2me | solution 1 for EvenCycleListing723.Main.exploration_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:42:40.064673+00:00
-- url     : https://prove2.me/submissions/d94b8f9a-6f41-418b-bfc6-73d65737ba58

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_Execution
import Theorems.Thm_EvenCycleListing723_Main_lemma_3_2

/-!
# Exploration bound (proof of Theorem 1.1 of Pant–Vassilevska Williams, dyadic bucketing)

Lemma 3.2 (`EvenCycleListing723.Main.lemma_3_2`) is used as a black box.
-/

set_option autoImplicit false

open EvenCycleListing723.Main

namespace L33Aux

variable {n : ℕ}

/-! ### chooseRoot returns a vertex of maximum current degree -/
lemma chooseRoot_spec (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n)
    (h : chooseRoot G A = some u) :
    u ∈ A ∧ ∀ v ∈ A, (neighbors G A v).card ≤ (neighbors G A u).card := by
  unfold chooseRoot at h
  set d : Fin n → ℕ := fun x => (neighbors G A x).card with hd
  set r : Fin n → Fin n → Bool := fun u v =>
    if (neighbors G A u).card = (neighbors G A v).card then decide (u ≤ v)
    else decide ((neighbors G A v).card ≤ (neighbors G A u).card) with hr
  have hr' : ∀ a b, r a b = true ↔ (d b < d a ∨ (d a = d b ∧ a ≤ b)) := by
    intro a b
    simp only [hr, hd]
    split_ifs with h1
    · simp only [decide_eq_true_eq]; omega
    · simp only [decide_eq_true_eq]; omega
  have htrans : ∀ a b c, r a b = true → r b c = true → r a c = true := by
    intro a b c h1 h2
    rw [hr'] at h1 h2 ⊢
    rw [Fin.le_def] at *
    omega
  have htot : ∀ a b, (r a b || r b a) = true := by
    intro a b
    rw [Bool.or_eq_true, hr', hr']
    rw [Fin.le_def, Fin.le_def]
    omega
  have hsorted := List.pairwise_mergeSort htrans htot A.toList
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp h
  have hmem : ∀ x, x ∈ A ↔ x ∈ u :: t := by
    intro x
    rw [← ht, List.mem_mergeSort, Finset.mem_toList]
  refine ⟨(hmem u).2 (List.mem_cons_self), ?_⟩
  intro v hv
  rcases List.mem_cons.mp ((hmem v).1 hv) with rfl | hvt
  · exact le_rfl
  · rw [ht] at hsorted
    have := (List.pairwise_cons.mp hsorted).1 v hvt
    rw [hr'] at this
    show d v ≤ d u
    omega

/-! ### Structure of `rounds` -/

lemma roundsAux_spec (G : SimpleGraph (Fin n)) (fuel : ℕ) (A : Finset (Fin n)) :
    (∀ p ∈ roundsAux G fuel A, p.1 ⊆ A ∧ p.2 ∈ p.1 ∧
        (∀ v ∈ p.1, (neighbors G p.1 v).card ≤ (neighbors G p.1 p.2).card) ∧
        2 ≤ (neighbors G p.1 p.2).card) ∧
      (roundsAux G fuel A).Pairwise (fun p q => q.1 ⊆ p.1.erase p.2) := by
  induction fuel generalizing A with
  | zero => simp [roundsAux]
  | succ fuel ih =>
    rw [roundsAux]
    rcases hc : chooseRoot G A with _ | u
    · simp
    · simp only
      split_ifs with hdeg
      · simp
      · obtain ⟨ih1, ih2⟩ := ih (A.erase u)
        obtain ⟨huA, hmax⟩ := chooseRoot_spec G A u hc
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨subset_rfl, huA, hmax, by show 2 ≤ (neighbors G A u).card; omega⟩
          · obtain ⟨h1, h2, h3, h4⟩ := ih1 p hp
            exact ⟨h1.trans (Finset.erase_subset _ _), h2, h3, h4⟩
        · refine List.pairwise_cons.mpr ⟨?_, ih2⟩
          intro q hq
          exact (ih1 q hq).1

/-! ### Restricted graphs, balls, cycle counts; one dyadic bucket -/

/-- `G` restricted to the vertex set `A`, on the same vertex type. -/
def restrict (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := x ∈ A ∧ y ∈ A ∧ G.Adj x y
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.2.2⟩

lemma restrict_adj (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x y : Fin n) :
    (restrict G A).Adj x y ↔ x ∈ A ∧ y ∈ A ∧ G.Adj x y := Iff.rfl

lemma restrict_le (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : restrict G A ≤ G :=
  fun x y h => ((restrict_adj G A x y).1 h).2.2

lemma mem_neighbors {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {u v : Fin n} :
    v ∈ neighbors G A u ↔ v ∈ A ∧ G.Adj u v := by
  unfold neighbors; simp

lemma neighbors_mono (G : SimpleGraph (Fin n)) {B A : Finset (Fin n)} (h : B ⊆ A) (u : Fin n) :
    neighbors G B u ⊆ neighbors G A u := by
  intro v hv
  rw [mem_neighbors] at hv ⊢
  exact ⟨h hv.1, hv.2⟩

lemma neighbors_restrict_of_mem (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) {u : Fin n}
    (hu : u ∈ A) : neighbors (restrict G A) Finset.univ u = neighbors G A u := by
  ext v
  rw [mem_neighbors, mem_neighbors]
  simp only [Finset.mem_univ, true_and, restrict_adj]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hu, h.1, h.2⟩⟩

lemma neighbors_restrict_of_not_mem (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) {u : Fin n}
    (hu : u ∉ A) : neighbors (restrict G A) Finset.univ u = ∅ := by
  ext v
  rw [mem_neighbors]
  simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, restrict_adj]
  exact fun h => hu h.1

lemma ball_subset_self (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n) (r : ℕ) :
    ball G A u r ⊆ A := by
  induction r with
  | zero =>
    simp only [ball]
    split_ifs with h
    · simpa using h
    · exact Finset.empty_subset _
  | succ r ih =>
    simp only [ball]
    refine Finset.union_subset ih ?_
    intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨w, _, hw⟩ := hv
    exact (mem_neighbors.mp hw).1

lemma ball_subset_succ (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n) (r : ℕ) :
    ball G A u r ⊆ ball G A u (r + 1) := by
  simp only [ball]
  exact Finset.subset_union_left

lemma ball_subset_restrict (G : SimpleGraph (Fin n)) {B A : Finset (Fin n)} (h : B ⊆ A)
    (u : Fin n) (r : ℕ) : ball G B u r ⊆ ball (restrict G A) Finset.univ u r := by
  induction r with
  | zero =>
    simp only [ball, Finset.mem_univ, if_true]
    split_ifs
    · exact subset_rfl
    · exact Finset.empty_subset _
  | succ r ih =>
    simp only [ball]
    refine Finset.union_subset_union ih ?_
    intro v hv
    rw [Finset.mem_biUnion] at hv ⊢
    obtain ⟨w, hw, hv⟩ := hv
    have hwB : w ∈ B := ball_subset_self G B u r hw
    refine ⟨w, ih hw, ?_⟩
    rw [neighbors_restrict_of_mem G A (h hwB)]
    exact neighbors_mono G h w hv

lemma mem_ball_univ_iff (H : SimpleGraph (Fin n)) (u : Fin n) (r : ℕ) (v : Fin n) :
    v ∈ ball H Finset.univ u r ↔ ∃ p : H.Walk v u, p.length ≤ r := by
  induction r generalizing v with
  | zero =>
    simp only [ball, Finset.mem_univ, if_true, Finset.mem_singleton, nonpos_iff_eq_zero]
    constructor
    · rintro rfl; exact ⟨SimpleGraph.Walk.nil, rfl⟩
    · rintro ⟨p, hp⟩
      exact SimpleGraph.Walk.eq_of_length_eq_zero hp
  | succ r ih =>
    simp only [ball]
    rw [Finset.mem_union, Finset.mem_biUnion, ih]
    constructor
    · rintro (⟨p, hp⟩ | ⟨w, hw, hvw⟩)
      · exact ⟨p, by omega⟩
      · obtain ⟨p, hp⟩ := (ih w).1 hw
        have had : H.Adj w v := (mem_neighbors.mp hvw).2
        exact ⟨SimpleGraph.Walk.cons had.symm p, by simp; omega⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl ⟨SimpleGraph.Walk.nil, by simp⟩
      | cons had q =>
        right
        refine ⟨_, (ih _).2 ⟨q, by simp at hp; omega⟩, ?_⟩
        rw [mem_neighbors]
        exact ⟨Finset.mem_univ _, had.symm⟩

lemma mem_ball_univ_symm (H : SimpleGraph (Fin n)) (u v : Fin n) (r : ℕ)
    (h : v ∈ ball H Finset.univ u r) : u ∈ ball H Finset.univ v r := by
  obtain ⟨p, hp⟩ := (mem_ball_univ_iff H u r v).1 h
  exact (mem_ball_univ_iff H v r u).2 ⟨p.reverse, by simpa using hp⟩

lemma cycleCount_mono {H G : SimpleGraph (Fin n)} (hle : H ≤ G) (k : ℕ) :
    cycleCount H k ≤ cycleCount G k := by
  unfold cycleCount cycleCopies
  apply Finset.card_le_card
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
  refine ⟨hE.1, hE.2.1, ?_⟩
  obtain ⟨v, p, hp, hpE⟩ := hE.2.2
  refine ⟨v, p.mapLe hle, hp.mapLe hle, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact hpE

lemma coeffs_nonneg (k : ℕ) : 0 ≤ pairQuadraticCoefficient k ∧ 0 ≤ pairCycleCoefficient k := by
  constructor
  · unfold pairQuadraticCoefficient; positivity
  · unfold pairCycleCoefficient alpha; positivity

/-- One dyadic bucket. -/
lemma bucket_bound (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n))
    (S : Finset (Finset (Fin n) × Fin n))
    (hS1 : ∀ p ∈ S, p.2 ∈ p.1 ∧
        (∀ v ∈ p.1, (neighbors G p.1 v).card ≤ (neighbors G p.1 p.2).card) ∧
        2 ≤ (neighbors G p.1 p.2).card)
    (hS2 : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → q.1 ⊆ p.1.erase p.2 ∨ p.1 ⊆ q.1.erase q.2)
    (j : ℕ) :
    ((∑ p ∈ S.filter (fun p => Nat.log 2 (neighbors G p.1 p.2).card = j),
        ∑ v ∈ ball G p.1 p.2 (k - 1), (neighbors G p.1 v).card : ℕ) : ℝ) ≤
      pairQuadraticCoefficient k * (n : ℝ) ^ 2 +
        pairCycleCoefficient k * (cycleCount G k : ℝ) := by
  classical
  set Sj := S.filter (fun p => Nat.log 2 (neighbors G p.1 p.2).card = j) with hSj
  have hab := coeffs_nonneg k
  rcases Sj.eq_empty_or_nonempty with hE | hne
  · rw [hE, Finset.sum_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ (cycleCount G k : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith [hab.1, hab.2]
  have hmemSj : ∀ q, q ∈ Sj ↔ q ∈ S ∧ Nat.log 2 (neighbors G q.1 q.2).card = j := by
    intro q; rw [hSj, Finset.mem_filter]
  obtain ⟨p0, hp0, hp0max⟩ := Finset.exists_max_image Sj (fun p => p.1.card) hne
  have hp0S := ((hmemSj p0).1 hp0).1
  have hp0j := ((hmemSj p0).1 hp0).2
  obtain ⟨hu0, hmax0, hdeg0⟩ := hS1 p0 hp0S
  set A := p0.1 with hA
  set H := restrict G A with hH
  -- every bucket round lives inside A
  have hsub : ∀ q ∈ Sj, q.1 ⊆ A := by
    intro q hq
    by_cases hqp : p0 = q
    · rw [← hqp]
    · rcases hS2 p0 hp0S q ((hmemSj q).1 hq).1 hqp with h | h
      · exact h.trans (Finset.erase_subset _ _)
      · exfalso
        have h' : A ⊆ q.1.erase q.2 := h
        have h1 := Finset.card_le_card h'
        have hq2 : q.2 ∈ q.1 := (hS1 q ((hmemSj q).1 hq).1).1
        rw [Finset.card_erase_of_mem hq2] at h1
        have h2 : q.1.card ≤ A.card := hp0max q hq
        have h3 : 0 < q.1.card := Finset.card_pos.mpr ⟨q.2, hq2⟩
        omega
  have hj1 : 1 ≤ j := by
    rw [← hp0j]; exact Nat.log_pos (by norm_num) hdeg0
  have hD : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    exact_mod_cast this
  have hmax : ∀ v, (degree H v : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
    intro v
    have hnat : degree H v ≤ 2 * 2 ^ j := by
      unfold degree
      by_cases hv : v ∈ A
      · rw [hH, neighbors_restrict_of_mem G A hv]
        have h1 : (neighbors G A v).card ≤ (neighbors G A p0.2).card := hmax0 v hv
        have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (neighbors G A p0.2).card
        rw [hp0j, pow_succ] at h2
        change (neighbors G A v).card ≤ 2 * 2 ^ j
        change _ < 2 ^ j * 2 at h2
        omega
      · rw [hH, neighbors_restrict_of_not_mem G A hv, Finset.card_empty]
        exact Nat.zero_le _
    exact_mod_cast hnat
  have hdegq : ∀ q ∈ Sj, 2 ^ j ≤ degree H q.2 := by
    intro q hq
    obtain ⟨hqS, hqj⟩ := (hmemSj q).1 hq
    obtain ⟨hq2, _, hqdeg⟩ := hS1 q hqS
    unfold degree
    rw [hH, neighbors_restrict_of_mem G A (hsub q hq hq2)]
    calc 2 ^ j = 2 ^ Nat.log 2 (neighbors G q.1 q.2).card := by rw [hqj]
      _ ≤ (neighbors G q.1 q.2).card := Nat.pow_log_le_self 2 (by omega)
      _ ≤ (neighbors G A q.2).card := Finset.card_le_card (neighbors_mono G (hsub q hq) _)
  -- injectivity of the roots
  have hinj : Set.InjOn Prod.snd (Sj : Set (Finset (Fin n) × Fin n)) := by
    intro p hp q hq hpq
    by_contra hne'
    have hpS := ((hmemSj p).1 hp).1
    have hqS := ((hmemSj q).1 hq).1
    rcases hS2 p hpS q hqS hne' with h | h
    · have := h (hS1 q hqS).1
      rw [Finset.mem_erase] at this
      exact this.1 hpq.symm
    · have := h (hS1 p hpS).1
      rw [Finset.mem_erase] at this
      exact this.1 hpq
  set U := Sj.image Prod.snd with hU
  set P := (Finset.univ ×ˢ U).filter
    (fun p : Fin n × Fin n => p.1 ∈ ball H Finset.univ p.2 (k - 1)) with hPdef
  have hPmem : ∀ p : Fin n × Fin n, p ∈ P ↔ p.2 ∈ U ∧ p.1 ∈ ball H Finset.univ p.2 (k - 1) := by
    intro p
    rw [hPdef, Finset.mem_filter, Finset.mem_product]
    simp
  have hP : ∀ p ∈ P, (2 : ℝ) ^ j ≤ (degree H p.2 : ℝ) ∧
      p.2 ∈ ball H Finset.univ p.1 (k - 1) := by
    intro p hp
    obtain ⟨hpU, hpb⟩ := (hPmem p).1 hp
    refine ⟨?_, mem_ball_univ_symm H _ _ _ hpb⟩
    rw [hU, Finset.mem_image] at hpU
    obtain ⟨q, hq, hqp⟩ := hpU
    have := hdegq q hq
    rw [hqp] at this
    exact_mod_cast this
  have hlem := lemma_3_2 k hk n n le_rfl H ((2 : ℝ) ^ j) hD hmax P hP
  have hnat : (∑ p ∈ Sj, ∑ v ∈ ball G p.1 p.2 (k - 1), (neighbors G p.1 v).card) ≤
      ∑ p ∈ P, degree H p.1 := by
    calc (∑ p ∈ Sj, ∑ v ∈ ball G p.1 p.2 (k - 1), (neighbors G p.1 v).card)
        ≤ ∑ p ∈ Sj, ∑ v ∈ ball H Finset.univ p.2 (k - 1), degree H v := by
          apply Finset.sum_le_sum
          intro q hq
          calc (∑ v ∈ ball G q.1 q.2 (k - 1), (neighbors G q.1 v).card)
              ≤ ∑ v ∈ ball G q.1 q.2 (k - 1), degree H v := by
                apply Finset.sum_le_sum
                intro v hv
                have hvq : v ∈ q.1 := ball_subset_self G q.1 q.2 (k - 1) hv
                unfold degree
                rw [hH, neighbors_restrict_of_mem G A (hsub q hq hvq)]
                exact Finset.card_le_card (neighbors_mono G (hsub q hq) _)
            _ ≤ ∑ v ∈ ball H Finset.univ q.2 (k - 1), degree H v :=
                Finset.sum_le_sum_of_subset (ball_subset_restrict G (hsub q hq) _ _)
      _ = ∑ u ∈ U, ∑ v ∈ ball H Finset.univ u (k - 1), degree H v := by
          rw [hU, Finset.sum_image hinj]
      _ = ∑ p ∈ P, degree H p.1 := by
          rw [Finset.sum_finset_product_right P U (fun u => ball H Finset.univ u (k - 1)) hPmem]
  have hcyc : (cycleCount H k : ℝ) ≤ (cycleCount G k : ℝ) := by
    exact_mod_cast cycleCount_mono (restrict_le G A) k
  calc ((∑ p ∈ Sj, ∑ v ∈ ball G p.1 p.2 (k - 1), (neighbors G p.1 v).card : ℕ) : ℝ)
      ≤ ((∑ p ∈ P, degree H p.1 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ∑ p ∈ P, (degree H p.1 : ℝ) := by push_cast; rfl
    _ ≤ _ := hlem
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hcyc hab.2
      linarith

lemma pairwise_or {α : Type*} {R : α → α → Prop} :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a
  | [], _ => by simp
  | x :: l, h => by
    rw [List.pairwise_cons] at h
    intro a ha b hb hab
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · subst ha; exact Or.inl (h.1 b hb)
    · subst hb; exact Or.inr (h.1 a ha)
    · exact pairwise_or l h.2 a ha b hb hab

/-- The real-valued form of the exploration bound. -/
lemma exploration_le_real (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) :
    (exploration G k : ℝ) ≤ (Nat.log 2 n : ℝ) *
      (pairQuadraticCoefficient k * (n : ℝ) ^ 2 +
        pairCycleCoefficient k * (cycleCount G k : ℝ)) := by
  classical
  obtain ⟨hspec1, hspec2⟩ := roundsAux_spec G n Finset.univ
  set L := rounds G with hL
  have hspec1' : ∀ p ∈ L, p.1 ⊆ Finset.univ ∧ p.2 ∈ p.1 ∧
      (∀ v ∈ p.1, (neighbors G p.1 v).card ≤ (neighbors G p.1 p.2).card) ∧
      2 ≤ (neighbors G p.1 p.2).card := hspec1
  have hspec2' : L.Pairwise (fun p q => q.1 ⊆ p.1.erase p.2) := hspec2
  have hnodup : L.Nodup := by
    refine hspec2'.imp_of_mem ?_
    intro a b ha _ hab heq
    subst heq
    have := hab (hspec1' a ha).2.1
    rw [Finset.mem_erase] at this
    exact this.1 rfl
  set S := L.toFinset with hS
  have hS1 : ∀ p ∈ S, p.2 ∈ p.1 ∧
      (∀ v ∈ p.1, (neighbors G p.1 v).card ≤ (neighbors G p.1 p.2).card) ∧
      2 ≤ (neighbors G p.1 p.2).card := by
    intro p hp
    rw [hS, List.mem_toFinset] at hp
    exact (hspec1' p hp).2
  have hS2 : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → q.1 ⊆ p.1.erase p.2 ∨ p.1 ⊆ q.1.erase q.2 := by
    intro p hp q hq hpq
    rw [hS, List.mem_toFinset] at hp hq
    exact pairwise_or L hspec2' p hp q hq hpq
  set f : Finset (Fin n) × Fin n → ℕ := fun p =>
    ∑ v ∈ ball G p.1 p.2 (k - 1), (neighbors G p.1 v).card with hf
  set g : Finset (Fin n) × Fin n → ℕ := fun p => Nat.log 2 (neighbors G p.1 p.2).card with hg
  have hexp : exploration G k = ∑ p ∈ S, f p := by
    rw [hS, List.sum_toFinset f hnodup]
    rfl
  have hmaps : ∀ p ∈ S, g p ∈ Finset.Icc 1 (Nat.log 2 n) := by
    intro p hp
    obtain ⟨_, _, hdeg⟩ := hS1 p hp
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.log_pos (by norm_num) hdeg
    · apply Nat.log_mono_right
      calc (neighbors G p.1 p.2).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
        _ = n := Fintype.card_fin n
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [hexp, ← hfib]
  push_cast
  calc (∑ j ∈ Finset.Icc 1 (Nat.log 2 n), ∑ p ∈ S with g p = j, (f p : ℝ))
      ≤ ∑ j ∈ Finset.Icc 1 (Nat.log 2 n), (pairQuadraticCoefficient k * (n : ℝ) ^ 2 +
          pairCycleCoefficient k * (cycleCount G k : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        have := bucket_bound k hk G S hS1 hS2 j
        rw [Nat.cast_sum] at this
        exact this
    _ = _ := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

end L33Aux

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      exploration G k ≤ C * (n ^ 2 + cycleCount G k) * logarithmicSize n := by
  set a := pairQuadraticCoefficient k with ha
  set b := pairCycleCoefficient k with hb
  obtain ⟨ha0, hb0⟩ := L33Aux.coeffs_nonneg k
  refine ⟨⌈a⌉₊ + ⌈b⌉₊, fun n G => ?_⟩
  have hreal := L33Aux.exploration_le_real k hk G
  have hlog : Nat.log 2 n ≤ logarithmicSize n := by
    unfold logarithmicSize
    rw [Nat.log2_eq_log_two]
    have := Nat.log_mono_right (b := 2) (le_max_right 2 n)
    omega
  have hlogR : (Nat.log 2 n : ℝ) ≤ (logarithmicSize n : ℝ) := by exact_mod_cast hlog
  have haC : a ≤ ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) := by
    push_cast
    have := Nat.le_ceil a
    have : (0 : ℝ) ≤ (⌈b⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hbC : b ≤ ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) := by
    push_cast
    have := Nat.le_ceil b
    have : (0 : ℝ) ≤ (⌈a⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  set C : ℕ := ⌈a⌉₊ + ⌈b⌉₊ with hC
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have ht : (0 : ℝ) ≤ (cycleCount G k : ℝ) := Nat.cast_nonneg _
  have hB0 : 0 ≤ a * (n : ℝ) ^ 2 + b * (cycleCount G k : ℝ) := by positivity
  have hBC : a * (n : ℝ) ^ 2 + b * (cycleCount G k : ℝ) ≤
      (C : ℝ) * ((n : ℝ) ^ 2 + (cycleCount G k : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right haC hn2
    have h2 := mul_le_mul_of_nonneg_right hbC ht
    nlinarith
  have hfinal : (exploration G k : ℝ) ≤
      (C : ℝ) * ((n : ℝ) ^ 2 + (cycleCount G k : ℝ)) * (logarithmicSize n : ℝ) := by
    calc (exploration G k : ℝ)
        ≤ (Nat.log 2 n : ℝ) * (a * (n : ℝ) ^ 2 + b * (cycleCount G k : ℝ)) := hreal
      _ ≤ (logarithmicSize n : ℝ) * (a * (n : ℝ) ^ 2 + b * (cycleCount G k : ℝ)) :=
          mul_le_mul_of_nonneg_right hlogR hB0
      _ ≤ (logarithmicSize n : ℝ) * ((C : ℝ) * ((n : ℝ) ^ 2 + (cycleCount G k : ℝ))) :=
          mul_le_mul_of_nonneg_left hBC (Nat.cast_nonneg _)
      _ = _ := by ring
  exact_mod_cast hfinal
