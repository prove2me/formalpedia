-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:23:05.067207+00:00
-- url     : https://prove2.me/submissions/34e9f21e-a4e8-4d80-a15d-1da16f9690fe

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace InitializationProof

variable {N : ℕ} (G : SimpleGraph (Fin N))

abbrev steps (D : ℕ) : ℕ := Nat.clog 2 (max 1 D)

def initial (D : ℕ) (e : Sym2 (Fin N)) : ℝ :=
  if e ∈ G.edgeSet then 1 / (2 : ℝ) ^ steps D else 0

def advance (x : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  if ∀ v ∈ e, load G x v ≤ 1/2 then 2 * x e else x e

def weights (D : ℕ) : ℕ → Sym2 (Fin N) → ℝ
  | 0 => initial G D
  | t+1 => advance G (weights D t)

lemma load_mono {x y : Sym2 (Fin N) → ℝ} (h : ∀ e, x e ≤ y e) (v : Fin N) :
    load G x v ≤ load G y v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_le_sum fun e _ => h e

lemma load_nonneg {x : Sym2 (Fin N) → ℝ} (h : ∀ e, 0 ≤ x e) (v : Fin N) :
    0 ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_nonneg fun e _ => h e

lemma advance_le {x : Sym2 (Fin N) → ℝ} (hx : ∀ e, 0 ≤ x e) (e : Sym2 (Fin N)) :
    x e ≤ advance G x e ∧ advance G x e ≤ 2 * x e := by
  unfold advance
  split_ifs <;> constructor <;> linarith [hx e]

lemma advance_hot {x : Sym2 (Fin N) → ℝ} (v : Fin N) (hv : 1/2 < load G x v) :
    load G (advance G x) v = load G x v := by
  unfold load RandomOrderCRS.fracDegree
  apply sum_congr rfl
  intro e he
  apply if_neg
  intro h
  exact (not_le.mpr hv) (h v ((G.mem_incidenceFinset v e).mp he).2)

lemma advance_feasible {x : Sym2 (Fin N) → ℝ}
    (hx : NonnegativeAssignment G x) (hload : ∀ v, load G x v ≤ 1) :
    NonnegativeAssignment G (advance G x) ∧ ∀ v, load G (advance G x) v ≤ 1 := by
  refine ⟨⟨fun e => (hx.1 e).trans (advance_le G hx.1 e).1, ?_⟩, ?_⟩
  · intro e he
    unfold advance
    split_ifs <;> simp [hx.2 e he]
  · intro v
    by_cases hv : 1/2 < load G x v
    · rw [advance_hot G v hv]; exact hload v
    · have h := load_mono G (fun e => (advance_le G hx.1 e).2) v
      have heq : load G (fun e => 2 * x e) v = 2 * load G x v := by
        simp [load, RandomOrderCRS.fracDegree, mul_sum]
      rw [heq] at h
      linarith [le_of_not_gt hv]

lemma initial_feasible (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    NonnegativeAssignment G (initial G D) ∧ ∀ v, load G (initial G D) v ≤ 1 := by
  have hp : (0 : ℝ) < 2 ^ steps D := by positivity
  refine ⟨⟨fun e => by unfold initial; split_ifs <;> positivity,
    fun e he => by simp [initial,he]⟩, ?_⟩
  intro v
  have heq : load G (initial G D) v = (G.degree v : ℝ) / 2 ^ steps D := by
    unfold load RandomOrderCRS.fracDegree
    calc
      _ = ∑ e ∈ G.incidenceFinset v, 1 / (2 : ℝ) ^ steps D := by
        apply sum_congr rfl
        intro e he
        exact if_pos ((G.mem_incidenceFinset v e).mp he).1
      _ = _ := by simp [div_eq_mul_inv]
  rw [heq, div_le_one hp]
  have h : G.degree v ≤ 2 ^ steps D :=
    (hD v).trans ((le_max_right 1 D).trans (Nat.le_pow_clog (by decide) _))
  exact_mod_cast h

lemma weights_feasible (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (t : ℕ) :
    NonnegativeAssignment G (weights G D t) ∧ ∀ v, load G (weights G D t) v ≤ 1 := by
  induction t with
  | zero => exact initial_feasible G D hD
  | succ t ih => exact advance_feasible G ih.1 ih.2

lemma weights_mono (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (e : Sym2 (Fin N)) :
    Monotone (fun t => weights G D t e) := by
  apply monotone_nat_of_le_succ
  intro t
  exact (advance_le G (weights_feasible G D hD t).1.1 e).1

lemma load_weights_mono (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (v : Fin N) :
    Monotone (fun t => load G (weights G D t) v) := by
  intro s t hst
  exact load_mono G (fun e => weights_mono G D hD e hst) v

lemma edge_le_load (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (e : Sym2 (Fin N)) (he : e ∈ G.edgeSet) (v : Fin N) (hv : v ∈ e) : x e ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact single_le_sum (fun f _ => hx f) ((G.mem_incidenceFinset v e).mpr ⟨he,hv⟩)

lemma final_cover (D : ℕ) (hD : ∀ v, G.degree v ≤ D)
    (e : Sym2 (Fin N)) (he : e ∈ G.edgeSet) :
    ∃ v ∈ e, 1/2 < load G (weights G D (steps D)) v := by
  by_contra hc
  push Not at hc
  have hvalue (t : ℕ) (ht : t ≤ steps D) :
      weights G D t e = (2 : ℝ)^t / 2 ^ steps D := by
    induction t with
    | zero => simp [weights, initial,he]
    | succ t ih =>
      have hact : ∀ v ∈ e, load G (weights G D t) v ≤ 1/2 := by
        intro v hv
        exact (load_weights_mono G D hD v (by omega)).trans (hc v hv)
      rw [weights, advance, if_pos hact, ih (by omega), pow_succ]
      ring
  have hv := hvalue (steps D) le_rfl
  rw [div_self (by positivity)] at hv
  obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
  have hel := edge_le_load G _ (weights_feasible G D hD (steps D)).1.1 _ he u
    (Sym2.mem_mk_left u v)
  have hh := hc u (Sym2.mem_mk_left u v)
  rw [hv] at hel
  linarith

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

lemma cover_bound (x : Sym2 (Fin N) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hc : ∀ e ∈ G.edgeSet, ∃ v ∈ e, 1/2 < load G x v) :
    (optimum G : ℝ) / 4 ≤ totalWeight G x := by
  let pick : G.edgeSet → Fin N := fun e => Classical.choose (hc e.1 e.2)
  have hpick (e : G.edgeSet) : pick e ∈ e.1 ∧ 1/2 < load G x (pick e) :=
    Classical.choose_spec (hc e.1 e.2)
  have hbound (M : Finset G.edgeSet) (hM : SemiStreamMWM.IsMatching G M) :
      (M.card : ℝ) ≤ 4 * totalWeight G x := by
    have hinj : Set.InjOn pick (M : Set G.edgeSet) := by
      intro e he f hf hef
      by_contra hne
      have h := hM e he f hf hne (pick e) (hpick e).1
      exact h (hef ▸ (hpick f).1)
    have hb : (M.card : ℝ) / 2 ≤ ∑ e ∈ M, load G x (pick e) := by
      calc
        _ = ∑ e ∈ M, (1/2 : ℝ) := by simp; ring
        _ ≤ _ := sum_le_sum fun e _ => (hpick e).2.le
    have hs : (∑ e ∈ M, load G x (pick e)) ≤ ∑ v : Fin N, load G x v := by
      rw [← sum_image hinj]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ => load_nonneg G hx v)
    rw [sum_loads G x] at hs
    linarith
  have hnat : optimum G ≤ ⌊4 * totalWeight G x⌋₊ := by
    unfold optimum SemiStreamMWM.mcm
    apply Finset.sup_le
    intro M hM
    apply (Nat.le_floor_iff (by
      exact mul_nonneg (by norm_num) (sum_nonneg fun e _ => hx e))).mpr
    exact hbound M (mem_filter.mp hM).2
  have hnon : 0 ≤ 4 * totalWeight G x :=
    mul_nonneg (by norm_num) (sum_nonneg fun e _ => hx e)
  have hcast : (optimum G : ℝ) ≤ 4 * totalWeight G x :=
    (by exact_mod_cast hnat : (optimum G : ℝ) ≤ (⌊4 * totalWeight G x⌋₊ : ℝ)).trans
      (Nat.floor_le hnon)
  linarith

lemma steps_budget (D : ℕ) : steps D ≤ budget 1 (degreeLog D) := by
  unfold steps budget
  rw [← Real.natCeil_logb_natCast]
  apply Nat.ceil_mono
  rw [one_mul]
  apply le_trans _ (le_max_right 1 (logTwo (max 2 (D : ℝ))))
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast (show 0 < max 1 D by omega)
  · push_cast
    exact max_le (by linarith [le_max_left 2 (D : ℝ)]) (le_max_right 2 _)

lemma pow_steps_le (D : ℕ) : 2 ^ steps D ≤ 2 * max 1 D := by
  by_cases hD : max 1 D = 1
  · simp [steps, hD]
  · have hd : 1 < max 1 D := by omega
    have ha := Nat.clog_pos (by decide : 1 < 2) hd
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hd
    have heq : Nat.clog 2 (max 1 D) = (Nat.clog 2 (max 1 D)).pred + 1 :=
      (Nat.succ_pred_eq_of_pos ha).symm
    unfold steps
    rw [heq, pow_succ]
    omega

lemma final_range (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (e : Sym2 (Fin N))
    (he : e ∈ G.edgeSet) :
    1 / (2 * (max 1 D : ℕ) : ℝ) ≤ weights G D (steps D) e ∧
      weights G D (steps D) e ≤ 1 := by
  have hf := weights_feasible G D hD (steps D)
  constructor
  · have hh : 1 / (2 * (max 1 D : ℕ) : ℝ) ≤ 1 / (2 : ℝ) ^ steps D := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast pow_steps_le D
    have h0 : weights G D 0 e = 1 / (2 : ℝ) ^ steps D := by simp [weights,initial,he]
    rw [← h0] at hh
    exact hh.trans (weights_mono G D hD e (Nat.zero_le _))
  · obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    exact (edge_le_load G _ hf.1.1 _ he u (Sym2.mem_mk_left u v)).trans (hf.2 u)

lemma final_fractional (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    fractional G (weights G D (steps D)) := by
  have hf := weights_feasible G D hD (steps D)
  refine ⟨fun e => ⟨hf.1.1 e, ?_⟩, hf.1.2, hf.2⟩
  by_cases he : e ∈ G.edgeSet
  · exact (final_range G D hD e he).2
  · rw [hf.1.2 e he]; norm_num

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

lemma input_weight (x : Sym2 (Fin N) → ℝ) (ids : Fin N → ℕ) (hi : Function.Injective ids) (v w : Fin N)
    (hvw : G.Adj v w) : (weightInput G ids x v).2 (ids w) = x s(v,w) := by
  unfold weightInput
  simp only
  rw [sum_eq_single w]
  · simp
  · intro z hz hzw
    rw [if_neg]
    exact fun h => hzw (hi h)
  · intro hw
    exact False.elim (hw (by simpa using hvw))

lemma input_load (x : Sym2 (Fin N) → ℝ) (ids : Fin N → ℕ) (hi : Function.Injective ids) (v : Fin N) :
    (∑ j ∈ (weightInput G ids x v).1, (weightInput G ids x v).2 j) = load G x v := by
  change (∑ j ∈ (G.neighborFinset v).image ids, (weightInput G ids x v).2 j) = _
  rw [sum_image (fun a _ b _ h => hi h), load_as_neighbors]
  apply sum_congr rfl
  intro w hw
  exact input_weight G x ids hi v w (by simpa using hw)


structure State where
  id : ℕ
  neighbors : Finset ℕ
  value : ℕ → ℝ

noncomputable def algorithm : Deterministic Bounds (Finset ℕ) (ℕ → ℝ) where
  program := {
    State := State
    Msg := ℕ × ℝ
    rounds := fun k => steps k.degree
    init := fun k id ns _ => ⟨id,ns,fun j => if j ∈ ns then 1/(2 : ℝ)^steps k.degree else 0⟩
    send := fun s => (s.id, ∑ j ∈ s.neighbors, s.value j)
    step := fun s msgs => {s with value := fun j =>
      if (∑ j ∈ s.neighbors, s.value j) ≤ 1/2 ∧
        (∀ m ∈ msgs, m.1 = j → m.2 ≤ 1/2) then 2*s.value j else s.value j}
    out := State.value }
  tape_independent := by intros; rfl

abbrev run (k : Bounds) (ids : Fin N → ℕ) (t : ℕ) : Fin N → State :=
  algorithm.program.run G k ids (neighborIDs G ids) (fun _ _ => false) t

lemma run_correct (k : Bounds) (ids : Fin N → ℕ) (hi : Function.Injective ids) (t : ℕ) :
    ∀ v : Fin N,
      (run G k ids t v).id = ids v ∧
      (run G k ids t v).neighbors = neighborIDs G ids v ∧
      ∀ w, G.Adj v w → (run G k ids t v).value (ids w) = weights G k.degree t s(v,w) := by
  induction t with
  | zero =>
    intro v
    refine ⟨rfl,rfl,?_⟩
    intro w hw
    have hid : ids w ∈ neighborIDs G ids v := by
      apply mem_image.mpr
      exact ⟨w,by simpa using hw,rfl⟩
    change (if ids w ∈ neighborIDs G ids v then _ else 0) = initial G k.degree s(v,w)
    rw [if_pos hid,initial,if_pos (G.mem_edgeSet.mpr hw)]
  | succ t ih =>
    have hload (v : Fin N) :
        (∑ j ∈ (run G k ids t v).neighbors, (run G k ids t v).value j) =
          load G (weights G k.degree t) v := by
      rw [(ih v).2.1]
      unfold neighborIDs
      rw [sum_image (fun a _ b _ h => hi h), load_as_neighbors]
      exact sum_congr rfl fun w hw => (ih v).2.2 w (by simpa using hw)
    intro v
    refine ⟨(ih v).1,(ih v).2.1,?_⟩
    intro w hvw
    have hmsg :
        (∀ m ∈ ((univ.filter (G.Adj v)).val.map
          (fun u => ((run G k ids t u).id,
            ∑ j ∈ (run G k ids t u).neighbors, (run G k ids t u).value j))),
          m.1 = ids w → m.2 ≤ 1/2) ↔ load G (weights G k.degree t) w ≤ 1/2 := by
      simp_rw [(fun u => (ih u).1), hload]
      simp only [Multiset.mem_map, mem_val, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        exact h (ids w,load G (weights G k.degree t) w) ⟨w,hvw,rfl⟩ rfl
      · intro h m hm hmj
        obtain ⟨u, hu, rfl⟩ := hm
        exact hi hmj ▸ h
    change (if (∑ j ∈ (run G k ids t v).neighbors, (run G k ids t v).value j) ≤ 1/2 ∧
      (∀ m ∈ ((univ.filter (G.Adj v)).val.map
        (fun u => ((run G k ids t u).id,
          ∑ j ∈ (run G k ids t u).neighbors, (run G k ids t u).value j))),
          m.1 = ids w → m.2 ≤ 1/2)
      then 2 * (run G k ids t v).value (ids w) else (run G k ids t v).value (ids w)) = _
    simp only [hmsg]
    rw [hload, (ih v).2.2 w hvw]
    simp only [weights, advance]
    have hh : (∀ z ∈ s(v,w), load G (weights G k.degree t) z ≤ 1/2) ↔
      load G (weights G k.degree t) v ≤ 1/2 ∧ load G (weights G k.degree t) w ≤ 1/2 := by
      simp [Sym2.mem_iff, or_imp, forall_and]
    simp only [hh]

end InitializationProof


theorem solution :
    ∃ (A : Deterministic Bounds (Finset ℕ) (ℕ → ℝ)) (C : ℝ), 0 < C ∧
      (∀ k, A.program.rounds k ≤ budget C (degreeLog k.degree)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds), boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Function.Injective ids →
          ∃ f : Sym2 (Fin N) → ℝ,
            ReportsWeights G ids (execute A G k ids (neighborIDs G ids)) f ∧
            fractional G f ∧
            (∀ e ∈ G.edgeSet, 1 / (2 * (max 1 k.degree : ℕ) : ℝ) ≤ f e ∧ f e ≤ 1) ∧
            (optimum G : ℝ) / 4 ≤ totalWeight G f := by
  refine ⟨InitializationProof.algorithm,1,by norm_num,
    fun k => InitializationProof.steps_budget k.degree,?_⟩
  intro N G k hG ids hi
  let f := InitializationProof.weights G k.degree (InitializationProof.steps k.degree)
  have hf := InitializationProof.weights_feasible G k.degree hG.2
    (InitializationProof.steps k.degree)
  refine ⟨f,⟨hf.1.2,?_⟩,InitializationProof.final_fractional G k.degree hG.2,
    InitializationProof.final_range G k.degree hG.2,?_⟩
  · intro u v huv
    have he (v w : Fin N) (hvw : G.Adj v w) :
        execute InitializationProof.algorithm G k ids (neighborIDs G ids) v (ids w) = f s(v,w) :=
      (InitializationProof.run_correct G k ids hi (InitializationProof.steps k.degree) v).2.2 w hvw
    exact ⟨he u v huv,by simpa only [Sym2.eq_swap] using he v u huv.symm⟩
  · exact InitializationProof.cover_bound G f hf.1.1
      (InitializationProof.final_cover G k.degree hG.2)
