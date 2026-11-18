-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:16:29.094962+00:00
-- url     : https://prove2.me/submissions/f7cc6ba1-792d-471c-aeb5-a2df1dd793bc

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

namespace CleanupProof

variable {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)

lemma load_nonneg (hx : ∀ e, 0 ≤ x e) (v : Fin N) : 0 ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_nonneg fun e _ => hx e

lemma cleanup_nonneg (hx : ∀ e, 0 ≤ x e) (e : Sym2 (Fin N)) : 0 ≤ cleanup G x e := by
  unfold cleanup
  split_ifs <;> simp_all

lemma cleanup_le (hx : ∀ e, 0 ≤ x e) (e : Sym2 (Fin N)) : cleanup G x e ≤ x e := by
  unfold cleanup
  split_ifs <;> simp_all

lemma load_cleanup_le (hx : ∀ e, 0 ≤ x e) (v : Fin N) :
    load G (cleanup G x) v ≤ load G x v := by
  unfold load RandomOrderCRS.fracDegree
  exact sum_le_sum fun e _ => cleanup_le G x hx e

lemma load_cleanup_hot (v : Fin N) (hv : 1/2 < load G x v) :
    load G (cleanup G x) v = 0 := by
  unfold load RandomOrderCRS.fracDegree
  apply sum_eq_zero
  intro e he
  unfold cleanup
  apply if_pos
  exact ⟨v, (G.mem_incidenceFinset v e).mp he |>.2, hv⟩

lemma cleanup_properties (hx : NonnegativeAssignment G x) :
    NonnegativeAssignment G (cleanup G x) ∧ ∀ v, load G (cleanup G x) v ≤ 1/2 := by
  refine ⟨⟨cleanup_nonneg G x hx.1, ?_⟩, ?_⟩
  · intro e he
    unfold cleanup
    split_ifs <;> simp_all [hx.2 e he]
  · intro v
    by_cases hv : 1/2 < load G x v
    · rw [load_cleanup_hot G x v hv]; norm_num
    · exact (load_cleanup_le G x hx.1 v).trans (le_of_not_gt hv)

lemma load_as_edges (v : Fin N) :
    load G x v = ∑ e ∈ G.edgeFinset, if v ∈ e then x e else 0 := by
  unfold load RandomOrderCRS.fracDegree
  rw [G.incidenceFinset_eq_filter]
  exact sum_filter ..

lemma loss_bound (hx : ∀ e, 0 ≤ x e) :
    totalWeight G x - totalWeight G (cleanup G x) ≤
      ∑ v : Fin N, if 1/2 < load G x v then load G x v else 0 := by
  have eqn : (∑ v : Fin N, if 1/2 < load G x v then load G x v else 0) =
      ∑ e ∈ G.edgeFinset, ∑ v : Fin N,
        if 1/2 < load G x v ∧ v ∈ e then x e else 0 := by
    calc
      _ = ∑ v : Fin N, ∑ e ∈ G.edgeFinset,
          if 1/2 < load G x v ∧ v ∈ e then x e else 0 := by
        apply sum_congr rfl
        intro v _
        by_cases hv : 1/2 < load G x v
        · simp only [hv, if_true, true_and]
          exact load_as_edges G x v
        · simp only [hv, if_false, false_and, sum_const_zero]
      _ = _ := sum_comm
  rw [eqn, totalWeight, totalWeight, ← sum_sub_distrib]
  apply sum_le_sum
  intro e he
  by_cases hhot : ∃ v ∈ e, 1/2 < load G x v
  · obtain ⟨v, hve, hv⟩ := hhot
    rw [cleanup, if_pos ⟨v,hve,hv⟩, sub_zero]
    calc
      x e = (if 1/2 < load G x v ∧ v ∈ e then x e else 0) := (if_pos ⟨hv,hve⟩).symm
      _ ≤ _ := single_le_sum (f := fun w : Fin N =>
        if 1/2 < load G x w ∧ w ∈ e then x e else 0)
        (fun w _ => by split_ifs <;> simp_all) (mem_univ v)
  · rw [cleanup, if_neg hhot, sub_self]
    apply sum_nonneg
    intro v _
    split_ifs <;> simp_all

lemma potential_cleanup (hx : NonnegativeAssignment G x) :
    potential G x ≤ potential G (cleanup G x) := by
  have hpoint (v : Fin N) :
      (if 1/2 < load G x v then load G x v else 0) ≤
        2 * ((load G x v)^2 - (load G (cleanup G x) v)^2) := by
    have hn := load_nonneg G x hx.1 v
    have hnc := load_nonneg G (cleanup G x) (cleanup_nonneg G x hx.1) v
    have hle := load_cleanup_le G x hx.1 v
    by_cases hv : 1/2 < load G x v
    · rw [if_pos hv, load_cleanup_hot G x v hv]
      nlinarith
    · rw [if_neg hv]
      have hs := mul_self_le_mul_self hnc hle
      nlinarith
  have hpen : (∑ v : Fin N, if 1/2 < load G x v then load G x v else 0) ≤
      penalty G x - penalty G (cleanup G x) := by
    calc
      _ ≤ ∑ v : Fin N, 2 * ((load G x v)^2 - (load G (cleanup G x) v)^2) :=
        sum_le_sum fun v _ => hpoint v
      _ = _ := by simp [penalty, mul_sub, sum_sub_distrib, mul_sum]
  have h := loss_bound G x hx.1
  unfold potential
  linarith

lemma load_as_neighbors (v : Fin N) :
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

lemma input_weight (ids : Fin N → ℕ) (hi : Function.Injective ids) (v w : Fin N)
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

lemma input_load (ids : Fin N → ℕ) (hi : Function.Injective ids) (v : Fin N) :
    (∑ j ∈ (weightInput G ids x v).1, (weightInput G ids x v).2 j) = load G x v := by
  change (∑ j ∈ (G.neighborFinset v).image ids, (weightInput G ids x v).2 j) = _
  rw [sum_image (fun a _ b _ h => hi h), load_as_neighbors]
  apply sum_congr rfl
  intro w hw
  exact input_weight G x ids hi v w (by simpa using hw)

structure CleanupState where
  id : ℕ
  weights : ℕ → ℝ
  hot : Prop
  removed : ℕ → Prop

noncomputable def algorithm : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ) where
  program := {
    State := CleanupState
    Msg := ℕ × Prop
    rounds := fun _ => 1
    init := fun _ id inp _ => ⟨id, inp.2, 1/2 < ∑ j ∈ inp.1, inp.2 j, fun _ => False⟩
    send := fun s => (s.id,s.hot)
    step := fun s msgs => {s with removed := fun j =>
      s.hot ∨ ∃ m ∈ msgs, m.1 = j ∧ m.2}
    out := fun s j => if s.removed j then 0 else s.weights j }
  tape_independent := by intros; rfl

lemma algorithm_edge (ids : Fin N → ℕ) (hi : Function.Injective ids) (v w : Fin N)
    (hvw : G.Adj v w) :
    execute algorithm G () ids (weightInput G ids x) v (ids w) = cleanup G x s(v,w) := by
  have hmem : (∃ m ∈ ((univ.filter (G.Adj v)).val.map fun u =>
      (ids u, 1/2 < load G x u)), m.1 = ids w ∧ m.2) ↔ 1/2 < load G x w := by
    simp only [Multiset.mem_map, mem_val, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨m, ⟨u, hu, rfl⟩, heq, hot⟩
      exact hi heq ▸ hot
    · intro hot
      exact ⟨(ids w, 1/2 < load G x w), ⟨w,hvw,rfl⟩, rfl,hot⟩
  unfold execute SmoothedMIS.LocalAlg.output
  simp only [algorithm, SmoothedMIS.LocalAlg.run]
  change (if (1/2 < ∑ j ∈ (weightInput G ids x v).1, (weightInput G ids x v).2 j) ∨
    (∃ m ∈ ((univ.filter (G.Adj v)).val.map fun u =>
      (ids u, 1/2 < ∑ j ∈ (weightInput G ids x u).1, (weightInput G ids x u).2 j)),
      m.1 = ids w ∧ m.2) then 0 else (weightInput G ids x v).2 (ids w)) = _
  simp_rw [input_load G x ids hi]
  rw [hmem, input_weight G x ids hi v w hvw]
  unfold cleanup
  have hh : (∃ z ∈ s(v,w), 1/2 < load G x z) ↔
      (1/2 < load G x v ∨ 1/2 < load G x w) := by
    simp only [Sym2.mem_iff]
    aesop
  simp only [hh]

end CleanupProof


theorem solution :
    ∃ (A : Deterministic Unit (Finset ℕ × (ℕ → ℝ)) (ℕ → ℝ)) (T : ℕ),
      A.program.rounds () ≤ T ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ),
        NonnegativeAssignment G x → ∀ ids : Fin N → ℕ, Function.Injective ids →
          ReportsWeights G ids (execute A G () ids (weightInput G ids x)) (cleanup G x) ∧
          NonnegativeAssignment G (cleanup G x) ∧
          (∀ v, load G (cleanup G x) v ≤ 1 / 2) ∧
          potential G x ≤ potential G (cleanup G x) := by
  refine ⟨CleanupProof.algorithm, 1, le_rfl, ?_⟩
  intro N G x hx ids hi
  have hp := CleanupProof.cleanup_properties G x hx
  refine ⟨⟨hp.1.2, ?_⟩, hp.1, hp.2, CleanupProof.potential_cleanup G x hx⟩
  intro u v huv
  refine ⟨CleanupProof.algorithm_edge G x ids hi u v huv, ?_⟩
  simpa only [Sym2.eq_swap] using CleanupProof.algorithm_edge G x ids hi v u huv.symm
