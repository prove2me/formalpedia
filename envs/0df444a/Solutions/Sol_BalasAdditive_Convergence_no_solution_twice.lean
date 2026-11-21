-- Prove2me | solution 1 for BalasAdditive.Convergence.no_solution_twice
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T04:47:58.740012+00:00
-- url     : https://prove2.me/submissions/7caacb7e-e324-483e-87af-8c682515363b

import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence.NoDupAux

open BalasAdditive.Convergence
open Classical

/-- Nonemptiness of `equalityF` when all negative-slack row inequalities hold
with at least one equality. -/
private theorem equalityF_nonempty {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n))
    (hhold : relationsHold P J X) (hnonstrict : ¬ relationsStrict P J X) :
    (equalityF P J X).Nonempty := by
  simp only [relationsStrict, not_forall] at hnonstrict
  obtain ⟨i, hslack, hnotlt⟩ := hnonstrict
  have hle := hhold i hslack
  have heq : negativeSum P X i = P.lp.slack J i := le_antisymm hle (not_lt.mp hnotlt)
  have hsum_lt : ∑ j ∈ X, min (P.lp.A i j) 0 < 0 := by
    change negativeSum P X i < 0
    linarith
  have hex : ∃ j ∈ X, min (P.lp.A i j) 0 < 0 := by
    by_contra h
    have hnonneg : (0 : ℝ) ≤ ∑ j ∈ X, min (P.lp.A i j) 0 :=
      Finset.sum_nonneg fun j hj => not_lt.mp fun hlt => h ⟨j, hj, hlt⟩
    linarith
  obtain ⟨j, hjX, hjmin⟩ := hex
  have hjA : P.lp.A i j < 0 := by
    rcases min_cases (P.lp.A i j) 0 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  exact ⟨j, Finset.mem_filter.mpr ⟨hjX, i, hslack, heq, hjA⟩⟩

private theorem equalityF_subset {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n)) :
    equalityF P J X ⊆ X :=
  Finset.filter_subset _ _

private theorem currentC_cancelAt_self {n : ℕ} (cs : List (Finset (Fin n))) (p : ℕ)
    (X : Finset (Fin n)) (hp : p < cs.length) :
    ((cancelAt cs p X)[p]?).getD ∅ = (cs[p]?).getD ∅ ∪ X := by
  simp [cancelAt, List.getElem?_set_self hp, List.getElem?_eq_getElem hp]

private theorem currentC_cancelAt_ne {n : ℕ} (cs : List (Finset (Fin n))) (p q : ℕ)
    (X : Finset (Fin n)) (hne : p ≠ q) :
    ((cancelAt cs p X)[q]?).getD ∅ = (cs[q]?).getD ∅ := by
  simp [cancelAt, List.getElem?_set_ne hne]

private theorem length_cancelAt {n : ℕ} (cs : List (Finset (Fin n))) (p : ℕ)
    (X : Finset (Fin n)) :
    (cancelAt cs p X).length = cs.length := by
  simp [cancelAt]

private theorem subset_cancelAt {n : ℕ} (cs : List (Finset (Fin n))) (p q : ℕ)
    (X : Finset (Fin n)) :
    (cs[q]?).getD ∅ ⊆ ((cancelAt cs p X)[q]?).getD ∅ := by
  by_cases h : p = q
  · subst h
    by_cases hp : p < cs.length
    · rw [currentC_cancelAt_self cs p X hp]
      exact Finset.subset_union_left
    · have hge : cs.length ≤ p := Nat.le_of_not_lt hp
      simp [cancelAt, List.set_eq_of_length_le hge]
  · rw [currentC_cancelAt_ne cs p q X h]

private theorem cancelOldD_spec {n m : ℕ} (P : Problem n m) (σ : State n) :
    (cancelOldD P σ).length = σ.cancelled.length ∧
    (∀ q : ℕ, (σ.cancelled[q]?).getD ∅ ⊆ ((cancelOldD P σ)[q]?).getD ∅) ∧
    (∀ q : ℕ, q < σ.history.length - 1 → σ.cancelled.length = σ.history.length →
      ((cancelOldD P σ)[q]?).getD ∅ ⊆ (σ.cancelled[q]?).getD ∅ ∪ oldD P σ q) := by
  unfold cancelOldD
  generalize hks : (Finset.range (σ.history.length - 1)).toList = ks
  have hnodup : ∀ l : List ℕ, l.Nodup → ∀ cs : List (Finset (Fin n)),
      (l.foldl (fun cs k => cancelAt cs k (oldD P σ k)) cs).length = cs.length ∧
      (∀ q : ℕ, (cs[q]?).getD ∅ ⊆
        ((l.foldl (fun cs k => cancelAt cs k (oldD P σ k)) cs)[q]?).getD ∅) ∧
      (∀ q : ℕ, cs.length = σ.history.length → q < σ.history.length - 1 →
        ((l.foldl (fun cs k => cancelAt cs k (oldD P σ k)) cs)[q]?).getD ∅ ⊆
          (cs[q]?).getD ∅ ∪
            (if q ∈ l then oldD P σ q else (∅ : Finset (Fin n)))) := by
    intro l hl
    induction l with
    | nil =>
      intro cs
      simp
    | cons k rest ih =>
      obtain ⟨hk_notin, hrest⟩ := List.nodup_cons.mp hl
      intro cs
      set cs' := cancelAt cs k (oldD P σ k)
      have hlen' : cs'.length = cs.length := length_cancelAt cs k _
      obtain ⟨ih1, ih2, ih3⟩ := ih hrest cs'
      refine ⟨ih1.trans hlen', ?_, ?_⟩
      · intro q
        exact (subset_cancelAt cs k q _).trans (ih2 q)
      · intro q hcs hq
        have hstep := ih3 q (hlen'.trans hcs) hq
        refine hstep.trans ?_
        by_cases hkq : k = q
        · subst hkq
          have hq_len : k < cs.length := by omega
          have hcs'_eq : (cs'[k]?).getD ∅ = (cs[k]?).getD ∅ ∪ oldD P σ k :=
            currentC_cancelAt_self cs k _ hq_len
          simp [hcs'_eq, hk_notin]
        · have hcs'_eq : (cs'[q]?).getD ∅ = (cs[q]?).getD ∅ :=
            currentC_cancelAt_ne cs k q _ hkq
          by_cases hqrest : q ∈ rest
          · simp [hcs'_eq, hqrest, Ne.symm hkq]
          · simp [hcs'_eq, hqrest, Ne.symm hkq]
  have hks_nodup : ks.Nodup := by
    rw [← hks]
    exact Finset.nodup_toList _
  obtain ⟨h1, h2, h3⟩ := hnodup ks hks_nodup σ.cancelled
  refine ⟨h1, h2, ?_⟩
  intro q hq hcs
  refine (h3 q hcs hq).trans ?_
  by_cases hmem : q ∈ ks <;> simp [hmem]

/-- Ancestor relation in a parent function `par` satisfying `par q < q` for `q > 0`. -/
private inductive Anc (par : ℕ → ℕ) (u : ℕ) : ℕ → Prop where
  | refl : Anc par u u
  | step {v : ℕ} (hv : 0 < v) (h : Anc par u (par v)) : Anc par u v

private theorem anc_le {par : ℕ → ℕ} (hpar : ∀ q > 0, par q < q) {u v : ℕ}
    (h : Anc par u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | @step v hv _ ih => exact ih.trans (Nat.le_of_lt (hpar v hv))

private theorem anc_zero {par : ℕ → ℕ} (hpar : ∀ q > 0, par q < q) :
    ∀ v : ℕ, Anc par 0 v := by
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · exact Anc.refl
    · exact Anc.step hv (ih (par v) (hpar v hv))

private theorem anc_first_step {par : ℕ → ℕ} {w u : ℕ}
    (h : Anc par w u) (hne : w ≠ u) :
    ∃ u₁ : ℕ, 0 < u₁ ∧ par u₁ = w ∧ Anc par u₁ u := by
  induction h with
  | refl => exact absurd rfl hne
  | @step v hv _ ih =>
    by_cases hw : w = par v
    · exact ⟨v, hv, hw.symm, Anc.refl⟩
    · obtain ⟨u₁, hu₁_pos, hu₁_par, hu₁_anc⟩ := ih hw
      exact ⟨u₁, hu₁_pos, hu₁_par, Anc.step hv hu₁_anc⟩

/-- Structural state invariant preserved along `Reachable P σ`. -/
private structure TreeInv {n m : ℕ} (P : Problem n m) (σ : State n) : Prop where
  hlen_pos : 0 < σ.history.length
  hcanc_len : σ.cancelled.length = σ.history.length
  hJ0 : σ.J 0 = ∅
  hphase_start : σ.phase = .start →
    (∀ q < σ.history.length, σ.currentC q = σ.snapshotC q) ∧
    σ.currentC (σ.history.length - 1) = ∅
  hphase_scan : ∀ bound, σ.phase = .scan bound →
    bound ≤ σ.history.length - 1 ∧
    ∀ q < bound, σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
  tree : ∃ (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n)),
    (∀ q > 0, par q < q) ∧
    (∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧
      (edgeX q).Nonempty ∧
      edgeX q ⊆ σ.N (par q) ∧
      Disjoint (edgeX q) (σ.J (par q)) ∧
      edgeX q ⊆ σ.currentC (par q) ∧
      (∀ r, q ≤ r → r < σ.history.length →
        σ.J (par q) ⊂ σ.J r → Disjoint (σ.N r) (edgeX q)) ∧
      (∀ r, q < r → r < σ.history.length →
        par r = par q → Disjoint (edgeX r) (edgeX q)))

private theorem treeInv_init {n m : ℕ} (P : Problem n m) : TreeInv P (init P) := by
  refine
    { hlen_pos := by simp [init]
      hcanc_len := by simp [init]
      hJ0 := by simp [init, State.J]
      hphase_start := ?_
      hphase_scan := by intro bound h; simp [init] at h
      tree := ⟨fun _ => 0, fun _ => ∅, fun q hq => hq, fun q hq0 hq1 => by simp [init] at hq1; omega⟩ }
  intro _
  refine ⟨?_, by simp [init, State.currentC]⟩
  intro q hq
  simp [init] at hq
  subst hq
  simp [init, State.currentC, State.snapshotC]

private theorem anc_subset_J {n : ℕ} (σ : State n) (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q)
    (hstep : ∀ q, 0 < q → q < σ.history.length → σ.J q = σ.J (par q) ∪ edgeX q)
    {u v : ℕ} (hv : v < σ.history.length) (h : Anc par u v) :
    σ.J u ⊆ σ.J v := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step w hw _ ih =>
    have hpar_lt : par w < σ.history.length := lt_trans (hpar w hw) hv
    rw [hstep w hw hv]
    exact (ih hpar_lt).trans Finset.subset_union_left

private theorem anc_ssubset_J {n : ℕ} (σ : State n) (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q)
    (hstep : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)))
    {u v : ℕ} (hv : v < σ.history.length) (h : Anc par u v) (hne : u ≠ v) :
    σ.J u ⊂ σ.J v := by
  cases h with
  | refl => exact absurd rfl hne
  | step hw hprev =>
    have hpar_lt : par v < σ.history.length := lt_trans (hpar v hw) hv
    have hsub : σ.J u ⊆ σ.J (par v) :=
      anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep q h0 h1).1) hpar_lt hprev
    obtain ⟨heq, ⟨x, hx⟩, hdisj⟩ := hstep v hw hv
    have hss : σ.J (par v) ⊂ σ.J v := by
      rw [heq, Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, ?_⟩
      intro heq'
      have hx_in : x ∈ σ.J (par v) := by
        have : x ∈ σ.J (par v) ∪ edgeX v := Finset.mem_union_right _ hx
        rwa [← heq'] at this
      exact Finset.disjoint_left.mp hdisj hx hx_in
    exact lt_of_le_of_lt hsub hss

/-- Every element of `σ.J p` comes from `edgeX q` for some `0 < q ≤ p` with `σ.J (par q) ⊂ σ.J p`. -/
private theorem mem_J_origin {n : ℕ} (σ : State n) (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q) (hJ0 : σ.J 0 = ∅)
    (hstep : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q))) :
    ∀ p < σ.history.length, ∀ x ∈ σ.J p,
      ∃ q, 0 < q ∧ q ≤ p ∧ σ.J (par q) ⊂ σ.J p ∧ x ∈ edgeX q := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp x hx
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp [hJ0] at hx
    · obtain ⟨heq, _, _⟩ := hstep p hp0 hp
      have hss_p : σ.J (par p) ⊂ σ.J p :=
        anc_ssubset_J σ par edgeX hpar hstep hp (Anc.step hp0 Anc.refl)
          (Nat.ne_of_lt (hpar p hp0))
      rw [heq] at hx
      rcases Finset.mem_union.mp hx with hx_par | hx_edge
      · have hpar_lt : par p < p := hpar p hp0
        obtain ⟨q, hq0, hqle, hss, hxq⟩ := ih (par p) hpar_lt (lt_trans hpar_lt hp) x hx_par
        exact ⟨q, hq0, hqle.trans (Nat.le_of_lt hpar_lt), hss.trans hss_p, hxq⟩
      · exact ⟨p, hp0, le_rfl, hss_p, hx_edge⟩

/-- Helper to advance `TreeInv` across any `appendSolution P σ p X X` step. -/
private theorem treeInv_appendSolution {n m : ℕ} (P : Problem n m) (σ : State n)
    (hinv : TreeInv P σ) (p : ℕ) (hp : p < σ.history.length) (X : Finset (Fin n))
    (hX_ne : X.Nonempty) (hX_sub : X ⊆ σ.N p) (hX_disj_curr : Disjoint X (σ.currentC p)) :
    TreeInv P (appendSolution P σ p X X) := by
  set τ := appendSolution P σ p X X
  set L := σ.history.length
  obtain ⟨par, edgeX, hpar, htree⟩ := hinv.tree
  have hstep_basic : ∀ q, 0 < q → q < L →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)) :=
    fun q h0 h1 => ⟨(htree q h0 h1).1, (htree q h0 h1).2.1, (htree q h0 h1).2.2.2.1⟩
  have hX_disj_Jp : Disjoint X (σ.J p) := by
    rw [Finset.disjoint_left]
    intro x hxX hxJp
    obtain ⟨q, hq0, hqle, hss, hxq⟩ :=
      mem_J_origin σ par edgeX hpar hinv.hJ0 hstep_basic p hp x hxJp
    have hdisj_N : Disjoint (σ.N p) (edgeX q) :=
      (htree q hq0 (lt_of_le_of_lt hqle hp)).2.2.2.2.2.1 p hqle hp hss
    exact Finset.disjoint_left.mp hdisj_N (hX_sub hxX) hxq
  have hJp_ss : σ.J p ⊂ σ.J p ∪ X := by
    obtain ⟨x, hx⟩ := hX_ne
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_union_left, ?_⟩
    intro heq
    have hxJp : x ∈ σ.J p := by
      have : x ∈ σ.J p ∪ X := Finset.mem_union_right _ hx
      rwa [← heq] at this
    exact Finset.disjoint_left.mp hX_disj_Jp hx hxJp
  have hτ_len : τ.history.length = L + 1 := by simp [τ, appendSolution, L]
  have hcs_len : (cancelAt σ.cancelled p X).length = L := by
    rw [length_cancelAt, hinv.hcanc_len]
  have hτ_canc_len : τ.cancelled.length = τ.history.length := by
    simp [τ, appendSolution, hcs_len, L]
  have hτ_J_old : ∀ q < L, τ.J q = σ.J q := by
    intro q hq
    simp [τ, appendSolution, State.J, List.getElem?_append_left hq]
  have hτ_J_new : τ.J L = σ.J p ∪ X := by
    simp [τ, appendSolution, State.J, L]
  have hτ_N_old : ∀ q < L, τ.N q = σ.N q := by
    intro q hq
    simp [τ, appendSolution, State.N, List.getElem?_append_left hq]
  have hτ_N_new : τ.N L = newN P σ.history (cancelAt σ.cancelled p X) (σ.J p ∪ X) := by
    simp [τ, appendSolution, State.N, L]
  have hτ_curr_old : ∀ q < L, τ.currentC q = ((cancelAt σ.cancelled p X)[q]?).getD ∅ := by
    intro q hq
    have hq' : q < (cancelAt σ.cancelled p X).length := by omega
    simp [τ, appendSolution, State.currentC, List.getElem?_append_left hq']
  have hτ_curr_new : τ.currentC L = ∅ := by
    have hL' : L = (cancelAt σ.cancelled p X).length := hcs_len.symm
    simp [τ, appendSolution, State.currentC, hL']
  let par' : ℕ → ℕ := fun q => if q = L then p else if q < L then par q else 0
  let edgeX' : ℕ → Finset (Fin n) := fun q => if q = L then X else edgeX q
  have hL_pos : 0 < L := hinv.hlen_pos
  have hpar' : ∀ q > 0, par' q < q := by
    intro q hq
    dsimp [par']
    split_ifs with h1 h2
    · subst h1; exact hp
    · exact hpar q hq
    · exact hq
  have hnewN_disj : ∀ w < L, σ.J w ⊂ σ.J p ∪ X →
      ∀ S : Finset (Fin n), S ⊆ ((cancelAt σ.cancelled p X)[w]?).getD ∅ →
      Disjoint (τ.N L) S := by
    intro w hw hss S hS
    rw [hτ_N_new, Finset.disjoint_left]
    intro j hjN hjS
    have hj_not_inh : j ∉ inheritedC σ.history (cancelAt σ.cancelled p X) (σ.J p ∪ X) :=
      (Finset.mem_filter.mp hjN).2.1
    apply hj_not_inh
    unfold inheritedC
    rw [Finset.mem_biUnion]
    refine ⟨w, Finset.mem_range.mpr hw, ?_⟩
    have hJw : ((σ.history[w]?).map Record.J).getD ∅ = σ.J w := rfl
    rw [hJw, if_pos hss]
    exact hS hjS
  refine
    { hlen_pos := by omega
      hcanc_len := hτ_canc_len
      hJ0 := by rw [hτ_J_old 0 hL_pos, hinv.hJ0]
      hphase_start := ?_
      hphase_scan := by intro bound h; simp [τ, appendSolution] at h
      tree := ⟨par', edgeX', hpar', ?_⟩ }
  · intro _
    refine ⟨?_, ?_⟩
    · intro q _
      simp [τ, appendSolution, State.currentC, State.snapshotC]
    · have hlast : τ.history.length - 1 = L := by omega
      rw [hlast]
      exact hτ_curr_new
  · intro q hq0 hq_len
    have hq_le : q ≤ L := by omega
    rcases Nat.lt_or_eq_of_le hq_le with hqL | rfl
    · have hpar_q_lt : par q < L := lt_trans (hpar q hq0) hqL
      have hpar'_q : par' q = par q := by simp [par', Nat.ne_of_lt hqL, hqL]
      have hedgeX'_q : edgeX' q = edgeX q := by simp [edgeX', Nat.ne_of_lt hqL]
      rw [hpar'_q, hedgeX'_q, hτ_J_old q hqL, hτ_J_old (par q) hpar_q_lt, hτ_N_old (par q) hpar_q_lt]
      obtain ⟨h1, h2, hsubN, h3, h4, h5, h6⟩ := htree q hq0 hqL
      refine ⟨h1, h2, hsubN, h3, ?_, ?_, ?_⟩
      · rw [hτ_curr_old (par q) hpar_q_lt]
        exact h4.trans (subset_cancelAt σ.cancelled p (par q) X)
      · intro r hqr hr_len hss_r
        have hr_le : r ≤ L := by omega
        rcases Nat.lt_or_eq_of_le hr_le with hrL | rfl
        · rw [hτ_J_old r hrL] at hss_r
          rw [hτ_N_old r hrL]
          exact h5 r hqr hrL hss_r
        · rw [hτ_J_new] at hss_r
          exact hnewN_disj (par q) hpar_q_lt hss_r (edgeX q)
            (h4.trans (subset_cancelAt σ.cancelled p (par q) X))
      · intro r hqr hr_len hpar_eq
        have hr_le : r ≤ L := by omega
        rcases Nat.lt_or_eq_of_le hr_le with hrL | rfl
        · have hpar'_r : par' r = par r := by simp [par', Nat.ne_of_lt hrL, hrL]
          have hedgeX'_r : edgeX' r = edgeX r := by simp [edgeX', Nat.ne_of_lt hrL]
          rw [hpar'_r] at hpar_eq
          rw [hedgeX'_r]
          exact h6 r hqr hrL hpar_eq
        · have hpar'_L : par' L = p := by simp [par']
          have hedgeX'_L : edgeX' L = X := by simp [edgeX']
          rw [hpar'_L] at hpar_eq
          rw [hedgeX'_L]
          subst hpar_eq
          exact hX_disj_curr.mono_right h4
    · have hpar'_L : par' L = p := by simp [par']
      have hedgeX'_L : edgeX' L = X := by simp [edgeX']
      rw [hpar'_L, hedgeX'_L, hτ_J_new, hτ_J_old p hp, hτ_N_old p hp]
      have hp_canc : p < σ.cancelled.length := hinv.hcanc_len.symm ▸ hp
      have hX_in_cs : X ⊆ ((cancelAt σ.cancelled p X)[p]?).getD ∅ := by
        rw [currentC_cancelAt_self σ.cancelled p X hp_canc]
        exact Finset.subset_union_right
      refine ⟨rfl, hX_ne, hX_sub, hX_disj_Jp, ?_, ?_, ?_⟩
      · rw [hτ_curr_old p hp]
        exact hX_in_cs
      · intro r hLr hr_len hss_r
        have hr_eq : r = L := by omega
        subst hr_eq
        rw [hτ_J_new] at hss_r
        exact hnewN_disj p hp hss_r X hX_in_cs
      · intro r hLr hr_len
        omega

/-- Helper to advance `TreeInv` across non-appending transitions (`beginScan` / `stop`). -/
private theorem treeInv_nonAppend {n m : ℕ} (P : Problem n m) (σ τ : State n)
    (hinv : TreeInv P σ) (hhist : τ.history = σ.history)
    (hcanc_len : τ.cancelled.length = σ.cancelled.length)
    (hcanc_mono : ∀ q, σ.currentC q ⊆ τ.currentC q)
    (hstart : τ.phase ≠ .start)
    (hscan : ∀ bound, τ.phase = .scan bound →
      bound ≤ τ.history.length - 1 ∧
      ∀ q < bound, τ.currentC q ⊆ τ.snapshotC q ∪ oldD P τ q) :
    TreeInv P τ := by
  have hJ : ∀ q, τ.J q = σ.J q := fun q => by simp [State.J, hhist]
  have hN : ∀ q, τ.N q = σ.N q := fun q => by simp [State.N, hhist]
  obtain ⟨par, edgeX, hpar, htree⟩ := hinv.tree
  refine
    { hlen_pos := by rw [hhist]; exact hinv.hlen_pos
      hcanc_len := by rw [hcanc_len, hinv.hcanc_len, hhist]
      hJ0 := by rw [hJ 0, hinv.hJ0]
      hphase_start := fun h => absurd h hstart
      hphase_scan := hscan
      tree := ⟨par, edgeX, hpar, ?_⟩ }
  intro q hq0 hq_len
  rw [hhist] at hq_len
  obtain ⟨h1, h2, hsubN, h3, h4, h5, h6⟩ := htree q hq0 hq_len
  refine ⟨by rw [hJ, hJ]; exact h1, h2, by rw [hN]; exact hsubN,
    by rw [hJ]; exact h3, h4.trans (hcanc_mono _), ?_, ?_⟩
  · intro r hqr hr_len hss
    rw [hhist] at hr_len
    rw [hJ, hJ] at hss
    rw [hN]
    exact h5 r hqr hr_len hss
  · intro r hqr hr_len hpar_eq
    rw [hhist] at hr_len
    exact h6 r hqr hr_len hpar_eq

private theorem treeInv_step {n m : ℕ} (P : Problem n m) {σ τ : State n}
    (hinv : TreeInv P σ) (hs : Step P σ τ) : TreeInv P τ := by
  have hL_pos := hinv.hlen_pos
  cases hs with
  | one_a hph _ =>
    obtain ⟨hc1, hc2, hc3⟩ := cancelOldD_spec P σ
    obtain ⟨hstart_eq, _⟩ := hinv.hphase_start hph
    refine treeInv_nonAppend P σ _ hinv rfl hc1 (fun q => hc2 q) (by simp [beginScan]) ?_
    intro bound hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨le_rfl, ?_⟩
    intro q hq
    have hq_lt : q < σ.history.length := by omega
    have hsub := hc3 q hq hinv.hcanc_len
    have hsnap : (beginScan σ (cancelOldD P σ) (σ.history.length - 1)).snapshotC q = σ.snapshotC q := rfl
    have holdD : oldD P (beginScan σ (cancelOldD P σ) (σ.history.length - 1)) q = oldD P σ q := rfl
    rw [hsnap, holdD]
    have hcurr : (beginScan σ (cancelOldD P σ) (σ.history.length - 1)).currentC q =
        ((cancelOldD P σ)[q]?).getD ∅ := rfl
    rw [hcurr]
    exact hsub.trans (by rw [← hstart_eq q hq_lt]; rfl)
  | two_a hph _ _ =>
    obtain ⟨hstart_eq, _⟩ := hinv.hphase_start hph
    refine treeInv_nonAppend P σ _ hinv rfl rfl (fun _ => Finset.Subset.refl _) (by simp [beginScan]) ?_
    intro bound hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨le_rfl, ?_⟩
    intro q hq
    have hq_lt : q < σ.history.length := by omega
    change σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
    rw [hstart_eq q hq_lt]
    exact Finset.subset_union_left
  | three_a hph _ _ _ =>
    obtain ⟨hstart_eq, _⟩ := hinv.hphase_start hph
    refine treeInv_nonAppend P σ _ hinv rfl rfl (fun _ => Finset.Subset.refl _) (by simp [beginScan]) ?_
    intro bound hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨le_rfl, ?_⟩
    intro q hq
    have hq_lt : q < σ.history.length := by omega
    change σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
    rw [hstart_eq q hq_lt]
    exact Finset.subset_union_left
  | three_b j hph _ _ _ hchoice =>
    obtain ⟨_, hcurr_last⟩ := hinv.hphase_start hph
    refine treeInv_appendSolution P σ hinv (σ.history.length - 1) (by omega) {j}
      (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.mpr hchoice.1) ?_
    rw [hcurr_last]
    exact Finset.disjoint_empty_right _
  | four_a hph _ _ hhold hnonstrict _ =>
    obtain ⟨_, hcurr_last⟩ := hinv.hphase_start hph
    refine treeInv_appendSolution P σ hinv (σ.history.length - 1) (by omega)
      (equalityF P σ.latest (σ.N (σ.history.length - 1)))
      (equalityF_nonempty P σ.latest _ hhold hnonstrict)
      (equalityF_subset P σ.latest _) ?_
    rw [hcurr_last]
    exact Finset.disjoint_empty_right _
  | four_b hph _ _ _ _ _ =>
    obtain ⟨hstart_eq, _⟩ := hinv.hphase_start hph
    refine treeInv_nonAppend P σ _ hinv rfl (length_cancelAt _ _ _)
      (fun q => subset_cancelAt _ _ q _) (by simp [beginScan]) ?_
    intro bound hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨le_rfl, ?_⟩
    intro q hq
    have hne : σ.history.length - 1 ≠ q := by omega
    have hq_lt : q < σ.history.length := by omega
    change ((cancelAt σ.cancelled (σ.history.length - 1) _)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
    rw [currentC_cancelAt_ne _ _ q _ hne]
    change σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
    rw [hstart_eq q hq_lt]
    exact Finset.subset_union_left
  | five_a bound hph _ =>
    refine treeInv_nonAppend P σ _ hinv rfl rfl (fun _ => Finset.Subset.refl _)
      (by simp [stop]) (by intro b hb; simp [stop] at hb)
  | six_a bound k hph hselect _ =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    refine treeInv_nonAppend P σ _ hinv rfl (length_cancelAt _ _ _)
      (fun q => subset_cancelAt _ _ q _) (by simp [beginScan]) ?_
    intro b hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨by change k ≤ σ.history.length - 1; omega, ?_⟩
    intro q hq
    have hne : k ≠ q := by omega
    change ((cancelAt σ.cancelled k _)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
    rw [currentC_cancelAt_ne _ k q _ hne]
    exact hscan_sub q (lt_trans hq hk_bound)
  | six_b bound k j hph hselect _ hchoice =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    have hk_len : k < σ.history.length := by omega
    have hj_rem : j ∈ oldRemaining P σ k := hchoice.1
    have hj_N : j ∈ σ.N k := (Finset.mem_sdiff.mp hj_rem).1
    have hj_not : j ∉ σ.snapshotC k ∪ oldD P σ k := (Finset.mem_sdiff.mp hj_rem).2
    refine treeInv_appendSolution P σ hinv k hk_len {j}
      (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.mpr hj_N) ?_
    rw [Finset.disjoint_singleton_left]
    intro hj_curr
    exact hj_not (hscan_sub k hk_bound hj_curr)
  | seven_a bound k hph hselect hhold hnonstrict _ =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    have hk_len : k < σ.history.length := by omega
    set F := equalityF P (σ.J k) (oldRemaining P σ k)
    have hF_rem : F ⊆ oldRemaining P σ k := equalityF_subset P (σ.J k) _
    have hF_N : F ⊆ σ.N k := hF_rem.trans Finset.sdiff_subset
    refine treeInv_appendSolution P σ hinv k hk_len F
      (equalityF_nonempty P (σ.J k) _ hhold hnonstrict) hF_N ?_
    rw [Finset.disjoint_left]
    intro x hxF hx_curr
    exact (Finset.mem_sdiff.mp (hF_rem hxF)).2 (hscan_sub k hk_bound hx_curr)
  | seven_b bound k hph hselect _ _ _ =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    refine treeInv_nonAppend P σ _ hinv rfl (length_cancelAt _ _ _)
      (fun q => subset_cancelAt _ _ q _) (by simp [beginScan]) ?_
    intro b hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨by change k ≤ σ.history.length - 1; omega, ?_⟩
    intro q hq
    have hne : k ≠ q := by omega
    change ((cancelAt σ.cancelled k _)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
    rw [currentC_cancelAt_ne _ k q _ hne]
    exact hscan_sub q (lt_trans hq hk_bound)

private theorem treeInv_reachable {n m : ℕ} (P : Problem n m) {σ : State n}
    (hr : Reachable P σ) : TreeInv P σ := by
  induction hr with
  | refl => exact treeInv_init P
  | tail _ hs ih => exact treeInv_step P ih hs

/-- If `u₁ < v₁ < L` share the same parent `w = par u₁ = par v₁`, no element of `edgeX u₁`
ever appears in `σ.J z` for any descendant `z < L` of `v₁`. -/
private theorem not_mem_of_sibling_lt {n : ℕ} (σ : State n)
    (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q)
    (htree : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧
      (edgeX q).Nonempty ∧
      edgeX q ⊆ σ.N (par q) ∧
      Disjoint (edgeX q) (σ.J (par q)) ∧
      edgeX q ⊆ σ.currentC (par q) ∧
      (∀ r, q ≤ r → r < σ.history.length →
        σ.J (par q) ⊂ σ.J r → Disjoint (σ.N r) (edgeX q)) ∧
      (∀ r, q < r → r < σ.history.length →
        par r = par q → Disjoint (edgeX r) (edgeX q)))
    {u₁ v₁ z : ℕ} (hu₁_pos : 0 < u₁) (hv₁_pos : 0 < v₁) (hu₁v₁ : u₁ < v₁)
    (hpar_eq : par v₁ = par u₁) (hz_len : z < σ.history.length)
    (hanc : Anc par v₁ z) {x : Fin n} (hx : x ∈ edgeX u₁) :
    x ∉ σ.J z := by
  have hstep_basic : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)) :=
    fun q h0 h1 => ⟨(htree q h0 h1).1, (htree q h0 h1).2.1, (htree q h0 h1).2.2.2.1⟩
  have hu₁_len : u₁ < σ.history.length :=
    lt_of_lt_of_le hu₁v₁ (le_trans (anc_le hpar hanc) (Nat.le_of_lt hz_len))
  obtain ⟨_, _, _, hdisj_u₁_J, _, hdisj_N, hdisj_sib⟩ := htree u₁ hu₁_pos hu₁_len
  induction hanc with
  | refl =>
    obtain ⟨hJv₁, _, _⟩ := htree v₁ hv₁_pos hz_len
    rw [hJv₁, hpar_eq, Finset.mem_union, not_or]
    refine ⟨Finset.disjoint_left.mp hdisj_u₁_J hx, ?_⟩
    exact Finset.disjoint_right.mp (hdisj_sib v₁ hu₁v₁ hz_len hpar_eq) hx
  | @step z' hz'_pos hprev ih =>
    have hpar_z'_lt : par z' < σ.history.length := lt_trans (hpar z' hz'_pos) hz_len
    have hx_not_par : x ∉ σ.J (par z') := ih hpar_z'_lt
    obtain ⟨hJz', _, hedge_sub_N, _, _, _, _⟩ := htree z' hz'_pos hz_len
    rw [hJz', Finset.mem_union, not_or]
    refine ⟨hx_not_par, ?_⟩
    have hv₁_le_par : v₁ ≤ par z' := anc_le hpar hprev
    have hu₁_le_par : u₁ ≤ par z' := Nat.le_of_lt (lt_of_lt_of_le hu₁v₁ hv₁_le_par)
    have hss_v₁ : σ.J (par v₁) ⊂ σ.J v₁ :=
      anc_ssubset_J σ par edgeX hpar hstep_basic (lt_of_le_of_lt hv₁_le_par hpar_z'_lt)
        (Anc.step hv₁_pos Anc.refl) (Nat.ne_of_lt (hpar v₁ hv₁_pos))
    have hsub_par : σ.J v₁ ⊆ σ.J (par z') :=
      anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep_basic q h0 h1).1) hpar_z'_lt hprev
    have hss_par : σ.J (par u₁) ⊂ σ.J (par z') := by
      rw [← hpar_eq]
      exact lt_of_lt_of_le hss_v₁ hsub_par
    have hdisj := hdisj_N (par z') hu₁_le_par hpar_z'_lt hss_par
    intro hx_edge
    exact Finset.disjoint_left.mp hdisj (hedge_sub_N hx_edge) hx

private theorem J_ne_of_lt {n m : ℕ} (P : Problem n m) (σ : State n)
    (hinv : TreeInv P σ) {u v : ℕ} (huv : u < v) (hv : v < σ.history.length) :
    σ.J u ≠ σ.J v := by
  obtain ⟨par, edgeX, hpar, htree⟩ := hinv.tree
  have hstep_basic : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)) :=
    fun q h0 h1 => ⟨(htree q h0 h1).1, (htree q h0 h1).2.1, (htree q h0 h1).2.2.2.1⟩
  by_cases hanc_uv : Anc par u v
  · exact ne_of_ssubset (anc_ssubset_J σ par edgeX hpar hstep_basic hv hanc_uv (Nat.ne_of_lt huv))
  · have hanc_vu : ¬ Anc par v u := fun h => absurd (anc_le hpar h) (not_le.mpr huv)
    set L := σ.history.length
    set S := (Finset.range (L + 1)).filter (fun w => Anc par w u ∧ Anc par w v)
    have hS_ne : S.Nonempty := ⟨0, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ L), anc_zero hpar u, anc_zero hpar v⟩⟩
    set w := S.max' hS_ne
    have hw_mem : w ∈ S := S.max'_mem hS_ne
    obtain ⟨hw_u, hw_v⟩ := (Finset.mem_filter.mp hw_mem).2
    have hwu_ne : w ≠ u := fun h => hanc_uv (h ▸ hw_v)
    have hwv_ne : w ≠ v := fun h => hanc_vu (h ▸ hw_u)
    obtain ⟨u₁, hu₁_pos, hu₁_par, hu₁_anc⟩ := anc_first_step hw_u hwu_ne
    obtain ⟨v₁, hv₁_pos, hv₁_par, hv₁_anc⟩ := anc_first_step hw_v hwv_ne
    have hu₁v₁_ne : u₁ ≠ v₁ := by
      intro heq
      have hu₁_le_u : u₁ ≤ u := anc_le hpar hu₁_anc
      have hu₁_in_S : u₁ ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hu₁_anc, heq ▸ hv₁_anc⟩
      have hu₁_le_w : u₁ ≤ w := S.le_max' u₁ hu₁_in_S
      have hw_lt_u₁ : w < u₁ := hu₁_par ▸ hpar u₁ hu₁_pos
      omega
    have hu_len : u < L := lt_trans huv hv
    have hu₁_len : u₁ < L := lt_of_le_of_lt (anc_le hpar hu₁_anc) hu_len
    have hv₁_len : v₁ < L := lt_of_le_of_lt (anc_le hpar hv₁_anc) hv
    rcases lt_or_gt_of_ne hu₁v₁_ne with hlt | hgt
    · obtain ⟨hJu₁, ⟨x, hx⟩, _⟩ := hstep_basic u₁ hu₁_pos hu₁_len
      have hx_in_Ju₁ : x ∈ σ.J u₁ := by rw [hJu₁]; exact Finset.mem_union_right _ hx
      have hx_in_Ju : x ∈ σ.J u :=
        anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep_basic q h0 h1).1) hu_len hu₁_anc hx_in_Ju₁
      have hx_not_Jv : x ∉ σ.J v :=
        not_mem_of_sibling_lt σ par edgeX hpar htree hu₁_pos hv₁_pos hlt
          (hv₁_par.trans hu₁_par.symm) hv hv₁_anc hx
      intro heq
      exact hx_not_Jv (heq ▸ hx_in_Ju)
    · obtain ⟨hJv₁, ⟨y, hy⟩, _⟩ := hstep_basic v₁ hv₁_pos hv₁_len
      have hy_in_Jv₁ : y ∈ σ.J v₁ := by rw [hJv₁]; exact Finset.mem_union_right _ hy
      have hy_in_Jv : y ∈ σ.J v :=
        anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep_basic q h0 h1).1) hv hv₁_anc hy_in_Jv₁
      have hy_not_Ju : y ∉ σ.J u :=
        not_mem_of_sibling_lt σ par edgeX hpar htree hv₁_pos hu₁_pos hgt
          (hu₁_par.trans hv₁_par.symm) hu_len hu₁_anc hy
      intro heq
      exact hy_not_Ju (heq.symm ▸ hy_in_Jv)

end BalasAdditive.Convergence.NoDupAux

open BalasAdditive.Convergence

theorem solution {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) :
    (σ.history.map Record.J).Nodup := by
  have hinv := BalasAdditive.Convergence.NoDupAux.treeInv_reachable P hr
  rw [List.nodup_iff_injective_get]
  intro ⟨u, hu⟩ ⟨v, hv⟩ heq
  simp only [List.length_map] at hu hv
  simp only [List.get_eq_getElem, List.getElem_map] at heq
  have hJu : σ.J u = σ.history[u].J := by
    simp [State.J, List.getElem?_eq_getElem hu]
  have hJv : σ.J v = σ.history[v].J := by
    simp [State.J, List.getElem?_eq_getElem hv]
  have hJeq : σ.J u = σ.J v := hJu.trans (heq.trans hJv.symm)
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · exact absurd hJeq (BalasAdditive.Convergence.NoDupAux.J_ne_of_lt P σ hinv hlt hv)
  · rfl
  · exact absurd hJeq.symm (BalasAdditive.Convergence.NoDupAux.J_ne_of_lt P σ hinv hgt hu)
