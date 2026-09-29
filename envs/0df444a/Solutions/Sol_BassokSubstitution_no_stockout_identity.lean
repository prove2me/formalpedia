-- Prove2me | solution 1 for BassokSubstitution.no_stockout_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:11:47.276679+00:00
-- url     : https://prove2.me/submissions/08c97c8a-ec65-4378-b6ec-4314b614acf0

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- One step of the inner loop of Algorithm (A): class `i`, product `j`. -/
def aux_bns_step (i j : ℕ) (st : AlgState) : AlgState :=
  { v := Function.update st.v j (st.v j - min (st.u i) (st.v j))
    u := Function.update st.u i (st.u i - min (st.u i) (st.v j))
    w := Function.update st.w j (Function.update (st.w j) i (min (st.u i) (st.v j))) }

theorem aux_bns_inner_succ (i n j : ℕ) (st : AlgState) :
    innerLoop i (n+1) j st = innerLoop i n (j-1) (aux_bns_step i j st) := rfl

theorem aux_bns_peel (i : ℕ) : ∀ (n j : ℕ) (st : AlgState),
    innerLoop i (n+1) j st = aux_bns_step i (j - n) (innerLoop i n j st) := by
  intro n
  induction n with
  | zero => intro j st; rfl
  | succ n ih =>
    intro j st
    rw [aux_bns_inner_succ i (n+1) j st, ih (j-1) (aux_bns_step i j st),
      aux_bns_inner_succ i n j st]
    congr 1
    omega

theorem aux_bns_inner_v_untouched (i : ℕ) : ∀ (n j : ℕ) (st : AlgState) (p : ℕ),
    (j < p ∨ p + n ≤ j) → (innerLoop i n j st).v p = st.v p := by
  intro n
  induction n with
  | zero => intro j st p _; rfl
  | succ n ih =>
    intro j st p hp
    rw [aux_bns_inner_succ, ih (j-1) _ p (by omega)]
    have hpj : p ≠ j := by omega
    simp only [aux_bns_step]
    exact Function.update_of_ne hpj _ _

theorem aux_bns_inner_agree (i m : ℕ) : ∀ (n j : ℕ) (A B : AlgState),
    m + n ≤ j → (∀ p, p ≠ m → A.v p = B.v p) → A.u i = B.u i →
    (∀ p, p ≠ m → (innerLoop i n j A).v p = (innerLoop i n j B).v p) ∧
      (innerLoop i n j A).u i = (innerLoop i n j B).u i := by
  intro n
  induction n with
  | zero => intro j A B _ hv hu; exact ⟨hv, hu⟩
  | succ n ih =>
    intro j A B hj hv hu
    rw [aux_bns_inner_succ, aux_bns_inner_succ]
    have hjm : j ≠ m := by omega
    apply ih (j-1) _ _ (by omega)
    · intro p hp
      simp only [aux_bns_step]
      by_cases hpj : p = j
      · rw [hpj]; simp [hv j hjm, hu]
      · rw [Function.update_of_ne hpj, Function.update_of_ne hpj]; exact hv p hp
    · simp [aux_bns_step, hu, hv j hjm]

theorem aux_bns_step_u_nonneg (i j : ℕ) (st : AlgState) : 0 ≤ (aux_bns_step i j st).u i := by
  simp only [aux_bns_step, Function.update_self]
  exact sub_nonneg.2 (min_le_left _ _)

theorem aux_bns_step_v_nonneg (i j : ℕ) (st : AlgState) : 0 ≤ (aux_bns_step i j st).v j := by
  simp only [aux_bns_step, Function.update_self]
  exact sub_nonneg.2 (min_le_right _ _)

theorem aux_bns_run_succ (k : ℕ) (y d : ℕ → ℝ) (n : ℕ) :
    runFrom k y d (n+1) = innerLoop (k + n) (n + 1) (k + n)
      { (runFrom k y d n) with
        u := Function.update (runFrom k y d n).u (k + n) (d (k + n)) } := rfl

theorem aux_bns_run_one (k : ℕ) (y d : ℕ → ℝ) :
    runFrom k y d 1 = aux_bns_step k k
      { v := y, u := Function.update (fun _ => 0) k (d k), w := fun _ _ => 0 } := rfl

theorem aux_bns_simstep (y d : ℕ → ℝ) (m n : ℕ)
    (h : ∀ p, p ≠ m → (runFrom m y d (n+1)).v p = (runFrom (m+1) y d n).v p) :
    (∀ p, p ≠ m → (runFrom m y d (n+1+1)).v p = (runFrom (m+1) y d (n+1)).v p) ∧
    0 ≤ (runFrom (m+1) y d (n+1)).u (m+n+1) ∧
    (runFrom m y d (n+1+1)).u (m+n+1) = (runFrom (m+1) y d (n+1)).u (m+n+1) -
        min ((runFrom (m+1) y d (n+1)).u (m+n+1)) ((runFrom m y d (n+1)).v m) ∧
    (runFrom m y d (n+1+1)).v m = (runFrom m y d (n+1)).v m -
        min ((runFrom (m+1) y d (n+1)).u (m+n+1)) ((runFrom m y d (n+1)).v m) := by
  have hA : runFrom m y d (n+1+1) = aux_bns_step (m+n+1) m (innerLoop (m+n+1) (n+1) (m+n+1)
      { (runFrom m y d (n+1)) with
        u := Function.update (runFrom m y d (n+1)).u (m+n+1) (d (m+n+1)) }) := by
    rw [aux_bns_run_succ, show m + (n+1) = m + n + 1 by omega, aux_bns_peel,
      show m + n + 1 - (n+1) = m by omega]
  have hB : runFrom (m+1) y d (n+1) = innerLoop (m+n+1) (n+1) (m+n+1)
      { (runFrom (m+1) y d n) with
        u := Function.update (runFrom (m+1) y d n).u (m+n+1) (d (m+n+1)) } := by
    rw [aux_bns_run_succ, show m + 1 + n = m + n + 1 by omega]
  have hagree := aux_bns_inner_agree (m+n+1) m (n+1) (m+n+1)
    { (runFrom m y d (n+1)) with
        u := Function.update (runFrom m y d (n+1)).u (m+n+1) (d (m+n+1)) }
    { (runFrom (m+1) y d n) with
        u := Function.update (runFrom (m+1) y d n).u (m+n+1) (d (m+n+1)) }
    (by omega) (fun p hp => h p hp) (by simp)
  have hvm := aux_bns_inner_v_untouched (m+n+1) (n+1) (m+n+1)
    { (runFrom m y d (n+1)) with
        u := Function.update (runFrom m y d (n+1)).u (m+n+1) (d (m+n+1)) } m (Or.inr (by omega))
  have hU : 0 ≤ (runFrom (m+1) y d (n+1)).u (m+n+1) := by
    rw [hB, aux_bns_peel]; exact aux_bns_step_u_nonneg _ _ _
  refine ⟨?_, hU, ?_, ?_⟩
  · intro p hp
    rw [hA, hB]
    simp only [aux_bns_step]
    rw [Function.update_of_ne hp]
    exact hagree.1 p hp
  · rw [hA, hB]
    simp only [aux_bns_step, Function.update_self]
    rw [hagree.2, hvm]
  · rw [hA, hB]
    simp only [aux_bns_step, Function.update_self]
    rw [hagree.2, hvm]

theorem aux_bns_sim (y d : ℕ → ℝ) (m : ℕ) : ∀ n : ℕ,
    (∀ p, p ≠ m → (runFrom m y d (n+1)).v p = (runFrom (m+1) y d n).v p) ∧
    0 ≤ (runFrom m y d (n+1)).v m := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [aux_bns_run_one]
      simp only [aux_bns_step]
      rw [Function.update_of_ne hp]
      rfl
    · rw [aux_bns_run_one]; exact aux_bns_step_v_nonneg _ _ _
  | succ n ih =>
    obtain ⟨h1, _, _, h4⟩ := aux_bns_simstep y d m n ih.1
    refine ⟨h1, ?_⟩
    rw [h4]; exact sub_nonneg.2 (min_le_right _ _)

theorem aux_bns_real_lemma (U V : ℝ) (h : 0 < U - min U V) : V - min U V = 0 := by
  rcases le_total U V with hUV | hUV
  · rw [min_eq_left hUV] at h; simp at h
  · rw [min_eq_right hUV]; ring

theorem aux_bns_exhaust (y d : ℕ → ℝ) (m : ℕ) :
    ∀ t, 0 < (runFrom m y d (t+1)).u (m+t) → (runFrom m y d (t+1)).v m = 0
  | 0, h => by
      rw [aux_bns_run_one] at h ⊢
      simp only [aux_bns_step, Nat.add_zero, Function.update_self] at h ⊢
      exact aux_bns_real_lemma _ _ h
  | t+1, h => by
      obtain ⟨_, _, h3, h4⟩ := aux_bns_simstep y d m t (aux_bns_sim y d m t).1
      rw [show m + (t+1) = m + t + 1 by omega, h3] at h
      rw [h4]
      exact aux_bns_real_lemma _ _ h

theorem aux_bns_sticky (y d : ℕ → ℝ) (m t : ℕ) (h : (runFrom m y d (t+1)).v m = 0) :
    ∀ n, t ≤ n → (runFrom m y d (n+1)).v m = 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ n hn ih =>
    obtain ⟨_, h2, _, h4⟩ := aux_bns_simstep y d m n (aux_bns_sim y d m n).1
    rw [h4, ih, min_eq_right h2, sub_zero]

variable {N : ℕ}

theorem aux_bns_short_eq (y d : Fin N → ℝ) (k t : ℕ) (j : Fin N) (hj : j.val = k + t) :
    shortage y d k j = (runFrom k (extend y) (extend d) (t+1)).u j.val := by
  unfold shortage
  rw [if_pos (by omega), show j.val + 1 - k = t + 1 by omega]

theorem aux_bns_short_nonneg (y d : Fin N → ℝ) (k : ℕ) (j : Fin N) : 0 ≤ shortage y d k j := by
  by_cases h : k ≤ j.val
  · obtain ⟨t, ht⟩ : ∃ t, j.val = k + t := ⟨j.val - k, by omega⟩
    rw [aux_bns_short_eq y d k t j ht, ht, aux_bns_run_succ, aux_bns_peel]
    exact aux_bns_step_u_nonneg _ _ _
  · unfold shortage
    rw [if_neg h]

theorem aux_bns_short_mono1 (y d : Fin N → ℝ) (m : ℕ) (j : Fin N) (hmj : m < j.val) :
    shortage y d m j ≤ shortage y d (m+1) j := by
  obtain ⟨n, hn⟩ : ∃ n, j.val = m + n + 1 := ⟨j.val - m - 1, by omega⟩
  rw [aux_bns_short_eq y d m (n+1) j (by omega), aux_bns_short_eq y d (m+1) n j (by omega), hn]
  obtain ⟨_, h2, h3, _⟩ := aux_bns_simstep (extend y) (extend d) m n
    (aux_bns_sim (extend y) (extend d) m n).1
  have hV := (aux_bns_sim (extend y) (extend d) m n).2
  rw [h3]
  have hmin := le_min h2 hV
  linarith

theorem aux_bns_short_mono (y d : Fin N → ℝ) (k : ℕ) (j : Fin N) :
    ∀ k', k ≤ k' → k' ≤ j.val → shortage y d k j ≤ shortage y d k' j := by
  intro k' hk
  induction k', hk using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ k' hk ih =>
    intro h
    exact (ih (by omega)).trans (aux_bns_short_mono1 y d k' j (by omega))

theorem aux_bns_short_eq_of_pos (y d : Fin N → ℝ) (m : ℕ) (m' i : Fin N)
    (hm : m ≤ m'.val) (hmi : m'.val < i.val) (hpos : 0 < shortage y d m m') :
    shortage y d m i = shortage y d (m+1) i := by
  obtain ⟨t, ht⟩ : ∃ t, m'.val = m + t := ⟨m'.val - m, by omega⟩
  rw [aux_bns_short_eq y d m t m' ht, ht] at hpos
  have hz := aux_bns_exhaust (extend y) (extend d) m t hpos
  obtain ⟨n, hn⟩ : ∃ n, i.val = m + n + 1 := ⟨i.val - m - 1, by omega⟩
  have hz' := aux_bns_sticky _ _ m t hz n (by omega)
  rw [aux_bns_short_eq y d m (n+1) i (by omega), aux_bns_short_eq y d (m+1) n i (by omega), hn]
  obtain ⟨_, h2, h3, _⟩ := aux_bns_simstep (extend y) (extend d) m n
    (aux_bns_sim (extend y) (extend d) m n).1
  rw [h3, hz', min_eq_right h2, sub_zero]

/-! Measurability -/

theorem aux_bns_meas_inner {α : Type*} [MeasurableSpace α] (i : ℕ) :
    ∀ (n j : ℕ) (st : α → AlgState),
    (∀ q, Measurable fun a => (st a).u q) → (∀ q, Measurable fun a => (st a).v q) →
    (∀ q, Measurable fun a => (innerLoop i n j (st a)).u q) ∧
      (∀ q, Measurable fun a => (innerLoop i n j (st a)).v q) := by
  intro n
  induction n with
  | zero => intro j st hu hv; exact ⟨hu, hv⟩
  | succ n ih =>
    intro j st hu hv
    simp only [aux_bns_inner_succ]
    refine ih (j-1) (fun a => aux_bns_step i j (st a)) ?_ ?_
    · intro q
      by_cases hq : q = i
      · rw [hq]; simp only [aux_bns_step, Function.update_self]
        exact (hu i).sub ((hu i).min (hv j))
      · simp only [aux_bns_step, Function.update_of_ne hq]; exact hu q
    · intro q
      by_cases hq : q = j
      · rw [hq]; simp only [aux_bns_step, Function.update_self]
        exact (hv j).sub ((hu i).min (hv j))
      · simp only [aux_bns_step, Function.update_of_ne hq]; exact hv q

theorem aux_bns_meas_run {α : Type*} [MeasurableSpace α] (k : ℕ) (y : ℕ → ℝ) (D : α → ℕ → ℝ)
    (hD : ∀ q, Measurable fun a => D a q) : ∀ n,
    (∀ q, Measurable fun a => (runFrom k y (D a) n).u q) ∧
      (∀ q, Measurable fun a => (runFrom k y (D a) n).v q) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun q => by show Measurable fun _ : α => (0:ℝ); exact measurable_const,
      fun q => by show Measurable fun _ : α => y q; exact measurable_const⟩
  | succ n ih =>
    simp only [aux_bns_run_succ]
    refine aux_bns_meas_inner (k+n) (n+1) (k+n) _ ?_ ?_
    · intro q
      by_cases hq : q = k + n
      · rw [hq]; simp only [Function.update_self]; exact hD _
      · simp only [Function.update_of_ne hq]; exact ih.1 q
    · exact ih.2

theorem aux_bns_meas_extend (q : ℕ) : Measurable fun d : Fin N → ℝ => extend d q := by
  by_cases hq : q < N
  · simp only [extend, hq, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [extend, hq, ↓reduceDIte]
    exact measurable_const

theorem aux_bns_meas_short (y : Fin N → ℝ) (k : ℕ) (j : Fin N) :
    Measurable fun d : Fin N → ℝ => shortage y d k j := by
  by_cases h : k ≤ j.val
  · simp only [shortage, h, ↓reduceIte]
    exact (aux_bns_meas_run k (extend y) (fun d => extend d) aux_bns_meas_extend _).1 _
  · simp only [shortage, h, ↓reduceIte]
    exact measurable_const

theorem aux_bns_meas_svz (y : Fin N → ℝ) (a b n : ℕ) :
    MeasurableSet {d : Fin N → ℝ | ShortVecZero y d a b n} := by
  have : {d : Fin N → ℝ | ShortVecZero y d a b n} =
      ⋂ m'' : Fin N, ⋂ (_ : b ≤ m''.val), ⋂ (_ : m''.val ≤ n),
        {d : Fin N → ℝ | shortage y d a m'' = 0} := by
    ext d; simp [ShortVecZero]
  rw [this]
  exact MeasurableSet.iInter fun m'' => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_eq_fun (aux_bns_meas_short y a m'') measurable_const

/-- The events of the decomposition. -/
def aux_bns_E (y : Fin N → ℝ) (i m : Fin N) : Set (Fin N → ℝ) :=
  {d | 0 < shortage y d (m + 1) i ∧ ShortVecZero y d m m i}

theorem aux_bns_pointwise (y d : Fin N → ℝ) (k i : Fin N) (hki : k.val < i.val) :
    (shortage y d i i = 0 ∨ ∃ m : Fin N, (k ≤ m ∧ m < i) ∧
        (0 < shortage y d (m + 1) i ∧ ShortVecZero y d m m i))
      ↔ ¬ (0 < shortage y d k i) := by
  constructor
  · rintro (h | ⟨m, ⟨hkm, hmi⟩, _, hsvz⟩)
    · have := aux_bns_short_mono y d k i i.val hki.le le_rfl
      rw [h] at this
      exact not_lt.2 this
    · have hkm' : k.val ≤ m.val := hkm
      have hmi' : m.val < i.val := hmi
      have h0 : shortage y d m i = 0 := hsvz i hmi'.le le_rfl
      have := aux_bns_short_mono y d k i m.val hkm' hmi'.le
      rw [h0] at this
      exact not_lt.2 this
  · intro h
    have hk0 : shortage y d k i = 0 := le_antisymm (not_lt.1 h) (aux_bns_short_nonneg _ _ _ _)
    by_cases hi0 : shortage y d i i = 0
    · exact Or.inl hi0
    · right
      have hex : ∃ m' : ℕ, k.val ≤ m' ∧ m' < i.val ∧ shortage y d m' i = 0 ∧
          shortage y d (m'+1) i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hi0
        have hall : ∀ m', k.val ≤ m' → m' ≤ i.val → shortage y d m' i = 0 := by
          intro m' hm'
          induction m', hm' using Nat.le_induction with
          | base => intro _; exact hk0
          | succ m' hm' ih => intro h'; exact hcon m' hm' (by omega) (ih (by omega))
        exact hall i.val hki.le le_rfl
      obtain ⟨m', hkm, hmi, hm0, hm1⟩ := hex
      refine ⟨⟨m', by omega⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · show k.val ≤ m'
        exact hkm
      · show m' < i.val
        exact hmi
      · exact lt_of_le_of_ne (aux_bns_short_nonneg _ _ _ _) (Ne.symm hm1)
      · intro m'' h1 h2
        rcases lt_or_eq_of_le h2 with h2 | h2
        · by_contra hne
          have hpos : 0 < shortage y d m' m'' :=
            lt_of_le_of_ne (aux_bns_short_nonneg _ _ _ _) (Ne.symm hne)
          have := aux_bns_short_eq_of_pos y d m' m'' i h1 h2 hpos
          exact hm1 (this ▸ hm0)
        · have : m'' = i := Fin.ext h2
          rw [this]; exact hm0

end BassokSubstitution

open MeasureTheory
open BassokSubstitution

theorem solution {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (k i : Fin N) (hki : k < i) :
    (Measure.pi ν).real {d | shortage y d i i = 0}
        + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
            (Measure.pi ν).real {d | 0 < shortage y d (m + 1) i ∧ ShortVecZero y d m m i}
      = 1 - (Measure.pi ν).real {d | 0 < shortage y d k i} := by
  classical
  have hki' : k.val < i.val := hki
  have hEm : ∀ m : Fin N, MeasurableSet (aux_bns_E y i m) := by
    intro m
    exact (measurableSet_lt measurable_const (aux_bns_meas_short y _ i)).inter
      (aux_bns_meas_svz y m m i)
  have hT : MeasurableSet {d : Fin N → ℝ | shortage y d i i = 0} :=
    measurableSet_eq_fun (aux_bns_meas_short y i i) measurable_const
  have hZ : MeasurableSet {d : Fin N → ℝ | 0 < shortage y d k i} :=
    measurableSet_lt measurable_const (aux_bns_meas_short y k i)
  set S : Finset (Fin N) := Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i) with hS
  have hU : MeasurableSet (⋃ m ∈ S, aux_bns_E y i m) :=
    Finset.measurableSet_biUnion S (fun b _ => hEm b)
  have hdisjS : (S : Set (Fin N)).PairwiseDisjoint (aux_bns_E y i) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hS] at ha hb
    show Disjoint (aux_bns_E y i a) (aux_bns_E y i b)
    rw [Set.disjoint_left]
    -- general claim for an ordered pair
    have key : ∀ a b : Fin N, a < b → b < i → ∀ d, d ∈ aux_bns_E y i a → d ∉ aux_bns_E y i b := by
      intro a b hab hbi d hda hdb
      have hab' : a.val < b.val := hab
      have hbi' : b.val < i.val := hbi
      have h0 : shortage y d b i = 0 := hdb.2 i hbi'.le le_rfl
      have := aux_bns_short_mono y d (a.val + 1) i b.val (by omega) hbi'.le
      rw [h0] at this
      exact absurd hda.1 (not_lt.2 this)
    intro d hda hdb
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h hb.2 d hda hdb
    · exact key b a h ha.2 d hdb hda
  have hdisjT : Disjoint {d : Fin N → ℝ | shortage y d i i = 0} (⋃ m ∈ S, aux_bns_E y i m) := by
    rw [Set.disjoint_left]
    intro d hd hdU
    simp only [Set.mem_iUnion, exists_prop] at hdU
    obtain ⟨m, hmS, hdm⟩ := hdU
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hmS
    have hmi' : m.val < i.val := hmS.2
    have := aux_bns_short_mono y d (m.val + 1) i i.val (by omega) le_rfl
    rw [show shortage y d i i = 0 from hd] at this
    exact absurd hdm.1 (not_lt.2 this)
  have hunion : {d : Fin N → ℝ | shortage y d i i = 0} ∪ (⋃ m ∈ S, aux_bns_E y i m) =
      {d : Fin N → ℝ | 0 < shortage y d k i}ᶜ := by
    ext d
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, exists_prop,
      hS, Finset.mem_filter, Finset.mem_univ, true_and, aux_bns_E]
    exact aux_bns_pointwise y d k i hki'
  show (Measure.pi ν).real {d | shortage y d i i = 0}
      + ∑ m ∈ S, (Measure.pi ν).real (aux_bns_E y i m) = _
  rw [← measureReal_biUnion_finset hdisjS (fun b _ => hEm b) (fun b _ => measure_ne_top _ _),
    ← measureReal_union hdisjT hU (measure_ne_top _ _) (measure_ne_top _ _),
    hunion, probReal_compl_eq_one_sub hZ]
