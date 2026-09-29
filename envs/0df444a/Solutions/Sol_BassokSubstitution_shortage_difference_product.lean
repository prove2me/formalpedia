-- Prove2me | solution 1 for BassokSubstitution.shortage_difference_product
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:16:23.775159+00:00
-- url     : https://prove2.me/submissions/29db95b7-1a6e-449b-87f3-ba0f49b5560b

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- One step of the inner loop. -/
def aux_sdp_step (i j : ℕ) (st : AlgState) : AlgState :=
  { v := Function.update st.v j (st.v j - min (st.u i) (st.v j))
    u := Function.update st.u i (st.u i - min (st.u i) (st.v j))
    w := Function.update st.w j (Function.update (st.w j) i (min (st.u i) (st.v j))) }

theorem aux_sdp_inner_succ (i n j : ℕ) (st : AlgState) :
    innerLoop i (n+1) j st = innerLoop i n (j-1) (aux_sdp_step i j st) := rfl

theorem aux_sdp_inner_last (i : ℕ) : ∀ (n j : ℕ) (st : AlgState),
    innerLoop i (n+1) j st = aux_sdp_step i (j - n) (innerLoop i n j st)
  | 0, j, st => by simp [innerLoop, aux_sdp_step]
  | n+1, j, st => by
    have h := aux_sdp_inner_last i n (j-1) (aux_sdp_step i j st)
    rw [aux_sdp_inner_succ i (n+1) j st, h, aux_sdp_inner_succ i n j st, Nat.sub_sub, Nat.add_comm 1 n]

theorem aux_sdp_inner_rel (c k : ℕ) : ∀ (m p : ℕ) (A B : AlgState), k + m ≤ p →
    (∀ a, a ≠ k → A.v a = B.v a) → A.u c = B.u c →
    (∀ a, a ≠ k → (innerLoop c m p A).v a = (innerLoop c m p B).v a) ∧
    (innerLoop c m p A).u c = (innerLoop c m p B).u c ∧
    (innerLoop c m p A).v k = A.v k
  | 0, p, A, B, _, hv, hu => ⟨hv, hu, rfl⟩
  | m+1, p, A, B, hp, hv, hu => by
    rw [aux_sdp_inner_succ, aux_sdp_inner_succ]
    have hpk : p ≠ k := by omega
    have hvp : A.v p = B.v p := hv p hpk
    have hv' : ∀ a, a ≠ k → (aux_sdp_step c p A).v a = (aux_sdp_step c p B).v a := by
      intro a ha
      by_cases hap : a = p
      · subst hap; simp [aux_sdp_step, hu, hvp]
      · simp [aux_sdp_step, Function.update_of_ne hap, hv a ha]
    have hu' : (aux_sdp_step c p A).u c = (aux_sdp_step c p B).u c := by
      simp [aux_sdp_step, hu, hvp]
    obtain ⟨h1, h2, h3⟩ := aux_sdp_inner_rel c k m (p-1) (aux_sdp_step c p A)
      (aux_sdp_step c p B) (by omega) hv' hu'
    refine ⟨h1, h2, ?_⟩
    rw [h3]
    all_goals simp [aux_sdp_step, Function.update_of_ne (Ne.symm hpk)]

theorem aux_sdp_runFrom_succ (k : ℕ) (Y D : ℕ → ℝ) (n : ℕ) :
    runFrom k Y D (n+1) = innerLoop (k+n) (n+1) (k+n)
      { runFrom k Y D n with u := Function.update (runFrom k Y D n).u (k+n) (D (k+n)) } := rfl

theorem aux_sdp_base (k : ℕ) (Y D : ℕ → ℝ) :
    (∀ a, a ≠ k → (runFrom k Y D 1).v a = (runFrom (k+1) Y D 0).v a) ∧
    (runFrom k Y D 1).u k = D k - min (D k) (Y k) ∧
    (runFrom k Y D 1).v k = Y k - min (D k) (Y k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp [runFrom, innerLoop, Function.update_of_ne ha]
  · simp [runFrom, innerLoop]
  · simp [runFrom, innerLoop]

theorem aux_sdp_couple_step (k : ℕ) (Y D : ℕ → ℝ) (n : ℕ)
    (ih : ∀ a, a ≠ k → (runFrom k Y D (n+1)).v a = (runFrom (k+1) Y D n).v a) :
    (∀ a, a ≠ k → (runFrom k Y D (n+2)).v a = (runFrom (k+1) Y D (n+1)).v a) ∧
    (runFrom k Y D (n+2)).u (k+n+1) = (runFrom (k+1) Y D (n+1)).u (k+n+1)
        - min ((runFrom (k+1) Y D (n+1)).u (k+n+1)) ((runFrom k Y D (n+1)).v k) ∧
    (runFrom k Y D (n+2)).v k = (runFrom k Y D (n+1)).v k
        - min ((runFrom (k+1) Y D (n+1)).u (k+n+1)) ((runFrom k Y D (n+1)).v k) := by
  set A := runFrom k Y D (n+1) with hA
  set B := runFrom (k+1) Y D n with hB
  have eA : runFrom k Y D (n+2) = innerLoop (k+n+1) (n+2) (k+n+1)
      { A with u := Function.update A.u (k+n+1) (D (k+n+1)) } := rfl
  have eB : runFrom (k+1) Y D (n+1) = innerLoop (k+n+1) (n+1) (k+n+1)
      { B with u := Function.update B.u (k+n+1) (D (k+n+1)) } := by
    rw [aux_sdp_runFrom_succ (k+1) Y D n]
    have : k + 1 + n = k + n + 1 := by omega
    rw [this]
  set A0 : AlgState := { A with u := Function.update A.u (k+n+1) (D (k+n+1)) } with hA0
  set B0 : AlgState := { B with u := Function.update B.u (k+n+1) (D (k+n+1)) } with hB0
  obtain ⟨h1, h2, h3⟩ := aux_sdp_inner_rel (k+n+1) k (n+1) (k+n+1) A0 B0 (by omega)
    (fun a ha => by simp [hA0, hB0, ih a ha]) (by simp [hA0, hB0])
  have eA' : runFrom k Y D (n+2) = aux_sdp_step (k+n+1) k (innerLoop (k+n+1) (n+1) (k+n+1) A0) := by
    rw [eA, aux_sdp_inner_last]
    have : k + n + 1 - (n + 1) = k := by omega
    rw [this]
  rw [eA', eB]
  have h3' : (innerLoop (k+n+1) (n+1) (k+n+1) A0).v k = A.v k := by rw [h3]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp [aux_sdp_step, Function.update_of_ne ha, h1 a ha]
  · simp [aux_sdp_step, h2, h3']
  · simp [aux_sdp_step, h2, h3']

theorem aux_sdp_couple (k : ℕ) (Y D : ℕ → ℝ) : ∀ n : ℕ,
    (∀ a, a ≠ k → (runFrom k Y D (n+1)).v a = (runFrom (k+1) Y D n).v a)
  | 0 => (aux_sdp_base k Y D).1
  | n+1 => (aux_sdp_couple_step k Y D n (aux_sdp_couple k Y D n)).1

/-- ℕ-indexed subproblem shortage. -/
def aux_sdp_sN (Y D : ℕ → ℝ) (k c : ℕ) : ℝ := (runFrom k Y D (c + 1 - k)).u c

/-- Remaining stock of product `k` in the `k`-subproblem after `n+1` classes. -/
def aux_sdp_VN (Y D : ℕ → ℝ) (k n : ℕ) : ℝ := (runFrom k Y D (n+1)).v k

theorem aux_sdp_F0 (Y D : ℕ → ℝ) (k : ℕ) :
    aux_sdp_sN Y D k k = D k - min (D k) (Y k) ∧ aux_sdp_VN Y D k 0 = Y k - min (D k) (Y k) := by
  have h := aux_sdp_base k Y D
  refine ⟨?_, h.2.2⟩
  simp only [aux_sdp_sN]
  rw [show k + 1 - k = 1 by omega]
  exact h.2.1

theorem aux_sdp_F1 (Y D : ℕ → ℝ) (k n : ℕ) :
    aux_sdp_sN Y D k (k+n+1) = aux_sdp_sN Y D (k+1) (k+n+1)
      - min (aux_sdp_sN Y D (k+1) (k+n+1)) (aux_sdp_VN Y D k n) ∧
    aux_sdp_VN Y D k (n+1) = aux_sdp_VN Y D k n
      - min (aux_sdp_sN Y D (k+1) (k+n+1)) (aux_sdp_VN Y D k n) := by
  have h := aux_sdp_couple_step k Y D n (aux_sdp_couple k Y D n)
  have e1 : k + n + 1 + 1 - k = n + 2 := by omega
  have e2 : k + n + 1 + 1 - (k+1) = n + 1 := by omega
  simp only [aux_sdp_sN, aux_sdp_VN, e1, e2]
  exact ⟨h.2.1, h.2.2⟩

theorem aux_sdp_step_u_nonneg (i j : ℕ) (st : AlgState) : 0 ≤ (aux_sdp_step i j st).u i := by
  simp only [aux_sdp_step, Function.update_self]
  exact sub_nonneg.2 (min_le_left _ _)

theorem aux_sdp_sN_nonneg (Y D : ℕ → ℝ) (k c : ℕ) (h : k ≤ c) : 0 ≤ aux_sdp_sN Y D k c := by
  unfold aux_sdp_sN
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show k + t + 1 - k = t + 1 by omega, aux_sdp_runFrom_succ, aux_sdp_inner_last]
  exact aux_sdp_step_u_nonneg _ _ _

theorem aux_sdp_VN_nonneg (Y D : ℕ → ℝ) (k : ℕ) : ∀ n, 0 ≤ aux_sdp_VN Y D k n
  | 0 => by rw [(aux_sdp_F0 Y D k).2]; exact sub_nonneg.2 (min_le_right _ _)
  | n+1 => by rw [(aux_sdp_F1 Y D k n).2]; exact sub_nonneg.2 (min_le_right _ _)

theorem aux_sdp_mono (Y D : ℕ → ℝ) (k c : ℕ) (h : k + 1 ≤ c) :
    aux_sdp_sN Y D k c ≤ aux_sdp_sN Y D (k+1) c := by
  obtain ⟨n, rfl⟩ : ∃ n, c = k + n + 1 := ⟨c - k - 1, by omega⟩
  rw [(aux_sdp_F1 Y D k n).1]
  have h1 := aux_sdp_sN_nonneg Y D (k+1) (k+n+1) (by omega)
  have h2 := aux_sdp_VN_nonneg Y D k n
  have h3 : 0 ≤ min (aux_sdp_sN Y D (k+1) (k+n+1)) (aux_sdp_VN Y D k n) := le_min h1 h2
  linarith

theorem aux_sdp_Q4 (Y D : ℕ → ℝ) (k c : ℕ) (h : k ≤ c) (hpos : 0 < aux_sdp_sN Y D k c) :
    aux_sdp_VN Y D k (c - k) = 0 := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · rw [Nat.sub_self, (aux_sdp_F0 Y D k).2]
    rw [(aux_sdp_F0 Y D k).1] at hpos
    rcases le_total (D k) (Y k) with hle | hle
    · rw [min_eq_left hle] at hpos; simp at hpos
    · rw [min_eq_right hle]; simp
  · obtain ⟨n, rfl⟩ : ∃ n, c = k + n + 1 := ⟨c - k - 1, by omega⟩
    rw [show k + n + 1 - k = n + 1 by omega, (aux_sdp_F1 Y D k n).2]
    rw [(aux_sdp_F1 Y D k n).1] at hpos
    rcases le_total (aux_sdp_sN Y D (k+1) (k+n+1)) (aux_sdp_VN Y D k n) with hle | hle
    · rw [min_eq_left hle] at hpos; simp at hpos
    · rw [min_eq_right hle]; simp

theorem aux_sdp_Q3v (Y D : ℕ → ℝ) (k n : ℕ) (h0 : aux_sdp_VN Y D k n = 0) :
    ∀ t, aux_sdp_VN Y D k (n+t) = 0
  | 0 => h0
  | t+1 => by
    have ih := aux_sdp_Q3v Y D k n h0 t
    rw [← Nat.add_assoc, (aux_sdp_F1 Y D k (n+t)).2, ih,
      min_eq_right (aux_sdp_sN_nonneg Y D (k+1) _ (by omega))]
    simp

theorem aux_sdp_Q5 (Y D : ℕ → ℝ) (k c c' : ℕ) (h : k ≤ c) (hpos : 0 < aux_sdp_sN Y D k c)
    (hc : c < c') : aux_sdp_sN Y D k c' = aux_sdp_sN Y D (k+1) c' := by
  have h0 := aux_sdp_Q4 Y D k c h hpos
  obtain ⟨t, rfl⟩ : ∃ t, c' = k + ((c - k) + t) + 1 := ⟨c' - c - 1, by omega⟩
  have hv := aux_sdp_Q3v Y D k (c - k) h0 t
  rw [(aux_sdp_F1 Y D k _).1, hv, min_eq_right (aux_sdp_sN_nonneg Y D (k+1) _ (by omega))]
  simp

theorem aux_sdp_Q6 (Y D : ℕ → ℝ) (c c' : ℕ) (hc : c < c') : ∀ g k, c - k = g → k ≤ c →
    0 < aux_sdp_sN Y D k c → aux_sdp_sN Y D k c' = aux_sdp_sN Y D (c+1) c'
  | 0, k, hg, hk, hpos => by
    have : k = c := by omega
    subst this
    exact aux_sdp_Q5 Y D k k c' le_rfl hpos hc
  | g+1, k, hg, hk, hpos => by
    rw [aux_sdp_Q5 Y D k c c' hk hpos hc]
    have hpos' : 0 < aux_sdp_sN Y D (k+1) c :=
      lt_of_lt_of_le hpos (aux_sdp_mono Y D k c (by omega))
    exact aux_sdp_Q6 Y D c c' hc g (k+1) (by omega) (by omega) hpos'

variable {N : ℕ}

theorem aux_sdp_sh_eq (y d : Fin N → ℝ) (k : ℕ) (m : Fin N) (h : k ≤ m.val) :
    shortage y d k m = aux_sdp_sN (extend y) (extend d) k m.val := by
  simp [shortage, h, aux_sdp_sN]

theorem aux_sdp_sh_nonneg (y d : Fin N → ℝ) (k : ℕ) (m : Fin N) : 0 ≤ shortage y d k m := by
  by_cases h : k ≤ m.val
  · rw [aux_sdp_sh_eq y d k m h]; exact aux_sdp_sN_nonneg _ _ _ _ h
  · simp [shortage, h]

theorem aux_sdp_sh_mono (y d : Fin N → ℝ) (k : ℕ) (m : Fin N) (h : k + 1 ≤ m.val) :
    shortage y d k m ≤ shortage y d (k+1) m := by
  rw [aux_sdp_sh_eq y d k m (by omega), aux_sdp_sh_eq y d (k+1) m h]
  exact aux_sdp_mono _ _ _ _ h

theorem aux_sdp_sh_Q5 (y d : Fin N → ℝ) (k : ℕ) (c c' : Fin N) (hk : k ≤ c.val)
    (hpos : 0 < shortage y d k c) (hc : c.val < c'.val) :
    shortage y d k c' = shortage y d (k+1) c' := by
  rw [aux_sdp_sh_eq y d k c hk] at hpos
  rw [aux_sdp_sh_eq y d k c' (by omega), aux_sdp_sh_eq y d (k+1) c' (by omega)]
  exact aux_sdp_Q5 _ _ _ _ _ hk hpos hc

theorem aux_sdp_sh_Q6 (y d : Fin N → ℝ) (k : ℕ) (c c' : Fin N) (hk : k ≤ c.val)
    (hpos : 0 < shortage y d k c) (hc : c.val < c'.val) :
    shortage y d k c' = shortage y d (c.val+1) c' := by
  rw [aux_sdp_sh_eq y d k c hk] at hpos
  rw [aux_sdp_sh_eq y d k c' (by omega), aux_sdp_sh_eq y d (c.val+1) c' (by omega)]
  exact aux_sdp_Q6 _ _ _ _ hc _ k rfl hk hpos

theorem aux_sdp_sub (y d : Fin N → ℝ) (j i : Fin N) (hji : j < i)
    (hd : ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)) :
    ¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1) := by
  have hji' : j.val < i.val := hji
  obtain ⟨h1, h2⟩ := hd
  refine ⟨fun H => h1 (fun m hm1 hm2 => H m (by omega) hm2), ?_⟩
  intro m hm1 hm2
  rcases Nat.eq_or_lt_of_le hm1 with heq | hlt
  · have hmi : m = i := Fin.ext heq.symm
    subst hmi
    by_contra hne
    have hpos : 0 < shortage y d j m := lt_of_le_of_ne (aux_sdp_sh_nonneg _ _ _ _) (Ne.symm hne)
    apply h1
    intro m' hm1' hm2'
    rw [← aux_sdp_sh_Q5 y d j m m' (by omega) hpos (by omega)]
    exact h2 m' hm1' hm2'
  · exact h2 m (by omega) hm2

theorem aux_sdp_diff (y d : Fin N → ℝ) (j i : Fin N) (hji : j < i) :
    ((¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1)) ∧
      ¬ (¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1))) ↔
    ((0 < shortage y d (j + 1) i ∧ ShortVecZero y d j j i) ∧
      ShortVecZero y d (i + 1) (i + 1) (N - 1)) := by
  have hji' : j.val < i.val := hji
  have hiN : i.val < N := i.isLt
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 : ShortVecZero y d (j + 1) (i + 1) (N - 1) := by
      by_contra h
      exact h3 ⟨h, fun m hm1 hm2 => h2 m (by omega) hm2⟩
    have hsi : shortage y d (j + 1) i ≠ 0 := by
      intro h0
      apply h1
      intro m hm1 hm2
      rcases Nat.eq_or_lt_of_le hm1 with heq | hlt
      · have hmi : m = i := Fin.ext heq.symm
        rw [hmi]; exact h0
      · exact h4 m hlt hm2
    have hpos : 0 < shortage y d (j + 1) i :=
      lt_of_le_of_ne (aux_sdp_sh_nonneg _ _ _ _) (Ne.symm hsi)
    have h2i : shortage y d j i = 0 := h2 i le_rfl (by omega)
    refine ⟨⟨hpos, ?_⟩, ?_⟩
    · intro m hm1 hm2
      rcases Nat.eq_or_lt_of_le hm2 with heq | hlt
      · have hmi : m = i := Fin.ext heq
        rw [hmi]; exact h2i
      · by_contra hne
        have hp : 0 < shortage y d j m :=
          lt_of_le_of_ne (aux_sdp_sh_nonneg _ _ _ _) (Ne.symm hne)
        have := aux_sdp_sh_Q5 y d j m i hm1 hp hlt
        rw [this] at h2i
        exact hsi h2i
    · intro m hm1 hm2
      rw [← aux_sdp_sh_Q6 y d (j + 1) i m (by omega) hpos (by omega)]
      exact h4 m (by omega) hm2
  · rintro ⟨⟨hpos, h2⟩, h3⟩
    have hQ6 : ∀ m : Fin N, i.val < m.val →
        shortage y d (j + 1) m = shortage y d (i.val + 1) m :=
      fun m hm => aux_sdp_sh_Q6 y d (j + 1) i m (by omega) hpos hm
    have h4 : ShortVecZero y d (j + 1) (i + 1) (N - 1) := by
      intro m hm1 hm2
      rw [hQ6 m (by omega)]
      exact h3 m hm1 hm2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro H
      have := H i le_rfl (by omega)
      rw [this] at hpos
      exact lt_irrefl _ hpos
    · intro m hm1 hm2
      rcases Nat.eq_or_lt_of_le hm1 with heq | hlt
      · have hmi : m = i := Fin.ext heq.symm
        rw [hmi]; exact h2 i (by omega) le_rfl
      · have e1 := aux_sdp_sh_mono y d j m (by omega)
        have e2 := h4 m hlt hm2
        have e3 := aux_sdp_sh_nonneg y d j m
        linarith
    · rintro ⟨h5, _⟩
      exact h5 h4

/-! Measurability -/

theorem aux_sdp_inner_meas (i : ℕ) : ∀ (m p : ℕ) (st : (Fin N → ℝ) → AlgState),
    (∀ a, Measurable fun d => (st d).v a) → (∀ a, Measurable fun d => (st d).u a) →
    (∀ a, Measurable fun d => (innerLoop i m p (st d)).v a) ∧
    (∀ a, Measurable fun d => (innerLoop i m p (st d)).u a)
  | 0, p, st, hv, hu => ⟨hv, hu⟩
  | m+1, p, st, hv, hu => by
    simp only [aux_sdp_inner_succ]
    apply aux_sdp_inner_meas i m (p-1) (fun d => aux_sdp_step i p (st d))
    · intro a
      by_cases hap : a = p
      · subst hap
        simp only [aux_sdp_step, Function.update_self]
        exact (hv a).sub ((hu i).min (hv a))
      · simp only [aux_sdp_step, Function.update_of_ne hap]
        exact hv a
    · intro a
      by_cases hai : a = i
      · subst hai
        simp only [aux_sdp_step, Function.update_self]
        exact (hu a).sub ((hu a).min (hv p))
      · simp only [aux_sdp_step, Function.update_of_ne hai]
        exact hu a

theorem aux_sdp_run_meas (k : ℕ) (Y : ℕ → ℝ) (D : (Fin N → ℝ) → ℕ → ℝ)
    (hD : ∀ a, Measurable fun d => D d a) : ∀ n,
    (∀ a, Measurable fun d => (runFrom k Y (D d) n).v a) ∧
    (∀ a, Measurable fun d => (runFrom k Y (D d) n).u a)
  | 0 => ⟨fun a => by simp [runFrom], fun a => by simp [runFrom]⟩
  | n+1 => by
    obtain ⟨hv, hu⟩ := aux_sdp_run_meas k Y D hD n
    simp only [aux_sdp_runFrom_succ]
    apply aux_sdp_inner_meas
    · intro a; exact hv a
    · intro a
      by_cases ha : a = k + n
      · subst ha
        simp only [Function.update_self]
        exact hD _
      · simp only [Function.update_of_ne ha]
        exact hu a

theorem aux_sdp_sh_meas (y : Fin N → ℝ) (k : ℕ) (m : Fin N) :
    Measurable fun d : Fin N → ℝ => shortage y d k m := by
  by_cases h : k ≤ m.val
  · simp only [shortage, h, if_true]
    refine (aux_sdp_run_meas k (extend y) (fun d => extend d) (fun a => ?_) _).2 _
    by_cases ha : a < N
    · simp only [extend, ha, dite_true]
      exact measurable_pi_apply _
    · simp only [extend, ha, dite_false]
      exact measurable_const
  · simp only [shortage, h, if_false]
    exact measurable_const

theorem aux_sdp_svz_meas (y : Fin N → ℝ) (k a n : ℕ) :
    MeasurableSet {d : Fin N → ℝ | ShortVecZero y d k a n} := by
  simp only [ShortVecZero]
  refine Measurable.setOf (Measurable.forall fun m => Measurable.imp measurable_const
    (Measurable.imp measurable_const ?_))
  exact measurableSet_setOfPred.1 (measurableSet_eq_fun (aux_sdp_sh_meas y k m) measurable_const)

/-! Locality -/

theorem aux_sdp_run_local (k : ℕ) (Y D D' : ℕ → ℝ) : ∀ n,
    (∀ t, t < n → D (k+t) = D' (k+t)) → runFrom k Y D n = runFrom k Y D' n
  | 0, _ => rfl
  | n+1, h => by
    rw [aux_sdp_runFrom_succ, aux_sdp_runFrom_succ,
      aux_sdp_run_local k Y D D' n (fun t ht => h t (by omega)), h n (by omega)]

theorem aux_sdp_sh_local (y d d' : Fin N → ℝ) (k : ℕ) (m : Fin N)
    (h : ∀ a : Fin N, k ≤ a.val → a.val ≤ m.val → d a = d' a) :
    shortage y d k m = shortage y d' k m := by
  unfold shortage
  split_ifs with hk
  · rw [aux_sdp_run_local k (extend y) (extend d) (extend d') _ ?_]
    intro t ht
    simp only [extend]
    split_ifs with hN
    · exact h ⟨k+t, hN⟩ (by simp) (by simp; omega)
    · rfl
  · rfl

theorem aux_sdp_svz_local (y d d' : Fin N → ℝ) (k a n : ℕ)
    (h : ∀ b : Fin N, k ≤ b.val → b.val ≤ n → d b = d' b) :
    ShortVecZero y d k a n → ShortVecZero y d' k a n := by
  intro H m hm1 hm2
  rw [← aux_sdp_sh_local y d d' k m (fun b hb1 hb2 => h b hb1 (le_trans hb2 hm2))]
  exact H m hm1 hm2

/-! Independence -/

theorem aux_sdp_indep (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (S T : Finset (Fin N)) (hST : Disjoint S T) (E F : Set (Fin N → ℝ))
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEl : ∀ d d', (∀ a ∈ S, d a = d' a) → d ∈ E → d' ∈ E)
    (hFl : ∀ d d', (∀ a ∈ T, d a = d' a) → d ∈ F → d' ∈ F) :
    (Measure.pi ν).real (E ∩ F) = (Measure.pi ν).real E * (Measure.pi ν).real F := by
  have hind : ProbabilityTheory.iIndepFun (fun i (ω : Fin N → ℝ) => ω i) (Measure.pi ν) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  let eS : (S → ℝ) → (Fin N → ℝ) := fun x a => if h : a ∈ S then x ⟨a, h⟩ else 0
  let eT : (T → ℝ) → (Fin N → ℝ) := fun x a => if h : a ∈ T then x ⟨a, h⟩ else 0
  have meS : Measurable eS := by
    refine measurable_pi_lambda _ fun a => ?_
    by_cases h : a ∈ S
    · simp only [eS, h, dite_true]; exact measurable_pi_apply _
    · simp only [eS, h, dite_false]; exact measurable_const
  have meT : Measurable eT := by
    refine measurable_pi_lambda _ fun a => ?_
    by_cases h : a ∈ T
    · simp only [eT, h, dite_true]; exact measurable_pi_apply _
    · simp only [eT, h, dite_false]; exact measurable_const
  have hE' : (fun ω (a : S) => ω a) ⁻¹' (eS ⁻¹' E) = E := by
    ext ω
    simp only [Set.mem_preimage]
    constructor
    · intro h; exact hEl _ ω (fun a ha => by simp [eS, ha]) h
    · intro h; exact hEl ω _ (fun a ha => by simp [eS, ha]) h
  have hF' : (fun ω (a : T) => ω a) ⁻¹' (eT ⁻¹' F) = F := by
    ext ω
    simp only [Set.mem_preimage]
    constructor
    · intro h; exact hFl _ ω (fun a ha => by simp [eT, ha]) h
    · intro h; exact hFl ω _ (fun a ha => by simp [eT, ha]) h
  have key := h2.measure_inter_preimage_eq_mul _ _ (meS hE) (meT hF)
  rw [hE', hF'] at key
  simp only [Measure.real, key, ENNReal.toReal_mul]

end BassokSubstitution

open BassokSubstitution

theorem solution {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (j i : Fin N) (hji : j < i) :
    (Measure.pi ν).real
        {d | ¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1)}
      - (Measure.pi ν).real
        {d | ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)}
      = (Measure.pi ν).real {d | 0 < shortage y d (j + 1) i ∧ ShortVecZero y d j j i}
        * (Measure.pi ν).real {d | ShortVecZero y d (i + 1) (i + 1) (N - 1)} := by
  have hji' : j.val < i.val := hji
  have hsub : {d | ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)}
      ⊆ {d | ¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1)} :=
    fun d hd => aux_sdp_sub y d j i hji hd
  have hA2m : MeasurableSet
      {d | ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)} :=
    (aux_sdp_svz_meas y _ _ _).compl.inter (aux_sdp_svz_meas y _ _ _)
  rw [← measureReal_sdiff hsub hA2m]
  have hset : {d | ¬ ShortVecZero y d (j + 1) i (N - 1) ∧ ShortVecZero y d j i (N - 1)} \
      {d | ¬ ShortVecZero y d (j + 1) (i + 1) (N - 1) ∧ ShortVecZero y d j (i + 1) (N - 1)}
      = {d | 0 < shortage y d (j + 1) i ∧ ShortVecZero y d j j i} ∩
        {d | ShortVecZero y d (i + 1) (i + 1) (N - 1)} := by
    ext d
    exact aux_sdp_diff y d j i hji
  rw [hset]
  refine aux_sdp_indep ν (Finset.univ.filter (fun a : Fin N => a.val ≤ i.val))
    (Finset.univ.filter (fun a : Fin N => i.val < a.val)) ?_ _ _
    ((measurableSet_lt measurable_const (aux_sdp_sh_meas y _ _)).inter (aux_sdp_svz_meas y _ _ _))
    (aux_sdp_svz_meas y _ _ _) ?_ ?_
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    omega
  · rintro d d' hdd' ⟨h1, h2⟩
    have hloc : ∀ a : Fin N, a.val ≤ i.val → d a = d' a := fun a ha =>
      hdd' a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩)
    refine ⟨?_, ?_⟩
    · rw [← aux_sdp_sh_local y d d' (j + 1) i (fun a _ ha2 => hloc a ha2)]
      exact h1
    · exact aux_sdp_svz_local y d d' j j i (fun b _ hb2 => hloc b hb2) h2
  · intro d d' hdd' h
    have hloc : ∀ a : Fin N, i.val < a.val → d a = d' a := fun a ha =>
      hdd' a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩)
    exact aux_sdp_svz_local y d d' (i + 1) (i + 1) (N - 1) (fun b hb1 _ => hloc b (by omega)) h
