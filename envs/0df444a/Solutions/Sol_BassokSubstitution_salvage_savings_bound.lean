-- Prove2me | solution 1 for BassokSubstitution.salvage_savings_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:25:10.419221+00:00
-- url     : https://prove2.me/submissions/1fb776dc-1388-40a5-acc4-bb12b73f65ce

import Mathlib
import Definitions.Def_BassokSubstitution_Profit
open MeasureTheory
namespace BassokSubstitution

noncomputable def aux_bss_T (Y D : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max 0 (aux_bss_T Y D k n + Y (k + n) - D (k + n))

lemma aux_bss_innerLoop (i k : ℕ) : ∀ (n : ℕ) (st : AlgState),
    (∀ j, k ≤ j → j ≤ k + n → 0 ≤ st.v j) →
    (innerLoop i (n+1) (k+n) st).u i = max 0 (st.u i - ∑ j ∈ Finset.Icc k (k+n), st.v j) ∧
    ∑ j ∈ Finset.Icc k (k+n), (innerLoop i (n+1) (k+n) st).v j
        = max 0 (∑ j ∈ Finset.Icc k (k+n), st.v j - st.u i) ∧
    (∀ j, k ≤ j → j ≤ k + n → 0 ≤ (innerLoop i (n+1) (k+n) st).v j) ∧
    (∀ j, (j < k ∨ k + n < j) → (innerLoop i (n+1) (k+n) st).v j = st.v j) := by
  intro n
  induction n with
  | zero =>
    intro st hv
    simp only [innerLoop, Nat.add_zero, Finset.Icc_self, Finset.sum_singleton,
      Function.update_self]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases le_total (st.u i) (st.v k) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]; ring
      · rw [min_eq_right h, max_eq_right (by linarith)]
    · rcases le_total (st.u i) (st.v k) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    · intro j hj1 hj2
      have : j = k := by omega
      subst this
      simp only [Function.update_self]
      linarith [min_le_right (st.u i) (st.v j)]
    · intro j hj
      rw [Function.update_of_ne (by omega)]
  | succ n ih =>
    intro st hv
    set J := k + (n + 1) with hJ
    set st1 : AlgState :=
      { v := Function.update st.v J (st.v J - min (st.u i) (st.v J))
        u := Function.update st.u i (st.u i - min (st.u i) (st.v J))
        w := Function.update st.w J (Function.update (st.w J) i (min (st.u i) (st.v J))) }
      with hst1
    have e : J - 1 = k + n := by omega
    have hunf : innerLoop i (n+1+1) J st = innerLoop i (n+1) (k+n) st1 := by
      rw [innerLoop, e]
    have hv1 : ∀ j, k ≤ j → j ≤ k + n → 0 ≤ st1.v j := by
      intro j hj1 hj2
      simp only [st1]
      rw [Function.update_of_ne (by omega)]
      exact hv j hj1 (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := ih st1 hv1
    have hst1v : ∀ j ∈ Finset.Icc k (k+n), st1.v j = st.v j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      simp only [st1]
      rw [Function.update_of_ne (by omega)]
    have hsum1 : ∑ j ∈ Finset.Icc k (k+n), st1.v j = ∑ j ∈ Finset.Icc k (k+n), st.v j :=
      Finset.sum_congr rfl hst1v
    have hsplit : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.Icc k J, f j = ∑ j ∈ Finset.Icc k (k+n), f j + f J := by
      intro f
      rw [hJ, ← Nat.add_assoc, Finset.sum_Icc_succ_top (by omega)]
    have hS : 0 ≤ ∑ j ∈ Finset.Icc k (k+n), st.v j :=
      Finset.sum_nonneg (fun j hj => by rw [Finset.mem_Icc] at hj; exact hv j hj.1 (by omega))
    have hvJ : 0 ≤ st.v J := hv J (by omega) le_rfl
    have hu1 : st1.u i = st.u i - min (st.u i) (st.v J) := by simp [st1]
    have hvJ1 : st1.v J = st.v J - min (st.u i) (st.v J) := by simp [st1]
    rw [hunf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, hsum1, hu1, hsplit]
      rcases le_total (st.u i) (st.v J) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith), max_eq_left (by linarith)]
      · rw [min_eq_right h]; ring_nf
    · rw [hsplit, h2, hsum1, hu1, h4 J (by omega), hvJ1, hsplit]
      rcases le_total (st.u i) (st.v J) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith), max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, sub_self, add_zero]; ring_nf
    · intro j hj1 hj2
      by_cases hjJ : j = J
      · rw [hjJ, h4 J (by omega), hvJ1]
        linarith [min_le_right (st.u i) (st.v J)]
      · exact h3 j hj1 (by omega)
    · intro j hj
      rw [h4 j (by omega)]
      simp only [st1]
      rw [Function.update_of_ne (by omega)]

lemma aux_bss_runFrom (k : ℕ) (Y D : ℕ → ℝ) (hY : ∀ j, 0 ≤ Y j) : ∀ n,
    (∀ j, k + n ≤ j → (runFrom k Y D n).v j = Y j) ∧
    (∀ j, k ≤ j → j < k + n → 0 ≤ (runFrom k Y D n).v j) ∧
    ∑ j ∈ Finset.Ico k (k+n), (runFrom k Y D n).v j = aux_bss_T Y D k n ∧
    (runFrom k Y D (n+1)).u (k+n) = max 0 (D (k+n) - Y (k+n) - aux_bss_T Y D k n) := by
  intro n
  induction n with
  | zero =>
    set st := runFrom k Y D 0 with hst
    set st0 : AlgState := { st with u := Function.update st.u (k + 0) (D (k + 0)) } with hst0
    have hv : ∀ j, k ≤ j → j ≤ k + 0 → 0 ≤ st0.v j := by
      intro j _ _; exact hY j
    obtain ⟨h1, -, -, -⟩ := aux_bss_innerLoop (k+0) k 0 st0 hv
    have hrf : runFrom k Y D (0+1) = innerLoop (k + 0) (0 + 1) (k + 0) st0 := rfl
    refine ⟨fun j _ => rfl, fun j h1 h2 => by omega, by simp [aux_bss_T], ?_⟩
    rw [hrf, h1]
    have hu0 : st0.u (k + 0) = D (k + 0) := by simp [st0]
    have hv0 : st0.v k = Y k := rfl
    simp only [Nat.add_zero, Finset.Icc_self, Finset.sum_singleton] at hu0 ⊢
    rw [hu0, hv0]
    simp [aux_bss_T]
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    set st := runFrom k Y D n with hst
    set st0 : AlgState := { st with u := Function.update st.u (k + n) (D (k + n)) } with hst0
    have hv : ∀ j, k ≤ j → j ≤ k + n → 0 ≤ st0.v j := by
      intro j hj1 hj2
      show 0 ≤ st.v j
      rcases Nat.lt_or_ge j (k + n) with h | h
      · exact ih2 j hj1 h
      · rw [ih1 j h]; exact hY j
    have hrf : runFrom k Y D (n+1) = innerLoop (k + n) (n + 1) (k + n) st0 := rfl
    obtain ⟨g1, g2, g3, g4⟩ := aux_bss_innerLoop (k+n) k n st0 hv
    have hIco : Finset.Ico k (k + (n+1)) = Finset.Icc k (k + n) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    have hsum0 : ∑ j ∈ Finset.Icc k (k+n), st0.v j = aux_bss_T Y D k n + Y (k + n) := by
      show ∑ j ∈ Finset.Icc k (k+n), st.v j = _
      rw [show Finset.Icc k (k+n) = Finset.Ico k (k+n+1) by
          ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega,
        Finset.sum_Ico_succ_top (by omega), ih3,
        ih1 (k+n) le_rfl]
    have hu0 : st0.u (k + n) = D (k + n) := by simp [st0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hrf, g4 j (by omega)]
      exact ih1 j (by omega)
    · intro j hj1 hj2
      rw [hrf]; exact g3 j hj1 (by omega)
    · rw [hIco, hrf, g2, hsum0, hu0]
      simp only [aux_bss_T]
    · -- next step
      set st' := runFrom k Y D (n+1) with hst'
      set st0' : AlgState := { st' with u := Function.update st'.u (k + (n+1)) (D (k + (n+1))) }
        with hst0'
      have hv' : ∀ j, k ≤ j → j ≤ k + (n+1) → 0 ≤ st0'.v j := by
        intro j hj1 hj2
        show 0 ≤ st'.v j
        rcases Nat.lt_or_ge j (k + (n+1)) with h | h
        · rw [hrf]; exact g3 j hj1 (by omega)
        · rw [hrf, g4 j (by omega)]; show 0 ≤ st.v j; rw [ih1 j (by omega)]; exact hY j
      have hrf' : runFrom k Y D (n+1+1) = innerLoop (k + (n+1)) (n + 1 + 1) (k + (n+1)) st0' := rfl
      obtain ⟨f1, -, -, -⟩ := aux_bss_innerLoop (k+(n+1)) k (n+1) st0' hv'
      have hsum0' : ∑ j ∈ Finset.Icc k (k+(n+1)), st0'.v j
          = aux_bss_T Y D k (n+1) + Y (k + (n+1)) := by
        show ∑ j ∈ Finset.Icc k (k+(n+1)), st'.v j = _
        rw [show Finset.Icc k (k+(n+1)) = Finset.Ico k (k+(n+1)+1) by
          ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega,
          Finset.sum_Ico_succ_top (by omega)]
        have e1 : ∑ j ∈ Finset.Ico k (k + (n+1)), st'.v j = aux_bss_T Y D k (n+1) := by
          rw [hIco, hrf, g2, hsum0, hu0]; simp only [aux_bss_T]
        have e2 : st'.v (k + (n+1)) = Y (k + (n+1)) := by
          rw [hrf, g4 _ (by omega)]; exact ih1 _ (by omega)
        rw [e1, e2]
      have hu0' : st0'.u (k + (n+1)) = D (k + (n+1)) := by simp [st0']
      rw [hrf', f1, hsum0', hu0']
      ring_nf

lemma aux_bss_T_nonneg (Y D : ℕ → ℝ) (k n : ℕ) : 0 ≤ aux_bss_T Y D k n := by
  cases n with
  | zero => simp [aux_bss_T]
  | succ n => simp only [aux_bss_T]; exact le_max_left _ _

lemma aux_bss_T_mono (Y D : ℕ → ℝ) (k a : ℕ) :
    ∀ n, aux_bss_T Y D (k + a) n ≤ aux_bss_T Y D k (a + n) := by
  intro n
  induction n with
  | zero => simp only [aux_bss_T]; exact aux_bss_T_nonneg _ _ _ _
  | succ n ih =>
    rw [show a + (n+1) = (a + n) + 1 by omega]
    simp only [aux_bss_T]
    rw [show k + a + n = k + (a + n) by omega]
    exact max_le_max le_rfl (by linarith)

lemma aux_bss_T_eq (Y D : ℕ → ℝ) (k a n0 : ℕ)
    (h : aux_bss_T Y D k (a + n0) = aux_bss_T Y D (k + a) n0) :
    ∀ m, aux_bss_T Y D k (a + n0 + m) = aux_bss_T Y D (k + a) (n0 + m) := by
  intro m
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [show a + n0 + (m+1) = (a + n0 + m) + 1 by omega, show n0 + (m+1) = (n0+m)+1 by omega]
    simp only [aux_bss_T]
    rw [ih, show k + (a + n0 + m) = k + a + (n0 + m) by omega]

lemma aux_bss_T_congr (Y Y' D : ℕ → ℝ) (k : ℕ) : ∀ n, (∀ j, j < k + n → Y j = Y' j) →
    aux_bss_T Y D k n = aux_bss_T Y' D k n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [aux_bss_T]
    rw [ih (fun j hj => h j (by omega)), h (k+n) (by omega)]

lemma aux_bss_extend_nonneg {N : ℕ} (y : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (j : ℕ) :
    0 ≤ extend y j := by
  unfold extend; split_ifs
  · exact hy _
  · exact le_rfl

lemma aux_bss_extend_val {N : ℕ} (y : Fin N → ℝ) (c : Fin N) : extend y c.val = y c := by
  simp [extend, c.isLt]

lemma aux_bss_shortage {N : ℕ} (y d : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (k : ℕ) (c : Fin N)
    (hkc : k ≤ c.val) :
    shortage y d k c = max 0 (d c - y c - aux_bss_T (extend y) (extend d) k (c.val - k)) := by
  unfold shortage
  rw [if_pos hkc, show c.val + 1 - k = (c.val - k) + 1 by omega]
  have h := (aux_bss_runFrom k (extend y) (extend d) (aux_bss_extend_nonneg y hy)
    (c.val - k)).2.2.2
  rw [show k + (c.val - k) = c.val by omega, aux_bss_extend_val, aux_bss_extend_val] at h
  exact h

lemma aux_bss_shortage_nonneg {N : ℕ} (y d : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (k : ℕ)
    (c : Fin N) : 0 ≤ shortage y d k c := by
  by_cases hkc : k ≤ c.val
  · rw [aux_bss_shortage y d hy k c hkc]; exact le_max_left _ _
  · unfold shortage; rw [if_neg hkc]

lemma aux_bss_shortage_mono {N : ℕ} (y d : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (k k' : ℕ)
    (c : Fin N) (hk : k ≤ k') (hk' : k' ≤ c.val) :
    shortage y d k c ≤ shortage y d k' c := by
  rw [aux_bss_shortage y d hy k c (by omega), aux_bss_shortage y d hy k' c hk']
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  have := aux_bss_T_mono (extend y) (extend d) k a (c.val - (k + a))
  rw [show a + (c.val - (k+a)) = c.val - k by omega] at this
  exact max_le_max le_rfl (by linarith)

lemma aux_bss_F3 {N : ℕ} (y d : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (k : ℕ) (c c' : Fin N)
    (hkc : k ≤ c.val) (hcc : c.val < c'.val)
    (hpos : 0 < shortage y d k c) : shortage y d k c' = shortage y d (k+1) c' := by
  rw [aux_bss_shortage y d hy k c hkc] at hpos
  have hx : 0 < d c - y c - aux_bss_T (extend y) (extend d) k (c.val - k) := by
    rcases le_or_gt (d c - y c - aux_bss_T (extend y) (extend d) k (c.val - k)) 0 with h | h
    · rw [max_eq_left h] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have hT0 : aux_bss_T (extend y) (extend d) k (1 + (c.val - k)) = 0 := by
    rw [add_comm]; simp only [aux_bss_T]
    rw [show k + (c.val - k) = c.val by omega, aux_bss_extend_val, aux_bss_extend_val]
    apply max_eq_left; linarith
  have hT1 : aux_bss_T (extend y) (extend d) k (1 + (c.val - k))
      = aux_bss_T (extend y) (extend d) (k+1) (c.val - k) := by
    have := aux_bss_T_mono (extend y) (extend d) k 1 (c.val - k)
    have := aux_bss_T_nonneg (extend y) (extend d) (k+1) (c.val - k)
    linarith
  have := aux_bss_T_eq (extend y) (extend d) k 1 (c.val - k) hT1 (c'.val - 1 - c.val)
  rw [show 1 + (c.val - k) + (c'.val - 1 - c.val) = c'.val - k by omega,
      show c.val - k + (c'.val - 1 - c.val) = c'.val - (k+1) by omega] at this
  rw [aux_bss_shortage y d hy k c' (by omega), aux_bss_shortage y d hy (k+1) c' (by omega), this]

lemma aux_bss_upd_nonneg {N : ℕ} (y : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (i : Fin N) (s : ℝ)
    (hs : 0 ≤ s) : ∀ j, 0 ≤ Function.update y i s j := by
  intro j
  by_cases hj : j = i
  · subst hj; simp [hs]
  · rw [Function.update_of_ne hj]; exact hy j

lemma aux_bss_F4 {N : ℕ} (y d : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (i : Fin N) (k : ℕ)
    (hk : k ≤ i.val) (t t' : ℝ) (ht : 0 ≤ t) (htt : t ≤ t')
    (h0 : shortage (Function.update y i t) d k i = 0) :
    shortage (Function.update y i t') d k i = 0 := by
  have hT : ∀ s : ℝ, aux_bss_T (extend (Function.update y i s)) (extend d) k (i.val - k)
      = aux_bss_T (extend y) (extend d) k (i.val - k) := by
    intro s
    apply aux_bss_T_congr
    intro j hj
    unfold extend
    split_ifs with hjN
    · rw [Function.update_of_ne]
      intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
    · rfl
  rw [aux_bss_shortage _ d (aux_bss_upd_nonneg y hy i t ht) k i hk, hT,
    Function.update_self] at h0
  rw [aux_bss_shortage _ d (aux_bss_upd_nonneg y hy i t' (le_trans ht htt)) k i hk, hT,
    Function.update_self]
  apply max_eq_left
  have : d i - t - aux_bss_T (extend y) (extend d) k (i.val - k) ≤ 0 := by
    rw [← h0]; exact le_max_right _ _
  linarith

lemma aux_bss_zero_of_le {N : ℕ} (Y d : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j) (k k' : ℕ) (i : Fin N)
    (hk : k ≤ k') (hk' : k' ≤ i.val) (h : shortage Y d k' i = 0) : shortage Y d k i = 0 :=
  le_antisymm (h ▸ aux_bss_shortage_mono Y d hY k k' i hk hk') (aux_bss_shortage_nonneg Y d hY k i)

lemma aux_bss_Bcond {N : ℕ} (Y d : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j) (m i : Fin N) (hmi : m < i) :
    (0 < shortage Y d (↑m + 1) i ∧ ShortVecZero Y d m m i) ↔
      (shortage Y d m i = 0 ∧ shortage Y d (↑m + 1) i ≠ 0) := by
  have hmi' : m.val < i.val := hmi
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 i hmi'.le le_rfl, ne_of_gt h1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨lt_of_le_of_ne (aux_bss_shortage_nonneg Y d hY _ i) (Ne.symm h2), ?_⟩
    intro c hc1 hc2
    rcases lt_or_eq_of_le hc2 with hlt | heq
    · by_contra hne
      have hpos : 0 < shortage Y d m c :=
        lt_of_le_of_ne (aux_bss_shortage_nonneg Y d hY _ c) (Ne.symm hne)
      have := aux_bss_F3 Y d hY m c i hc1 hlt hpos
      exact h2 (this ▸ h1)
    · have : c = i := Fin.ext heq
      subst this; exact h1

def aux_bss_A {N : ℕ} (Y : Fin N → ℝ) (i : Fin N) : Set (Fin N → ℝ) :=
  {d | shortage Y d i i = 0}

def aux_bss_B {N : ℕ} (Y : Fin N → ℝ) (i m : Fin N) : Set (Fin N → ℝ) :=
  {d | 0 < shortage Y d (↑m + 1) i ∧ ShortVecZero Y d m m i}

noncomputable def aux_bss_G {N : ℕ} [NeZero N] (M : Model N) (Y : Fin N → ℝ) (i : Fin N)
    (d : Fin N → ℝ) : ℝ :=
  M.s 0 * ((aux_bss_A Y i).indicator 1 d
      + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i), (aux_bss_B Y i m).indicator 1 d)
    - (M.s i * (aux_bss_A Y i).indicator 1 d
      + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i), M.s m * (aux_bss_B Y i m).indicator 1 d)

lemma aux_bss_val {N : ℕ} [NeZero N] (M : Model N) (Y d : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j)
    (i : Fin N) :
    (shortage Y d 0 i ≠ 0 ∧ aux_bss_G M Y i d = 0) ∨
    ∃ m : Fin N, m ≤ i ∧ shortage Y d m i = 0 ∧ (m = i ∨ shortage Y d (↑m + 1) i ≠ 0) ∧
      aux_bss_G M Y i d = M.s 0 - M.s m := by
  by_cases h0 : shortage Y d 0 i = 0
  · right
    obtain ⟨m, hmi, hm0, hm1⟩ : ∃ m : ℕ, m ≤ i.val ∧ shortage Y d m i = 0 ∧
        (m = i.val ∨ shortage Y d (m+1) i ≠ 0) := by
      by_contra hne
      push_neg at hne
      have : ∀ n, n ≤ i.val → shortage Y d n i = 0 := by
        intro n
        induction n with
        | zero => intro _; exact h0
        | succ n ih => intro hn; exact (hne n (by omega) (ih (by omega))).2
      exact (hne i.val le_rfl (this i.val le_rfl)).1 rfl
    have hmN : m < N := lt_of_le_of_lt hmi i.isLt
    set mf : Fin N := ⟨m, hmN⟩ with hmf
    have hmfv : mf.val = m := rfl
    refine ⟨mf, hmi, hm0, ?_, ?_⟩
    · rcases hm1 with h | h
      · left; exact Fin.ext h
      · right; exact h
    rcases hm1 with heq | hne
    · -- m = i
      have hmi_eq : mf = i := Fin.ext heq
      have hA : d ∈ aux_bss_A Y i := by
        show shortage Y d i i = 0
        rw [← heq]; exact hm0
      have hB : ∀ m' ∈ Finset.univ.filter (fun m : Fin N => m < i), d ∉ aux_bss_B Y i m' := by
        intro m' hm' hB
        rw [Finset.mem_filter] at hm'
        have hm'' : m'.val < i.val := hm'.2
        rw [aux_bss_B, Set.mem_setOf_eq, aux_bss_Bcond Y d hY m' i hm'.2] at hB
        exact hB.2 (aux_bss_zero_of_le Y d hY _ i.val i (by omega) le_rfl (heq ▸ hm0))
      unfold aux_bss_G
      rw [Set.indicator_of_mem hA, Finset.sum_eq_zero (fun m' hm' => by
        rw [Set.indicator_of_notMem (hB m' hm')]),
        Finset.sum_eq_zero (fun m' hm' => by rw [Set.indicator_of_notMem (hB m' hm'), mul_zero]),
        ← hmi_eq]
      simp
    · -- m < i
      have hmlt : m < i.val := by
        by_contra hge
        apply hne
        unfold shortage
        rw [if_neg (by omega)]
      have hA : d ∉ aux_bss_A Y i := by
        intro hA
        exact hne (aux_bss_zero_of_le Y d hY _ i.val i (by omega) le_rfl hA)
      have hBm : d ∈ aux_bss_B Y i mf := by
        rw [aux_bss_B, Set.mem_setOf_eq, aux_bss_Bcond Y d hY mf i hmlt]
        exact ⟨hm0, hne⟩
      have hB : ∀ m' ∈ Finset.univ.filter (fun m : Fin N => m < i), m' ≠ mf →
          d ∉ aux_bss_B Y i m' := by
        intro m' hm' hne' hB
        rw [Finset.mem_filter] at hm'
        have hm'' : m'.val < i.val := hm'.2
        rw [aux_bss_B, Set.mem_setOf_eq, aux_bss_Bcond Y d hY m' i hm'.2] at hB
        have hne'' : m'.val ≠ m := fun h => hne' (Fin.ext h)
        rcases Nat.lt_or_gt_of_ne hne'' with hlt | hgt
        · exact hB.2 (aux_bss_zero_of_le Y d hY _ m i (by omega) hmi hm0)
        · exact hne (aux_bss_zero_of_le Y d hY _ m'.val i (by omega) hm''.le hB.1)
      have hmem : mf ∈ Finset.univ.filter (fun m : Fin N => m < i) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmlt⟩
      unfold aux_bss_G
      rw [Set.indicator_of_notMem hA,
        Finset.sum_eq_single_of_mem mf hmem (fun m' hm' hne' => by
          rw [Set.indicator_of_notMem (hB m' hm' hne')]),
        Finset.sum_eq_single_of_mem mf hmem (fun m' hm' hne' => by
          rw [Set.indicator_of_notMem (hB m' hm' hne'), mul_zero]),
        Set.indicator_of_mem hBm]
      simp
  · left
    refine ⟨h0, ?_⟩
    have hA : d ∉ aux_bss_A Y i := by
      intro hA
      exact h0 (aux_bss_zero_of_le Y d hY 0 i.val i (by omega) le_rfl hA)
    have hB : ∀ m' ∈ Finset.univ.filter (fun m : Fin N => m < i), d ∉ aux_bss_B Y i m' := by
      intro m' hm' hB
      rw [Finset.mem_filter] at hm'
      have hm'' : m'.val < i.val := hm'.2
      rw [aux_bss_B, Set.mem_setOf_eq, aux_bss_Bcond Y d hY m' i hm'.2] at hB
      exact h0 (aux_bss_zero_of_le Y d hY 0 m'.val i (by omega) hm''.le hB.1)
    unfold aux_bss_G
    rw [Set.indicator_of_notMem hA, Finset.sum_eq_zero (fun m' hm' => by
        rw [Set.indicator_of_notMem (hB m' hm')]),
      Finset.sum_eq_zero (fun m' hm' => by rw [Set.indicator_of_notMem (hB m' hm'), mul_zero])]
    simp

lemma aux_bss_Gmono {N : ℕ} [NeZero N] (M : Model N) (hA2 : M.Assumption2)
    (y d : Fin N → ℝ) (hy : ∀ j, 0 ≤ y j) (i : Fin N) (t t' : ℝ) (ht : 0 ≤ t) (htt : t ≤ t') :
    aux_bss_G M (Function.update y i t) i d ≤ aux_bss_G M (Function.update y i t') i d := by
  have hY := aux_bss_upd_nonneg y hy i t ht
  have hY' := aux_bss_upd_nonneg y hy i t' (le_trans ht htt)
  have hsm : ∀ m m' : Fin N, m ≤ m' → M.s m' ≤ M.s m := by
    intro m m' h
    rcases eq_or_lt_of_le h with h | h
    · rw [h]
    · exact hA2 m m' h
  have hs0 : ∀ m : Fin N, M.s m ≤ M.s 0 := fun m => hsm 0 m (Fin.zero_le _)
  rcases aux_bss_val M _ d hY i with ⟨h1, g1⟩ | ⟨m, hmi, hm0, hm1, g1⟩ <;>
    rcases aux_bss_val M _ d hY' i with ⟨h2, g2⟩ | ⟨m', hmi', hm0', hm1', g2⟩
  · rw [g1, g2]
  · rw [g1, g2]; linarith [hs0 m']
  · exfalso
    have hmi'' : m.val ≤ i.val := hmi
    have := aux_bss_F4 y d hy i m hmi'' t t' ht htt hm0
    exact h2 (aux_bss_zero_of_le _ d hY' 0 m i (by omega) hmi'' this)
  · rw [g1, g2]
    have hmi'' : m.val ≤ i.val := hmi
    have hF := aux_bss_F4 y d hy i m hmi'' t t' ht htt hm0
    have hle : m ≤ m' := by
      by_contra hlt
      push_neg at hlt
      have hlt' : m'.val < m.val := hlt
      rcases hm1' with h | h
      · rw [h] at hlt'; omega
      · exact h (aux_bss_zero_of_le _ d hY' _ m i (by omega) hmi'' hF)
    linarith [hsm m m' hle]

lemma aux_bss_extend_cont {N : ℕ} (j : ℕ) : Continuous (fun d : Fin N → ℝ => extend d j) := by
  by_cases h : j < N
  · simp only [extend, h, dif_pos]; exact continuous_apply _
  · simp only [extend, h, dif_neg, not_false_eq_true]; exact continuous_const

lemma aux_bss_T_cont {N : ℕ} (Y : ℕ → ℝ) (k : ℕ) : ∀ n,
    Continuous (fun d : Fin N → ℝ => aux_bss_T Y (extend d) k n) := by
  intro n
  induction n with
  | zero => simp only [aux_bss_T]; exact continuous_const
  | succ n ih =>
    simp only [aux_bss_T]
    exact continuous_const.max ((ih.add continuous_const).sub (aux_bss_extend_cont _))

lemma aux_bss_shortage_cont {N : ℕ} (Y : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j) (k : ℕ) (c : Fin N) :
    Continuous (fun d => shortage Y d k c) := by
  by_cases hkc : k ≤ c.val
  · have : (fun d => shortage Y d k c) = fun d =>
        max 0 (d c - Y c - aux_bss_T (extend Y) (extend d) k (c.val - k)) :=
      funext fun d => aux_bss_shortage Y d hY k c hkc
    rw [this]
    exact continuous_const.max
      (((continuous_apply c).sub continuous_const).sub (aux_bss_T_cont _ _ _))
  · have : (fun d => shortage Y d k c) = fun _ => 0 :=
      funext fun d => by unfold shortage; rw [if_neg hkc]
    rw [this]; exact continuous_const

lemma aux_bss_A_meas {N : ℕ} (Y : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j) (i : Fin N) :
    MeasurableSet (aux_bss_A Y i) :=
  measurableSet_eq_fun (aux_bss_shortage_cont Y hY _ i).measurable measurable_const

lemma aux_bss_B_meas {N : ℕ} (Y : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j) (i m : Fin N) :
    MeasurableSet (aux_bss_B Y i m) := by
  unfold aux_bss_B ShortVecZero
  refine measurableSet_setOfPred.2 (Measurable.and (measurableSet_setOfPred.1
    (measurableSet_lt measurable_const (aux_bss_shortage_cont Y hY _ i).measurable))
    (Measurable.forall fun c => ?_))
  exact Measurable.imp measurable_const (Measurable.imp measurable_const
    (Measurable.eq (aux_bss_shortage_cont Y hY _ c).measurable measurable_const))

lemma aux_bss_integral {N : ℕ} [NeZero N] (M : Model N) (μ : Measure (Fin N → ℝ))
    [IsFiniteMeasure μ] (Y : Fin N → ℝ) (hY : ∀ j, 0 ≤ Y j) (i : Fin N) :
    Integrable (aux_bss_G M Y i) μ ∧
    ∫ d, aux_bss_G M Y i d ∂μ =
      M.s 0 * (μ.real (aux_bss_A Y i)
        + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i), μ.real (aux_bss_B Y i m))
      - (M.s i * μ.real (aux_bss_A Y i)
        + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i), M.s m * μ.real (aux_bss_B Y i m)) := by
  set S := Finset.univ.filter (fun m : Fin N => m < i) with hS
  have hIA : Integrable ((aux_bss_A Y i).indicator (1 : (Fin N → ℝ) → ℝ)) μ :=
    (integrable_const (1:ℝ)).indicator (aux_bss_A_meas Y hY i)
  have hIB : ∀ m, Integrable ((aux_bss_B Y i m).indicator (1 : (Fin N → ℝ) → ℝ)) μ :=
    fun m => (integrable_const (1:ℝ)).indicator (aux_bss_B_meas Y hY i m)
  have hs1 : Integrable (fun d => ∑ m ∈ S, (aux_bss_B Y i m).indicator (1 : (Fin N → ℝ) → ℝ) d) μ :=
    integrable_finsetSum _ fun m _ => hIB m
  have hs2 : Integrable (fun d => ∑ m ∈ S, M.s m * (aux_bss_B Y i m).indicator 1 d) μ :=
    integrable_finsetSum _ fun m _ => (hIB m).const_mul _
  have h1 : Integrable (fun d => (aux_bss_A Y i).indicator (1 : (Fin N → ℝ) → ℝ) d
      + ∑ m ∈ S, (aux_bss_B Y i m).indicator 1 d) μ := by
    have := hIA.add hs1
    exact this
  have h2 : Integrable (fun d => M.s i * (aux_bss_A Y i).indicator 1 d
      + ∑ m ∈ S, M.s m * (aux_bss_B Y i m).indicator 1 d) μ := (hIA.const_mul _).add hs2
  refine ⟨(h1.const_mul _).sub h2, ?_⟩
  have hA' : ∫ d, (aux_bss_A Y i).indicator 1 d ∂μ = μ.real (aux_bss_A Y i) :=
    integral_indicator_one (aux_bss_A_meas Y hY i)
  have hB' : ∀ m, ∫ d, (aux_bss_B Y i m).indicator 1 d ∂μ = μ.real (aux_bss_B Y i m) :=
    fun m => integral_indicator_one (aux_bss_B_meas Y hY i m)
  unfold aux_bss_G
  rw [integral_sub (h1.const_mul _) h2, integral_const_mul, integral_add hIA hs1,
    integral_add (hIA.const_mul _) hs2, integral_finsetSum _ (fun m _ => hIB m),
    integral_finsetSum _ (fun m _ => (hIB m).const_mul _), integral_const_mul]
  simp only [integral_const_mul, hA', hB']

end BassokSubstitution

open BassokSubstitution

theorem solution {N : ℕ} [NeZero N] (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (i : Fin N) :
    MonotoneOn
      (fun t : ℝ =>
        M.s 0 * ((Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
            + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i),
                (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                  ShortVecZero (Function.update y i t) d m m i})
          - (M.s i * (Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
            + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i),
                M.s m * (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                  ShortVecZero (Function.update y i t) d m m i}))
      (Set.Ici 0) := by
  have hy' : ∀ j, 0 ≤ y j := fun j => hy j
  intro t ht t' ht' htt
  have ht0 : 0 ≤ t := ht
  have ht0' : 0 ≤ t' := ht'
  have e := aux_bss_integral M (Measure.pi ν) (Function.update y i t)
    (aux_bss_upd_nonneg y hy' i t ht0) i
  have e' := aux_bss_integral M (Measure.pi ν) (Function.update y i t')
    (aux_bss_upd_nonneg y hy' i t' ht0') i
  simp only [aux_bss_A, aux_bss_B] at e e'
  dsimp only
  rw [← e.2, ← e'.2]
  exact integral_mono e.1 e'.1 (fun d => aux_bss_Gmono M hA2 y d hy' i t t' ht0 htt)
