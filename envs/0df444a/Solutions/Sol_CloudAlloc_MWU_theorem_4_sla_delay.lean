-- Prove2me | solution 1 for CloudAlloc.MWU.theorem_4_sla_delay
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:09:46.712171+00:00
-- url     : https://prove2.me/submissions/1e45e42c-9e15-4fc3-8d9f-423bcf37d4ff

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_userWork

namespace Aux_CA4

open CloudAlloc.MWU

/-- gradient inequality for `u ↦ u log (u / y)` -/
theorem grad (y u v : ℝ) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) :
    v * Real.log (v / y) + (Real.log (v / y) + 1) * (u - v) ≤ u * Real.log (u / y) := by
  rw [Real.log_div hu.ne' hy.ne', Real.log_div hv.ne' hy.ne']
  have h2 := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
  rw [inv_div, Real.log_div hu.ne' hv.ne'] at h2
  have h3 : u * (1 - v / u) = u - v := by field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hu.le
  rw [h3] at h4
  have key : u * (Real.log u - Real.log y) -
      (v * (Real.log v - Real.log y) + (Real.log v - Real.log y + 1) * (u - v)) =
      u * (Real.log u - Real.log v) - (u - v) := by ring
  linarith

/-- first-order optimality condition of the KL projection -/
theorem foc {N : ℕ} {ε : ℝ} (hεN : 0 < ε / N) (y x : Fin N → ℝ) (hy : ∀ k, 0 < y k)
    (hx : IsKLProj N ε y x) (i j : Fin N) (hj : ε / N < x j) : x j / y j ≤ x i / y i := by
  by_cases hij : i = j
  · rw [hij]
  by_contra hlt
  push_neg at hlt
  obtain ⟨hxT, hopt⟩ := hx
  obtain ⟨hsum, hlow⟩ := hxT
  have hyi := hy i
  have hyj := hy j
  set D := x j / y j - x i / y i with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  have hW : 0 < 1 / y i + 1 / y j := by positivity
  set s := min (x j - ε / N) (D / (2 * (1 / y i + 1 / y j))) with hs
  have hs1 : s ≤ x j - ε / N := min_le_left _ _
  have hs2 : s ≤ D / (2 * (1 / y i + 1 / y j)) := min_le_right _ _
  have hspos : 0 < s := lt_min (by linarith) (by positivity)
  let z : Fin N → ℝ := fun k => x k + (if k = i then s else 0) - (if k = j then s else 0)
  have hzi : z i = x i + s := by simp [z, hij]
  have hzj : z j = x j - s := by simp [z, Ne.symm hij]
  have hzk : ∀ k, k ≠ i → k ≠ j → z k = x k := by intro k h1 h2; simp [z, h1, h2]
  have hzlow : ∀ k, ε / N ≤ z k := by
    intro k
    by_cases h1 : k = i
    · rw [h1, hzi]; linarith [hlow i]
    · by_cases h2 : k = j
      · rw [h2, hzj]; linarith
      · rw [hzk k h1 h2]; exact hlow k
  have hzsum : ∑ k, z k = 1 := by
    simp only [z, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    linarith
  have hzT : z ∈ truncSimplex N ε := by
    show (∑ k, z k = 1) ∧ ∀ k, ε / N ≤ z k
    exact ⟨hzsum, hzlow⟩
  have h1 := hopt z hzT
  have hxpos : ∀ k, 0 < x k := fun k => lt_of_lt_of_le hεN (hlow k)
  have hzpos : ∀ k, 0 < z k := fun k => lt_of_lt_of_le hεN (hzlow k)
  have hterm : ∀ k, z k * Real.log (z k / y k) - x k * Real.log (x k / y k) ≤
      (Real.log (z k / y k) + 1) * ((if k = i then s else 0) - (if k = j then s else 0)) := by
    intro k
    have := grad (y k) (x k) (z k) (hy k) (hxpos k) (hzpos k)
    have e : z k - x k = (if k = i then s else 0) - (if k = j then s else 0) := by
      simp only [z]; ring
    rw [← e]
    linarith
  have hsumt := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [Finset.sum_sub_distrib] at hsumt
  simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hsumt
  unfold klDiv at h1
  rw [hzi, hzj] at hsumt
  have h5 : Real.log ((x j - s) / y j) ≤ Real.log ((x i + s) / y i) := by
    have : 0 ≤ s * (Real.log ((x i + s) / y i) - Real.log ((x j - s) / y j)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hspos).mp this
    linarith
  rw [Real.log_le_log_iff (div_pos (by linarith) hyj) (div_pos (by linarith [hxpos i]) hyi)] at h5
  rw [sub_div, add_div] at h5
  have h6 : s / y j + s / y i = s * (1 / y i + 1 / y j) := by ring
  have h7 : s * (1 / y i + 1 / y j) ≤ D / 2 := by
    have := mul_le_mul_of_nonneg_right hs2 hW.le
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hW.ne'] at this
    exact this
  have : D ≤ s / y j + s / y i := by rw [hD]; linarith
  linarith

theorem mem_trunc {N : ℕ} {ε η : ℝ} {β : Fin N → ℝ} {L h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) : ∀ t, (∑ k, h t k = 1) ∧ ∀ k, ε / N ≤ h t k := by
  intro t
  unfold IsAlg1Run at hrun
  cases t with
  | zero => exact hrun.1
  | succ t => exact (hrun.2 t).1

theorem gain_le {N : ℕ} (ε : ℝ) (β : Fin N → ℝ) (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N)
    (hN : (0 : ℝ) < N) : gain N ε β h L t i ≤ 1 + ε ^ 2 / (8 * N) := by
  have : 0 ≤ ε ^ 2 / (8 * N) := by positivity
  unfold gain
  split_ifs <;> linarith

theorem gain_nonneg {N : ℕ} (ε : ℝ) (β : Fin N → ℝ) (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N)
    (hN : (0 : ℝ) < N) : 0 ≤ gain N ε β h L t i := by
  have : 0 ≤ ε ^ 2 / (8 * N) := by positivity
  unfold gain
  split_ifs <;> linarith

theorem exists_gt {N : ℕ} (x hh : Fin N → ℝ) (hx : ∑ k, x k = 1) (hh1 : ∑ k, hh k = 1) (i : Fin N)
    (hi : x i < hh i) : ∃ j, hh j < x j := by
  by_contra hno
  push_neg at hno
  have : ∑ k, x k < ∑ k, hh k := Finset.sum_lt_sum (fun k _ => hno k) ⟨i, Finset.mem_univ _, hi⟩
  linarith

theorem queue_nonneg {N : ℕ} (h L : ℕ → Fin N → ℝ) : ∀ t i, 0 ≤ queue h L t i := by
  intro t i
  cases t with
  | zero => exact le_refl _
  | succ t => exact le_max_left _ _

theorem queue_succ {N : ℕ} (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) :
    queue h L (t + 1) i = queue h L t i + L t i - work h L t i := by
  show max 0 (L t i + queue h L t i - h t i) = _
  unfold work
  by_cases hc : h t i ≤ L t i + queue h L t i
  · rw [min_eq_left hc, max_eq_right (show (0 : ℝ) ≤ L t i + queue h L t i - h t i by linarith)]
    ring
  · push_neg at hc
    rw [min_eq_right hc.le, max_eq_left (show L t i + queue h L t i - h t i ≤ 0 by linarith)]
    ring

theorem cum_work {N : ℕ} (h L : ℕ → Fin N → ℝ) (i : Fin N) : ∀ k,
    ∑ t ∈ Finset.range k, work h L t i = ∑ t ∈ Finset.range k, L t i - queue h L k i := by
  intro k
  induction k with
  | zero =>
    show (∑ t ∈ Finset.range 0, work h L t i) = ∑ t ∈ Finset.range 0, L t i - 0
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, queue_succ]
    ring

theorem h_pos {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) {β : Fin N → ℝ}
    {L h : ℕ → Fin N → ℝ} (hrun : IsAlg1Run N ε η β L h) : ∀ t k, 0 < h t k := by
  intro t k
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact lt_of_lt_of_le (div_pos hε hNpos) ((mem_trunc hrun t).2 k)

theorem h_le_one {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) {β : Fin N → ℝ}
    {L h : ℕ → Fin N → ℝ} (hrun : IsAlg1Run N ε η β L h) (t : ℕ) (k : Fin N) : h t k ≤ 1 := by
  calc h t k ≤ ∑ j, h t j :=
        Finset.single_le_sum (fun j _ => (h_pos hN hε hrun t j).le) (Finset.mem_univ k)
    _ = 1 := (mem_trunc hrun t).1

theorem work_nonneg {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) {β : Fin N → ℝ}
    {L h : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) (hrun : IsAlg1Run N ε η β L h)
    (t : ℕ) (k : Fin N) : 0 ≤ work h L t k := by
  unfold work
  exact le_min (h_pos hN hε hrun t k).le (by linarith [hL t k, queue_nonneg h L t k])

theorem work_le {N : ℕ} (h L : ℕ → Fin N → ℝ) (t : ℕ) (k : Fin N) : work h L t k ≤ h t k :=
  min_le_left _ _

theorem theta_small {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3) :
    0 ≤ η * (ε ^ 2 / (8 * (N : ℝ))) ∧ η * (ε ^ 2 / (8 * (N : ℝ))) ≤ 1 / 100 := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ ε ^ 2 / (8 * (N : ℝ)) := by positivity
  have h1 : ε ^ 2 ≤ 1 / 100 := by nlinarith
  have h2 : ε ^ 2 / (8 * (N : ℝ)) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨mul_nonneg hη.le h0, ?_⟩
  have : η * (ε ^ 2 / (8 * (N : ℝ))) ≤ ε ^ 2 / (8 * (N : ℝ)) :=
    mul_le_of_le_one_left h0 (by linarith)
  linarith

/-- low-utilisation steps boost every busy user by `1 + 2c` -/
theorem boost_low {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (t : ℕ)
    (hS : ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L t j), h t j ≤ 1 - ε)
    (i : Fin N) (hq : 0 < queue h L t i) :
    h t i * (1 + ε * η / (2 * (N : ℝ))) ≤ h (t + 1) i := by
  obtain ⟨c, hc_def⟩ : ∃ c, c = ε * η / (2 * (N : ℝ)) := ⟨_, rfl⟩
  rw [← hc_def]
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  have hmem := mem_trunc hrun
  have hlow : ∀ t k, ε / N ≤ h t k := fun t k => (hmem t).2 k
  have hsum1 : ∀ t, ∑ k, h t k = 1 := fun t => (hmem t).1
  have hpos : ∀ t k, 0 < h t k := fun t k => lt_of_lt_of_le hfl (hlow t k)
  set a := ε ^ 2 / (8 * (N : ℝ)) with ha
  have ha0 : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by rw [hc_def]; positivity
  let E : ℕ → Fin N → ℝ := fun t k => Real.exp (η * gain N ε β h L t k)
  have hE : ∀ t k, 0 < E t k := fun t k => Real.exp_pos _
  have hEle : ∀ t k, E t k ≤ Real.exp (η * (1 + a)) := by
    intro t k
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (gain_le ε β h L t k hNpos) hη.le
  have hy : ∀ t k, 0 < h t k * E t k := fun t k => mul_pos (hpos t k) (hE t k)
  have hfoc : ∀ t i j, ε / N < h (t + 1) j →
      h (t + 1) j / (h t j * E t j) ≤ h (t + 1) i / (h t i * E t i) := by
    intro t i j hj
    have hrun' := hrun
    unfold IsAlg1Run at hrun'
    exact foc hfl (fun k => h t k * E t k) (h (t + 1)) (hy t) (hrun'.2 t) i j hj
  have hfoc' : ∀ t i j, ε / N < h (t + 1) j →
      h (t + 1) j * (h t i * E t i) ≤ h (t + 1) i * (h t j * E t j) := by
    intro t i j hj
    have := hfoc t i j hj
    rwa [div_le_div_iff₀ (hy t j) (hy t i)] at this
  by_contra hcon
  push_neg at hcon
  have hgi : gain N ε β h L t i ≥ 1 := by
    have : 0 ≤ ε ^ 2 / (8 * (N : ℝ)) := by positivity
    unfold gain; rw [if_pos hq]; split_ifs <;> linarith
  have hEi : Real.exp η ≤ E t i := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hgi hη.le
    linarith
  set κ := (1 + c) * Real.exp (-η) with hκ
  set K := (1 + c) * Real.exp (η * a) with hK
  have hexpη : Real.exp (-η) * Real.exp η = 1 := by rw [← Real.exp_add]; simp
  have hc1 : 0 ≤ 1 + c := by linarith
  have hri : h (t + 1) i < κ * (h t i * E t i) := by
    have h1 : (1 + c) * h t i ≤ κ * (h t i * E t i) := by
      calc (1 + c) * h t i = (1 + c) * h t i * (Real.exp (-η) * Real.exp η) := by
            rw [hexpη, mul_one]
        _ ≤ (1 + c) * h t i * (Real.exp (-η) * E t i) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEi (Real.exp_pos _).le)
              (mul_nonneg hc1 (hpos t i).le)
        _ = κ * (h t i * E t i) := by rw [hκ]; ring
    linarith
  have hκ0 : 0 ≤ κ := mul_nonneg hc1 (Real.exp_pos _).le
  have hall : ∀ j, h (t + 1) j ≤ ε / N ∨ h (t + 1) j ≤ κ * (h t j * E t j) := by
    intro j
    by_cases hj : ε / N < h (t + 1) j
    · right
      have h1 := hfoc' t i j hj
      have h2 : h (t + 1) i * (h t j * E t j) < κ * (h t i * E t i) * (h t j * E t j) :=
        mul_lt_mul_of_pos_right hri (hy t j)
      have h3 : h (t + 1) j * (h t i * E t i) < κ * (h t j * E t j) * (h t i * E t i) := by
        linarith
      exact le_of_lt (lt_of_mul_lt_mul_right h3 (hy t i).le)
    · left; push_neg at hj; exact hj
  have hκ1 : κ ≤ 1 := by
    rw [hκ]
    have h1 : 1 + c ≤ Real.exp η := by
      have := Real.add_one_le_exp η
      have : c ≤ η := by
        rw [hc_def, div_le_iff₀ (by linarith)]
        have : ε ≤ 2 * N := by linarith
        have := mul_le_mul_of_nonneg_left this hη.le
        linarith
      linarith
    have h2 : (1 + c) * Real.exp (-η) ≤ Real.exp η * Real.exp (-η) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    rw [← Real.exp_add] at h2
    simpa using h2
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 1 ≤ Real.exp (η * a) := Real.one_le_exp (by positivity)
    have := mul_le_mul (show (1 : ℝ) ≤ 1 + c by linarith) this zero_le_one hc1
    linarith
  have hbound : ∀ j, h (t + 1) j ≤
      (if 0 < queue h L t j then K * h t j else κ * h t j + (1 - κ) * (ε / N)) := by
    intro j
    split_ifs with hqj
    · rcases hall j with h1 | h1
      · have := mul_le_mul_of_nonneg_right hK1 (hpos t j).le
        have := hlow t j
        linarith
      · have hEle' : Real.exp (-η) * E t j ≤ Real.exp (η * a) := by
          calc Real.exp (-η) * E t j ≤ Real.exp (-η) * Real.exp (η * (1 + a)) :=
                mul_le_mul_of_nonneg_left (hEle t j) (Real.exp_pos _).le
            _ = Real.exp (η * a) := by rw [← Real.exp_add]; congr 1; ring
        have : κ * (h t j * E t j) ≤ K * h t j := by
          calc κ * (h t j * E t j) = (1 + c) * h t j * (Real.exp (-η) * E t j) := by
                rw [hκ]; ring
            _ ≤ (1 + c) * h t j * Real.exp (η * a) :=
                mul_le_mul_of_nonneg_left hEle' (mul_nonneg hc1 (hpos t j).le)
            _ = K * h t j := by rw [hK]; ring
        linarith
    · have hg0 : gain N ε β h L t j = 0 := by unfold gain; rw [if_neg hqj]
      have hEj : E t j = 1 := by
        show Real.exp (η * gain N ε β h L t j) = 1
        rw [hg0]; simp
      rcases hall j with h1 | h1
      · have := mul_nonneg hκ0 (sub_nonneg.mpr (hlow t j))
        linarith
      · rw [hEj, mul_one] at h1
        have : 0 ≤ (1 - κ) * (ε / N) := mul_nonneg (by linarith) hfl.le
        linarith
  have htot : (1 : ℝ) ≤
      ∑ j, (if 0 < queue h L t j then K * h t j else κ * h t j + (1 - κ) * (ε / N)) := by
    calc (1 : ℝ) = ∑ j, h (t + 1) j := (hsum1 (t + 1)).symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hbound j)
  rw [Finset.sum_ite] at htot
  set Bs := Finset.univ.filter (fun j => 0 < queue h L t j) with hBs
  set Is := Finset.univ.filter (fun j => ¬ 0 < queue h L t j) with hIs
  have hsplit : ∑ j ∈ Bs, h t j + ∑ j ∈ Is, h t j = 1 := by
    rw [hBs, hIs, Finset.sum_filter_add_sum_filter_not]; exact hsum1 t
  have hcard : Bs.card + Is.card = N := by
    rw [hBs, hIs, Finset.card_filter_add_card_filter_not]; simp
  have hiB : i ∈ Bs := by rw [hBs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hq⟩
  have hBcard : 1 ≤ Bs.card := Finset.card_pos.mpr ⟨i, hiB⟩
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at htot
  have hSB : ∑ j ∈ Bs, h t j ≤ 1 - ε := hS
  have hSB0 : 0 ≤ ∑ j ∈ Bs, h t j := Finset.sum_nonneg (fun j _ => (hpos t j).le)
  have hIcR : (Is.card : ℝ) = N - Bs.card := by
    have : (Is.card : ℝ) + Bs.card = N := by exact_mod_cast (by omega : Is.card + Bs.card = N)
    linarith
  have hBcR : (1 : ℝ) ≤ Bs.card := by exact_mod_cast hBcard
  have hineq : (1 - κ) * (ε / N) ≤ K - 1 := by
    have h1 : (1 - κ) * (∑ j ∈ Is, h t j - Is.card * (ε / N)) ≤ (K - 1) * ∑ j ∈ Bs, h t j := by
      linarith
    have h2 : ε / N ≤ ∑ j ∈ Is, h t j - Is.card * (ε / N) := by
      rw [hIcR]
      have : ε ≤ ∑ j ∈ Is, h t j := by linarith
      have hNe : (N : ℝ) * (ε / N) = ε := by field_simp
      rw [sub_mul, hNe]
      have := mul_le_mul_of_nonneg_right hBcR hfl.le
      linarith
    have h3 : (K - 1) * ∑ j ∈ Bs, h t j ≤ K - 1 := by
      have := mul_le_mul_of_nonneg_left (show ∑ j ∈ Bs, h t j ≤ 1 by linarith)
        (show (0 : ℝ) ≤ K - 1 by linarith)
      linarith
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - κ)
    linarith
  have hηa : η * a ≤ 1 := by
    have : a ≤ 1 := by
      rw [ha, div_le_one (by linarith)]
      have : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le (by linarith)
      linarith
    exact mul_le_one₀ (by linarith) ha0 this
  have hηa0 : 0 ≤ η * a := mul_nonneg hη.le ha0
  have hexp1 : Real.exp (η * a) ≤ 1 + 2 * (η * a) := by
    have := Real.abs_exp_sub_one_sub_id_le (x := η * a)
      (by rw [abs_le]; constructor <;> linarith)
    have h2 := (abs_le.mp this).2
    have : (η * a) ^ 2 ≤ η * a := by rw [sq]; exact mul_le_of_le_one_left hηa0 hηa
    linarith
  have hexp2 : Real.exp (-η) ≤ 1 - η + η ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -η) (by rw [abs_le]; constructor <;> linarith)
    have h2 := (abs_le.mp this).2
    rw [neg_sq] at h2
    linarith
  have hfin : K - 1 < (1 - κ) * (ε / N) := by
    set u := ε / N with hu
    have hu0 : 0 < u := hfl
    have hu1 : u ≤ 1 / 20 := by
      rw [hu, div_le_iff₀ hNpos]; linarith
    have hc_eq : c = η * u / 2 := by rw [hc_def, hu]; ring
    have ha_eq : a = ε * u / 8 := by rw [ha, hu]; ring
    have hK' : K ≤ (1 + c) * (1 + 2 * (η * a)) := by
      rw [hK]; exact mul_le_mul_of_nonneg_left hexp1 hc1
    have hκ' : κ ≤ (1 + c) * (1 - η + η ^ 2) := by
      rw [hκ]; exact mul_le_mul_of_nonneg_left hexp2 hc1
    have e1 : η ^ 2 ≤ 1 / 9 := by
      have := mul_le_mul hη' hη' hη.le (by norm_num)
      rw [sq]; linarith
    have q1 : η ^ 2 * u ≤ 1 / 180 := by
      have := mul_le_mul e1 hu1 hu0.le (by norm_num)
      linarith
    have e2 : η * ε ≤ 1 / 30 := by
      have := mul_le_mul hη' hε' hε.le (by norm_num)
      linarith
    have q2 : η * ε * u ≤ 1 / 600 := by
      have := mul_le_mul e2 hu1 hu0.le (by norm_num)
      linarith
    have q3 : 0 ≤ η * u := mul_nonneg hη.le hu0.le
    have P : 0 < 1 / 2 - η - u / 2 + η * u / 2 - η ^ 2 * u / 2 - ε / 4 - η * ε * u / 8 := by
      linarith
    have key : (1 - (1 + c) * (1 - η + η ^ 2)) * u - (c + 2 * (η * a) + 2 * c * (η * a)) =
        η * u * (1 / 2 - η - u / 2 + η * u / 2 - η ^ 2 * u / 2 - ε / 4 - η * ε * u / 8) := by
      rw [hc_eq, ha_eq]; ring
    have hpos' : 0 < η * u * (1 / 2 - η - u / 2 + η * u / 2 - η ^ 2 * u / 2 - ε / 4 -
        η * ε * u / 8) := mul_pos (mul_pos hη hu0) P
    have h1 : (1 - (1 + c) * (1 - η + η ^ 2)) * u ≤ (1 - κ) * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu0.le
    have h2 : K - 1 ≤ c + 2 * (η * a) + 2 * c * (η * a) := by
      have : (1 + c) * (1 + 2 * (η * a)) = 1 + c + 2 * (η * a) + 2 * c * (η * a) := by ring
      linarith
    linarith
  linarith

/-- a busy user never loses more than a factor `1 - η λ` in one step -/
theorem boost_active {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (t : ℕ) (i : Fin N) (hq : 0 < queue h L t i) :
    h t i * (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) ≤ h (t + 1) i := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  have hmem := mem_trunc hrun
  have hlow : ∀ t k, ε / N ≤ h t k := fun t k => (hmem t).2 k
  have hsum1 : ∀ t, ∑ k, h t k = 1 := fun t => (hmem t).1
  have hpos : ∀ t k, 0 < h t k := fun t k => lt_of_lt_of_le hfl (hlow t k)
  set a := ε ^ 2 / (8 * (N : ℝ)) with ha
  have ha0 : 0 ≤ a := by positivity
  let E : ℕ → Fin N → ℝ := fun t k => Real.exp (η * gain N ε β h L t k)
  have hE : ∀ t k, 0 < E t k := fun t k => Real.exp_pos _
  have hEle : ∀ t k, E t k ≤ Real.exp (η * (1 + a)) := by
    intro t k
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (gain_le ε β h L t k hNpos) hη.le
  have hy : ∀ t k, 0 < h t k * E t k := fun t k => mul_pos (hpos t k) (hE t k)
  have hfoc : ∀ t i j, ε / N < h (t + 1) j →
      h (t + 1) j / (h t j * E t j) ≤ h (t + 1) i / (h t i * E t i) := by
    intro t i j hj
    have hrun' := hrun
    unfold IsAlg1Run at hrun'
    exact foc hfl (fun k => h t k * E t k) (h (t + 1)) (hy t) (hrun'.2 t) i j hj
  have hfoc' : ∀ t i j, ε / N < h (t + 1) j →
      h (t + 1) j * (h t i * E t i) ≤ h (t + 1) i * (h t j * E t j) := by
    intro t i j hj
    have := hfoc t i j hj
    rwa [div_le_div_iff₀ (hy t j) (hy t i)] at this
  have hηa0 : 0 ≤ η * a := mul_nonneg hη.le ha0
  have hshrink : h t i * (1 - η * a) ≤ h t i :=
    mul_le_of_le_one_right (hpos t i).le (by linarith)
  by_cases hlt : h t i < β i
  · have hle : h t i ≤ h (t + 1) i := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨j, hj⟩ := exists_gt (h (t + 1)) (h t) (hsum1 (t + 1)) (hsum1 t) i hcon
      have hjf : ε / N < h (t + 1) j := lt_of_le_of_lt (hlow t j) hj
      have h1 := hfoc' t i j hjf
      have hgi : gain N ε β h L t i = 1 + ε ^ 2 / (8 * (N : ℝ)) := by
        unfold gain; rw [if_pos hq, if_pos hlt]
      have hEij : E t j ≤ E t i := by
        show Real.exp (η * gain N ε β h L t j) ≤ Real.exp (η * gain N ε β h L t i)
        rw [hgi]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (gain_le ε β h L t j hNpos) hη.le)
      have hp := hpos t i
      have hpj := hpos t j
      have hEj := hE t j
      have hEi := hE t i
      have h2 : h (t + 1) i * (h t j * E t j) ≤ h (t + 1) i * (h t j * E t i) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (lt_of_lt_of_le hfl (hlow (t + 1) i)))
        exact mul_le_mul_of_nonneg_left hEij hpj.le
      have h3 : h t j * (h t i * E t i) < h (t + 1) j * (h t i * E t i) :=
        mul_lt_mul_of_pos_right hj (mul_pos hp hEi)
      have h4 : h t i * (h t j * E t i) < h (t + 1) i * (h t j * E t i) := by linarith
      have h5 := lt_of_mul_lt_mul_right h4 (mul_pos hpj hEi).le
      linarith
    linarith
  · push_neg at hlt
    have hge : β i ≤ h t i := hlt
    by_contra hcon
    push_neg at hcon
    have hlt2 : h (t + 1) i < h t i := by linarith
    obtain ⟨j, hj⟩ := exists_gt (h (t + 1)) (h t) (hsum1 (t + 1)) (hsum1 t) i hlt2
    have hjf : ε / N < h (t + 1) j := lt_of_le_of_lt (hlow t j) hj
    have h1 := hfoc' t i j hjf
    have hgi : gain N ε β h L t i = 1 := by
      unfold gain; rw [if_pos hq, if_neg (not_lt.mpr hge)]
    have hEi : E t i = Real.exp η := by
      show Real.exp (η * gain N ε β h L t i) = _; rw [hgi, mul_one]
    have hEj : E t j ≤ Real.exp η * Real.exp (η * a) := by
      rw [← Real.exp_add]
      have := hEle t j
      rwa [show η * (1 + a) = η + η * a by ring] at this
    have hp := hpos t i
    have hpj := hpos t j
    have hxi : 0 < h (t + 1) i := lt_of_lt_of_le hfl (hlow (t + 1) i)
    have h3 : h t j * (h t i * E t i) < h (t + 1) j * (h t i * E t i) :=
      mul_lt_mul_of_pos_right hj (mul_pos hp (by rw [hEi]; exact Real.exp_pos _))
    have h4 : h (t + 1) i * (h t j * E t j) ≤
        h (t + 1) i * (h t j * (Real.exp η * Real.exp (η * a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEj hpj.le) hxi.le
    rw [hEi] at h3 h1
    have h5 : h t i < h (t + 1) i * Real.exp (η * a) := by
      have h6 : h t j * Real.exp η * h t i <
          h t j * Real.exp η * (h (t + 1) i * Real.exp (η * a)) := by
        linarith
      exact lt_of_mul_lt_mul_left h6 (mul_pos hpj (Real.exp_pos η)).le
    have h7 : 1 - η * a ≤ Real.exp (-(η * a)) := by linarith [Real.add_one_le_exp (-(η * a))]
    have h8 : h t i * Real.exp (-(η * a)) < h (t + 1) i := by
      have := mul_lt_mul_of_pos_right h5 (Real.exp_pos (-(η * a)))
      have e : h (t + 1) i * Real.exp (η * a) * Real.exp (-(η * a)) = h (t + 1) i := by
        rw [mul_assoc, ← Real.exp_add]; simp
      linarith
    have h9 : h t i * (1 - η * a) ≤ h t i * Real.exp (-(η * a)) :=
      mul_le_mul_of_nonneg_left h7 hp.le
    linarith

set_option maxHeartbeats 1600000 in
/-- Lemma 2 under the hypothesis `β ≥ e^{η(1+λ)} ε / N` -/
theorem sla_boost {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N ≤ β j)
    (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (t : ℕ) (i : Fin N) (hq : 0 < queue h L t i)
    (hlt : h t i < β i) :
    h t i * (1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ))) ≤ h (t + 1) i := by
  obtain ⟨lam, hlam_eq⟩ : ∃ lam, lam = ε ^ 2 / (8 * (N : ℝ)) := ⟨_, rfl⟩
  obtain ⟨c', hc'_def⟩ : ∃ c', c' = ε * η * lam / (2 * (N : ℝ)) := ⟨_, rfl⟩
  rw [← hlam_eq, ← hc'_def]
  rw [← hlam_eq] at hβ
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  have hmem := mem_trunc hrun
  have hlow : ∀ t k, ε / N ≤ h t k := fun t k => (hmem t).2 k
  have hsum1 : ∀ t, ∑ k, h t k = 1 := fun t => (hmem t).1
  have hpos : ∀ t k, 0 < h t k := fun t k => lt_of_lt_of_le hfl (hlow t k)
  have hlampos : 0 < lam := by rw [hlam_eq]; exact div_pos (pow_pos hε 2) (by linarith)
  have hlam0 : 0 ≤ lam := hlampos.le
  have hc0 : 0 ≤ c' := by
    rw [hc'_def]
    exact div_nonneg (mul_nonneg (mul_nonneg hε.le hη.le) hlam0) (by linarith)
  obtain ⟨ρ0, hρ0def⟩ : ∃ ρ0, ρ0 = Real.exp (η * (1 + lam)) := ⟨_, rfl⟩
  rw [← hρ0def] at hβ
  have hβ' : ∀ j, ρ0 * (ε / N) ≤ β j := by
    intro j; have := hβ j; rw [mul_div_assoc] at this; exact this
  set u := ε / N with hu
  have hu1 : u ≤ 1 / 20 := by rw [hu, div_le_iff₀ hNpos]; linarith
  let E : Fin N → ℝ := fun k => Real.exp (η * gain N ε β h L t k)
  have hE : ∀ k, 0 < E k := fun k => Real.exp_pos _
  have hy : ∀ k, 0 < h t k * E k := fun k => mul_pos (hpos t k) (hE k)
  have hfoc' : ∀ i j, u < h (t + 1) j →
      h (t + 1) j * (h t i * E i) ≤ h (t + 1) i * (h t j * E j) := by
    intro i j hj
    have hrun' := hrun
    unfold IsAlg1Run at hrun'
    have := foc hfl (fun k => h t k * E k) (h (t + 1)) hy (hrun'.2 t) i j hj
    rwa [div_le_div_iff₀ (hy j) (hy i)] at this
  have hgtop : ∀ j, 0 < queue h L t j → h t j < β j → gain N ε β h L t j = 1 + lam := by
    intro j h1 h2
    have e : gain N ε β h L t j = 1 + ε ^ 2 / (8 * (N : ℝ)) := by
      unfold gain; rw [if_pos h1, if_pos h2]
    rw [e, hlam_eq]
  have hgone : ∀ j, 0 < queue h L t j → ¬ h t j < β j → gain N ε β h L t j = 1 := by
    intro j h1 h2
    unfold gain; rw [if_pos h1, if_neg h2]
  have hgzero : ∀ j, ¬ 0 < queue h L t j → gain N ε β h L t j = 0 := by
    intro j h1
    unfold gain; rw [if_neg h1]
  by_contra hcon
  push_neg at hcon
  set κ := (1 + c') * Real.exp (-(η * (1 + lam))) with hκ
  set μ := (1 + c') * Real.exp (-(η * lam)) with hμ
  have hc1 : 0 ≤ 1 + c' := by linarith
  have hinv : ∀ x : ℝ, Real.exp (-x) * Real.exp x = 1 := by
    intro x; rw [← Real.exp_add]; simp
  have hEtop : ∀ j, 0 < queue h L t j → h t j < β j → E j = Real.exp (η * (1 + lam)) := by
    intro j h1 h2
    show Real.exp (η * gain N ε β h L t j) = _
    rw [hgtop j h1 h2]
  have hκtop : ∀ j, 0 < queue h L t j → h t j < β j → κ * (h t j * E j) = (1 + c') * h t j := by
    intro j h1 h2
    rw [hκ, hEtop j h1 h2]
    calc (1 + c') * Real.exp (-(η * (1 + lam))) * (h t j * Real.exp (η * (1 + lam)))
        = (1 + c') * h t j * (Real.exp (-(η * (1 + lam))) * Real.exp (η * (1 + lam))) := by ring
      _ = (1 + c') * h t j := by rw [hinv, mul_one]
  have hri : h (t + 1) i < κ * (h t i * E i) := by
    rw [hκtop i hq hlt]; linarith
  have hκ0 : 0 ≤ κ := mul_nonneg hc1 (Real.exp_pos _).le
  have hall : ∀ j, h (t + 1) j ≤ u ∨ h (t + 1) j ≤ κ * (h t j * E j) := by
    intro j
    by_cases hj : u < h (t + 1) j
    · right
      have h1 := hfoc' i j hj
      have h2 : h (t + 1) i * (h t j * E j) < κ * (h t i * E i) * (h t j * E j) :=
        mul_lt_mul_of_pos_right hri (hy j)
      have h3 : h (t + 1) j * (h t i * E i) < κ * (h t j * E j) * (h t i * E i) := by linarith
      exact le_of_lt (lt_of_mul_lt_mul_right h3 (hy i).le)
    · left; push_neg at hj; exact hj
  -- numeric facts
  have hηl : η * lam ≤ 1 / 100 := by
    have h1 : ε ^ 2 ≤ 1 / 100 := by
      have := mul_le_mul hε' hε' hε.le (by norm_num); rw [sq]; linarith
    have h2 : lam ≤ 1 / 1600 := by
      rw [hlam_eq, div_le_iff₀ (by linarith)]; linarith
    have := mul_le_mul hη' h2 hlam0 (by norm_num)
    linarith
  have hηl0 : 0 < η * lam := mul_pos hη hlampos
  have hc_eq : c' = η * lam * u / 2 := by
    rw [hc'_def, hu]; ring
  have hcη : c' ≤ η := by
    rw [hc_eq]
    have : lam * u ≤ 1 := by
      have : lam ≤ 1 := by
        rw [hlam_eq, div_le_iff₀ (by linarith)]
        have : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le (by linarith)
        linarith
      exact mul_le_one₀ this hfl.le (by linarith)
    have := mul_le_mul_of_nonneg_left this hη.le
    linarith
  have hκ1 : κ ≤ 1 := by
    rw [hκ]
    have h1 : 1 + c' ≤ Real.exp (η * (1 + lam)) := by
      have := Real.add_one_le_exp (η * (1 + lam))
      have : η ≤ η * (1 + lam) := by linarith [hηl0.le]
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(η * (1 + lam)))).le
    rw [mul_comm (Real.exp (η * (1 + lam))), hinv] at h2
    exact h2
  have hκμ : κ ≤ μ := by
    rw [hκ, hμ]
    apply mul_le_mul_of_nonneg_left _ hc1
    apply Real.exp_le_exp.mpr
    linarith
  have hexp2 : Real.exp (-(η * lam)) ≤ 1 - η * lam + (η * lam) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -(η * lam))
      (by rw [abs_le]; constructor <;> linarith)
    have h2 := (abs_le.mp this).2
    rw [neg_sq] at h2
    linarith
  have hfin : c' < (1 - μ) * u := by
    have h1 : (1 + c') * Real.exp (-(η * lam)) ≤ (1 + c') * (1 - η * lam + (η * lam) ^ 2) :=
      mul_le_mul_of_nonneg_left hexp2 hc1
    have h2 : (1 - (1 + c') * (1 - η * lam + (η * lam) ^ 2)) * u ≤ (1 - μ) * u :=
      mul_le_mul_of_nonneg_right (by rw [hμ]; linarith) hfl.le
    have key : (1 - (1 + c') * (1 - η * lam + (η * lam) ^ 2)) * u - c' =
        η * lam * u * (1 / 2 - η * lam - u / 2 + η * lam * u / 2 - (η * lam) ^ 2 * u / 2) := by
      rw [hc_eq]; ring
    have hq2 : (η * lam) ^ 2 * u ≤ 1 / 10000 := by
      have : (η * lam) ^ 2 ≤ 1 / 10000 := by
        rw [sq]; have := mul_le_mul hηl hηl hηl0.le (by norm_num); linarith
      have := mul_le_mul this hu1 hfl.le (by norm_num)
      linarith
    have hxu : 0 ≤ η * lam * u := mul_nonneg hηl0.le hfl.le
    have hP : 0 < 1 / 2 - η * lam - u / 2 + η * lam * u / 2 - (η * lam) ^ 2 * u / 2 := by
      linarith
    have hpos' := mul_pos (mul_pos hηl0 hfl) hP
    linarith
  have hμ1 : 0 ≤ 1 - μ := by
    by_contra hneg
    push_neg at hneg
    have : (1 - μ) * u < 0 := mul_neg_of_neg_of_pos hneg hfl
    linarith
  have hρ1 : 1 + η * (1 + lam) ≤ ρ0 := by
    rw [hρ0def]; linarith [Real.add_one_le_exp (η * (1 + lam))]
  have hρ0ge : 1 ≤ ρ0 := by
    have := mul_nonneg hη.le (by linarith : (0 : ℝ) ≤ 1 + lam)
    linarith
  have hμρ : 1 ≤ μ * ρ0 := by
    rw [hμ, hρ0def]
    have e : (1 + c') * Real.exp (-(η * lam)) * Real.exp (η * (1 + lam)) =
        (1 + c') * Real.exp η := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e]
    have h1 := Real.one_le_exp hη.le
    have := mul_le_mul (show (1 : ℝ) ≤ 1 + c' by linarith) h1 zero_le_one (by linarith)
    linarith
  -- per-coordinate bounds
  have hbound : ∀ j, h (t + 1) j ≤ (if 0 < queue h L t j then
      (if h t j < β j then (1 + c') * h t j else μ * h t j) else max u (κ * h t j)) := by
    intro j
    split_ifs with hqj hbj
    · rcases hall j with h1 | h1
      · have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + c' by linarith) (hpos t j).le
        have := hlow t j
        linarith
      · rw [hκtop j hqj hbj] at h1; exact h1
    · have hbj' : β j ≤ h t j := not_lt.mp hbj
      have hEj : E j = Real.exp η := by
        show Real.exp (η * gain N ε β h L t j) = _
        rw [hgone j hqj hbj, mul_one]
      rcases hall j with h1 | h1
      · have hμ0 : 0 ≤ μ := by linarith
        have h2 : u ≤ μ * h t j := by
          have h3 : ρ0 * u ≤ h t j := le_trans (hβ' j) hbj'
          have h4 := mul_le_mul_of_nonneg_left h3 hμ0
          have h5 := mul_le_mul_of_nonneg_right hμρ hfl.le
          linarith
        linarith
      · have : κ * (h t j * E j) = μ * h t j := by
          rw [hκ, hμ, hEj]
          have e : Real.exp (-(η * (1 + lam))) * Real.exp η = Real.exp (-(η * lam)) := by
            rw [← Real.exp_add]; congr 1; ring
          calc (1 + c') * Real.exp (-(η * (1 + lam))) * (h t j * Real.exp η)
              = (1 + c') * (Real.exp (-(η * (1 + lam))) * Real.exp η) * h t j := by ring
            _ = (1 + c') * Real.exp (-(η * lam)) * h t j := by rw [e]
        linarith
    · have hEj : E j = 1 := by
        show Real.exp (η * gain N ε β h L t j) = 1
        rw [hgzero j hqj]; simp
      rcases hall j with h1 | h1
      · exact le_trans h1 (le_max_left _ _)
      · rw [hEj, mul_one] at h1
        exact le_trans h1 (le_max_right _ _)
  -- summation
  have htot : (1 : ℝ) ≤ ∑ j, (if 0 < queue h L t j then
      (if h t j < β j then (1 + c') * h t j else μ * h t j) else max u (κ * h t j)) := by
    calc (1 : ℝ) = ∑ j, h (t + 1) j := (hsum1 (t + 1)).symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hbound j)
  rw [Finset.sum_ite, Finset.sum_ite] at htot
  set Bs := Finset.univ.filter (fun j => 0 < queue h L t j) with hBs
  set Is := Finset.univ.filter (fun j => ¬ 0 < queue h L t j) with hIs
  set G1 := Bs.filter (fun j => h t j < β j) with hG1
  set G2 := Bs.filter (fun j => ¬ h t j < β j) with hG2
  have e1 : ∑ j ∈ G1, (1 + c') * h t j = (1 + c') * ∑ j ∈ G1, h t j := by rw [Finset.mul_sum]
  have e2 : ∑ j ∈ G2, μ * h t j = μ * ∑ j ∈ G2, h t j := by rw [Finset.mul_sum]
  rw [e1, e2] at htot
  have hsplit : ∀ f : Fin N → ℝ, ∑ j, f j = ∑ j ∈ G1, f j + ∑ j ∈ G2, f j + ∑ j ∈ Is, f j := by
    intro f
    rw [hG1, hG2, Finset.sum_filter_add_sum_filter_not, hBs, hIs,
      Finset.sum_filter_add_sum_filter_not]
  have hS := hsplit (h t)
  rw [hsum1 t] at hS
  have hBsum := hsplit β
  have hiG1 : i ∈ G1 := by
    rw [hG1, Finset.mem_filter, hBs, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, hq⟩, hlt⟩
  have hS1lt : ∑ j ∈ G1, h t j < ∑ j ∈ G1, β j := by
    apply Finset.sum_lt_sum_of_nonempty ⟨i, hiG1⟩
    intro j hj
    rw [hG1, Finset.mem_filter] at hj
    exact hj.2
  have hIβ : (Is.card : ℝ) * (ρ0 * u) ≤ ∑ j ∈ Is, β j := by
    have := Finset.card_nsmul_le_sum Is β (ρ0 * u) (fun j _ => hβ' j)
    rwa [nsmul_eq_mul] at this
  have hS1le : ∑ j ∈ G1, h t j ≤ 1 := by
    have : 0 ≤ ∑ j ∈ G2, h t j := Finset.sum_nonneg (fun j _ => (hpos t j).le)
    have : 0 ≤ ∑ j ∈ Is, h t j := Finset.sum_nonneg (fun j _ => (hpos t j).le)
    linarith
  have hFdef : ∑ j ∈ Is, (h t j - max u (κ * h t j)) =
      ∑ j ∈ Is, h t j - ∑ j ∈ Is, max u (κ * h t j) := Finset.sum_sub_distrib _ _
  have hterm0 : ∀ j, 0 ≤ h t j - max u (κ * h t j) := by
    intro j
    have h1 := hlow t j
    have h2 : κ * h t j ≤ h t j := mul_le_of_le_one_left (hpos t j).le hκ1
    have := max_le h1 h2
    linarith
  have hkey : ∑ j ∈ Is, (h t j - max u (κ * h t j)) + (1 - μ) * ∑ j ∈ G2, h t j ≤
      c' * ∑ j ∈ G1, h t j := by
    rw [hFdef]; linarith
  have hh5 : c' * ∑ j ∈ G1, h t j ≤ c' := by
    have := mul_le_mul_of_nonneg_left hS1le hc0
    linarith
  have hF0 : 0 ≤ ∑ j ∈ Is, (h t j - max u (κ * h t j)) :=
    Finset.sum_nonneg (fun j _ => hterm0 j)
  by_cases hG2e : G2.Nonempty
  · obtain ⟨j0, hj0⟩ := hG2e
    have hj0' : β j0 ≤ h t j0 := by
      have := hj0
      rw [hG2, Finset.mem_filter] at this
      exact not_lt.mp this.2
    have hA : h t j0 ≤ ∑ j ∈ G2, h t j := Finset.single_le_sum (fun j _ => (hpos t j).le) hj0
    have hAu : u ≤ ∑ j ∈ G2, h t j := by
      have h1 := hβ' j0
      have h2 : u ≤ ρ0 * u := by
        have := mul_le_mul_of_nonneg_right hρ0ge hfl.le
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left hAu hμ1
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hG2e
    have hA0 : ∑ j ∈ G2, h t j = 0 := by rw [hG2e, Finset.sum_empty]
    have hβG2 : ∑ j ∈ G2, β j = 0 := by rw [hG2e, Finset.sum_empty]
    rw [hA0, mul_zero, add_zero] at hkey
    have hBβ : ∑ j ∈ Is, β j < ∑ j ∈ Is, h t j := by linarith
    have hIne : Is.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty, Finset.sum_empty] at hBβ
      exact lt_irrefl 0 hBβ
    have hIc : (1 : ℝ) ≤ Is.card := by exact_mod_cast Finset.card_pos.mpr hIne
    have hc'u : c' < (ρ0 - 1) * u := by
      rw [hc_eq]
      have h1 : η * (1 + lam) * u ≤ (ρ0 - 1) * u := mul_le_mul_of_nonneg_right (by linarith) hfl.le
      have h2 := mul_pos hη hfl
      have h3 : 0 ≤ η * lam * u := mul_nonneg hηl0.le hfl.le
      linarith
    by_cases hbig : ∃ j ∈ Is, u ≤ κ * h t j
    · obtain ⟨j1, hj1, hu1'⟩ := hbig
      have hterm : (1 - κ) * u ≤ h t j1 - max u (κ * h t j1) := by
        rw [max_eq_right hu1']
        have h1 : u ≤ h t j1 := hlow t j1
        have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 - κ by linarith)
        linarith
      have hsl := Finset.single_le_sum (fun j _ => hterm0 j) hj1
      have : (1 - μ) * u ≤ (1 - κ) * u := mul_le_mul_of_nonneg_right (by linarith) hfl.le
      linarith
    · push_neg at hbig
      have hF : ∑ j ∈ Is, (h t j - max u (κ * h t j)) = ∑ j ∈ Is, h t j - Is.card * u := by
        rw [Finset.sum_congr rfl (fun j hj => show h t j - max u (κ * h t j) = h t j - u by
          rw [max_eq_left (hbig j hj).le]), Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul]
      have hρu : 0 ≤ (ρ0 - 1) * u := mul_nonneg (by linarith) hfl.le
      have h1 : (ρ0 - 1) * u ≤ (Is.card : ℝ) * ((ρ0 - 1) * u) := by
        have := mul_le_mul_of_nonneg_right hIc hρu
        linarith
      linarith

theorem work_eq_of_next_pos {N : ℕ} (g L : ℕ → Fin N → ℝ) (τ : ℕ) (i : Fin N)
    (hq : 0 < queue g L (τ + 1) i) : work g L τ i = g τ i := by
  have hq' : 0 < max 0 (L τ i + queue g L τ i - g τ i) := hq
  have : g τ i ≤ L τ i + queue g L τ i := by
    by_contra hc
    push_neg at hc
    rw [max_eq_left (show L τ i + queue g L τ i - g τ i ≤ 0 by linarith)] at hq'
    exact lt_irrefl 0 hq'
  exact min_eq_left this

theorem queue_Ico {N : ℕ} (g L : ℕ → Fin N → ℝ) (i : Fin N) (s u : ℕ) (hsu : s ≤ u) :
    queue g L u i = queue g L s i + ∑ τ ∈ Finset.Ico s u, L τ i -
      ∑ τ ∈ Finset.Ico s u, work g L τ i := by
  have h1 := cum_work g L i u
  have h2 := cum_work g L i s
  rw [← Finset.sum_range_add_sum_Ico _ hsu, ← Finset.sum_range_add_sum_Ico _ hsu] at h1
  linarith

theorem lindley {N : ℕ} (g L : ℕ → Fin N → ℝ) (i : Fin N) (a : ℝ) (hg : ∀ τ, g τ i = a)
    (s : ℕ) : ∀ k : ℕ,
    queue g L s i + ∑ τ ∈ Finset.Ico s (s + k), L τ i - a * k ≤ queue g L (s + k) i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : queue g L (s + k) i + L (s + k) i - a ≤ queue g L (s + k + 1) i := by
      show _ ≤ max 0 (L (s + k) i + queue g L (s + k) i - g (s + k) i)
      rw [hg]
      have := le_max_right 0 (L (s + k) i + queue g L (s + k) i - a)
      linarith
    rw [show s + (k + 1) = s + k + 1 by omega, Finset.sum_Ico_succ_top (by omega : s ≤ s + k)]
    push_cast
    linarith

theorem last_zero {N : ℕ} (g L : ℕ → Fin N → ℝ) (i : Fin N) (u : ℕ)
    (hu : 0 < queue g L u i) :
    ∃ s, s < u ∧ queue g L s i = 0 ∧ ∀ τ, s < τ → τ ≤ u → 0 < queue g L τ i := by
  have h0 : queue g L 0 i = 0 := rfl
  have hspec : queue g L (Nat.findGreatest (fun τ => queue g L τ i = 0) u) i = 0 :=
    Nat.findGreatest_spec (P := fun τ => queue g L τ i = 0) (Nat.zero_le u) h0
  refine ⟨Nat.findGreatest (fun τ => queue g L τ i = 0) u, ?_, hspec, ?_⟩
  · have hle := Nat.findGreatest_le (P := fun τ => queue g L τ i = 0) u
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [h] at hspec
      linarith
  · intro τ h1 h2
    have hne : ¬ queue g L τ i = 0 :=
      Nat.findGreatest_is_greatest (P := fun τ => queue g L τ i = 0) h1 h2
    exact lt_of_le_of_ne (queue_nonneg g L τ i) (Ne.symm hne)

set_option maxHeartbeats 1600000 in
theorem climb {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N ≤ β j)
    (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (i : Fin N) (s : ℕ) :
    ∀ m : ℕ, (∀ τ, s ≤ τ → τ < s + m → 0 < queue h L τ i) →
      min ((1 - η * (ε ^ 2 / (8 * (N : ℝ)))) * β i)
        (ε / N * (1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ))) ^ m) ≤ h (s + m) i := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hθ0, hθ1⟩ := theta_small hN hε hε' hη hη'
  have hβ0 : 0 ≤ β i := by
    have h1 := hβ i
    have : 0 < Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N := by positivity
    linarith
  have hρ0 : 0 ≤ ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)) := by positivity
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = 1 - η * (ε ^ 2 / (8 * (N : ℝ))) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)) := ⟨_, rfl⟩
  rw [← hθ, ← hρ]
  have hθpos : 0 ≤ θ := by rw [hθ]; linarith
  have hθle : θ ≤ 1 := by rw [hθ]; linarith
  have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith
  have hMβ : θ * β i ≤ β i := mul_le_of_le_one_left hβ0 hθle
  intro m
  induction m with
  | zero =>
    intro _
    simp only [pow_zero, mul_one, add_zero]
    exact le_trans (min_le_right _ _) ((mem_trunc hrun s).2 i)
  | succ m ih =>
    intro hb
    have ih' := ih (fun τ h1 h2 => hb τ h1 (by omega))
    have hq : 0 < queue h L (s + m) i := hb (s + m) (by omega) (by omega)
    have hp := h_pos hN hε hrun (s + m) i
    rw [show s + (m + 1) = s + m + 1 by omega]
    by_cases hge : θ * β i ≤ h (s + m) i
    · have hM : θ * β i ≤ h (s + m + 1) i := by
        by_cases hlt : h (s + m) i < β i
        · have hsb := sla_boost hN hε hε' hη hη' hβ hβsum hrun (s + m) i hq hlt
          rw [← hρ] at hsb
          have := le_mul_of_one_le_right hp.le hρ1
          linarith
        · push_neg at hlt
          have hba := boost_active hN hε hε' hη hη' hrun (s + m) i hq
          rw [← hθ] at hba
          have := mul_le_mul_of_nonneg_left hlt hθpos
          linarith
      exact le_trans (min_le_left _ _) hM
    · push_neg at hge
      have hlt : h (s + m) i < β i := lt_of_lt_of_le hge hMβ
      have hsb := sla_boost hN hε hε' hη hη' hβ hβsum hrun (s + m) i hq hlt
      rw [← hρ] at hsb
      have hX : ε / N * ρ ^ m ≤ h (s + m) i := by
        by_contra hX
        push_neg at hX
        have := lt_min hge hX
        linarith
      have hstep : ε / N * ρ ^ (m + 1) ≤ h (s + m + 1) i := by
        rw [pow_succ, ← mul_assoc]
        have := mul_le_mul_of_nonneg_right hX (by linarith : (0 : ℝ) ≤ ρ)
        linarith
      exact le_trans (min_le_right _ _) hstep

set_option maxHeartbeats 1600000 in
theorem KL {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N ≤ β j)
    (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (i : Fin N) (P0 : ℕ)
    (hP0 : 1 ≤ ε / N * (1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ))) ^ P0)
    (s u : ℕ) (hb : ∀ τ, s < τ → τ ≤ u → 0 < queue h L τ i) :
    (1 - 2 * ε) * β i * ((u : ℝ) - s) - (1 - 2 * ε) * β i * ((P0 : ℝ) + 1) ≤
      ∑ τ ∈ Finset.Ico s u, work h L τ i := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  obtain ⟨hθ0, hθ1⟩ := theta_small hN hε hε' hη hη'
  have hβ0 : ∀ j, 0 ≤ β j := by
    intro j
    have h1 := hβ j
    have : 0 < Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N := by positivity
    linarith
  have hβ1 : β i ≤ 1 :=
    le_trans (Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ i)) hβsum
  have hρ1 : 1 ≤ 1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)) := by
    have : 0 ≤ ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)) := by positivity
    linarith
  have hθε : η * (ε ^ 2 / (8 * (N : ℝ))) ≤ 2 * ε := by
    have hx0 : 0 ≤ ε ^ 2 / (8 * (N : ℝ)) := by positivity
    have h1 : ε ^ 2 / (8 * (N : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left (show ε ≤ 8 * (N : ℝ) by linarith) hε.le
      linarith
    have h2 := mul_le_mul_of_nonneg_right (show η ≤ 1 by linarith) hx0
    linarith
  have haM : (1 - 2 * ε) * β i ≤ (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) * β i :=
    mul_le_mul_of_nonneg_right (by linarith) (hβ0 i)
  have hM1 : (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) * β i ≤ 1 := by
    have := mul_le_mul_of_nonneg_right
      (show 1 - η * (ε ^ 2 / (8 * (N : ℝ))) ≤ 1 by linarith) (hβ0 i)
    linarith
  have ha0 : 0 ≤ (1 - 2 * ε) * β i := mul_nonneg (by linarith) (hβ0 i)
  have hw0 : ∀ τ, 0 ≤ work h L τ i := fun τ => work_nonneg hN hε hL hrun τ i
  by_cases hsu : s + 1 + P0 ≤ u
  · have hsub : ∑ τ ∈ Finset.Ico (s + 1 + P0) u, work h L τ i ≤
        ∑ τ ∈ Finset.Ico s u, work h L τ i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (by omega))
        (fun τ _ _ => hw0 τ)
    have hterm : ∀ τ ∈ Finset.Ico (s + 1 + P0) u, (1 - 2 * ε) * β i ≤ work h L τ i := by
      intro τ hτ
      rw [Finset.mem_Ico] at hτ
      rw [work_eq_of_next_pos h L τ i (hb (τ + 1) (by omega) (by omega))]
      have hc := climb hN hε hε' hη hη' hβ hβsum hrun i (s + 1) (τ - (s + 1))
        (fun τ' h1 h2 => hb τ' (by omega) (by omega))
      rw [show s + 1 + (τ - (s + 1)) = τ by omega] at hc
      have hX : 1 ≤ ε / N * (1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ))) ^ (τ - (s + 1)) :=
        le_trans hP0 (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1 (by omega)) hfl.le)
      have hmin : min ((1 - η * (ε ^ 2 / (8 * (N : ℝ)))) * β i)
          (ε / N * (1 + ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ))) ^ (τ - (s + 1))) =
          (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) * β i := min_eq_left (by linarith)
      rw [hmin] at hc
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hsu] at hsum
    push_cast at hsum
    linarith
  · push_neg at hsu
    have h1 : (u : ℝ) - s ≤ (P0 : ℝ) + 1 := by
      have : u ≤ s + P0 + 1 := by omega
      have : (u : ℝ) ≤ s + P0 + 1 := by exact_mod_cast this
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 ha0
    have h3 : 0 ≤ ∑ τ ∈ Finset.Ico s u, work h L τ i := Finset.sum_nonneg (fun τ _ => hw0 τ)
    linarith

end Aux_CA4

set_option maxHeartbeats 1600000 in
open CloudAlloc.MWU Aux_CA4 in
theorem solution {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N ≤ β j)
    (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let pt := 32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * Real.log ((N : ℝ) / ε)
    ∀ (i : Fin N) (h' : ℕ → Fin N → ℝ), (∀ τ, h' τ i = (1 - 2 * ε) * β i) →
      (∀ t, userWork h' L i t ≤ userWork h L i (t + ⌊pt⌋₊)) ∧
        (∀ t, userWork h' L i t - β i * pt ≤ userWork h L i t) := by
  intro pt i h' hh'
  have hpt : pt = 32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * Real.log ((N : ℝ) / ε) := rfl
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  obtain ⟨hθ0, hθ1⟩ := theta_small hN hε hε' hη hη'
  have hβ0 : 0 ≤ β i := by
    have h1 := hβ i
    have : 0 < Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N := by positivity
    linarith
  have ha0 : 0 ≤ (1 - 2 * ε) * β i := mul_nonneg (by linarith) hβ0
  have haβ : (1 - 2 * ε) * β i ≤ β i := mul_le_of_le_one_left hβ0 (by linarith)
  obtain ⟨c', hc'⟩ : ∃ c', c' = ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)) := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc']; positivity
  have hc'small : c' ≤ 1 / 100 := by
    rw [hc', div_le_iff₀ (by positivity)]
    have := mul_le_mul hε' hθ1 hθ0 (by norm_num : (0 : ℝ) ≤ 1 / 10)
    linarith
  have hlogN : 1 ≤ Real.log ((N : ℝ) / ε) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : (20 : ℝ) ≤ N / ε := by
      rw [le_div_iff₀ hε]
      linarith
    linarith
  have hpt0 : 0 ≤ pt := by
    rw [hpt]
    exact mul_nonneg (by positivity) (by linarith)
  have hptc : pt * c' = 2 * Real.log ((N : ℝ) / ε) := by
    have e : 32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * (ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)))
        = 2 := by
      first
        | (field_simp; ring1)
        | field_simp
    rw [hpt, hc']
    calc 32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * Real.log ((N : ℝ) / ε) *
          (ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ)))
        = 32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * (ε * η * (ε ^ 2 / (8 * (N : ℝ))) / (2 * (N : ℝ))) *
          Real.log ((N : ℝ) / ε) := by ring
      _ = 2 * Real.log ((N : ℝ) / ε) := by rw [e]
  obtain ⟨D, hD⟩ : ∃ D, D = 1 - (1 + c')⁻¹ := ⟨_, rfl⟩
  have hDl : D ≤ Real.log (1 + c') := by
    rw [hD]; exact Real.one_sub_inv_le_log_of_pos (by linarith)
  have hD23 : 2 / 3 * c' ≤ D := by
    rw [hD]
    have : (1 + c')⁻¹ ≤ 1 - 2 / 3 * c' := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hc'0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - c')]
    linarith
  have hDpos : 0 < D := by linarith
  obtain ⟨X, hX⟩ : ∃ X, X = Real.log ((N : ℝ) / ε) / D := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact div_nonneg (by linarith) hDpos.le
  have hXD : X * D = Real.log ((N : ℝ) / ε) := by rw [hX]; exact div_mul_cancel₀ _ hDpos.ne'
  obtain ⟨P0, hP0⟩ : ∃ P0 : ℕ, P0 = ⌈X⌉₊ := ⟨_, rfl⟩
  have hP0X : X ≤ (P0 : ℝ) := by rw [hP0]; exact Nat.le_ceil X
  have hP0lt : (P0 : ℝ) < X + 1 := by rw [hP0]; exact Nat.ceil_lt_add_one hX0
  have hC1 : 1 ≤ ε / N * (1 + c') ^ P0 := by
    have hlogpow : Real.log ((N : ℝ) / ε) ≤ Real.log ((1 + c') ^ P0) := by
      rw [Real.log_pow]
      have := mul_le_mul hP0X hDl hDpos.le (Nat.cast_nonneg P0)
      linarith
    have hNεpos : 0 < (N : ℝ) / ε := div_pos hNpos hε
    have h1 := (Real.log_le_log_iff hNεpos (pow_pos (by linarith) P0)).mp hlogpow
    have e : ε / N * (N / ε) = 1 := by field_simp
    have := mul_le_mul_of_nonneg_left h1 hfl.le
    linarith
  have hC1' := hC1
  rw [hc'] at hC1'
  have hC2 : P0 + 1 ≤ ⌊pt⌋₊ := by
    apply Nat.le_floor
    push_cast
    have h1 : X * c' ≤ 3 / 2 * Real.log ((N : ℝ) / ε) := by
      have := mul_le_mul_of_nonneg_left hD23 hX0
      linarith
    have h2 : ((P0 : ℝ) + 1) * c' ≤ (X + 2) * c' :=
      mul_le_mul_of_nonneg_right (by linarith) hc'0.le
    have h3 : ((P0 : ℝ) + 1) * c' ≤ pt * c' := by linarith
    exact le_of_mul_le_mul_right h3 hc'0
  have hPpt : ((⌊pt⌋₊ : ℕ) : ℝ) ≤ pt := Nat.floor_le hpt0
  have hPc : (P0 : ℝ) + 1 ≤ ((⌊pt⌋₊ : ℕ) : ℝ) := by exact_mod_cast hC2
  have haP : (1 - 2 * ε) * β i * ((P0 : ℝ) + 1) ≤ (1 - 2 * ε) * β i * ((⌊pt⌋₊ : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hPc ha0
  refine ⟨?_, ?_⟩
  · intro t
    unfold userWork
    rw [cum_work h' L i t, cum_work h L i (t + ⌊pt⌋₊),
      ← Finset.sum_range_add_sum_Ico _ (by omega : t ≤ t + ⌊pt⌋₊)]
    have hQ'0 := queue_nonneg h' L t i
    have hLnn : 0 ≤ ∑ τ ∈ Finset.Ico t (t + ⌊pt⌋₊), L τ i :=
      Finset.sum_nonneg (fun τ _ => hL τ i)
    by_cases hQ : 0 < queue h L (t + ⌊pt⌋₊) i
    · obtain ⟨s, hs, hQs, hb⟩ := last_zero h L i (t + ⌊pt⌋₊) hQ
      have hqi := queue_Ico h L i s (t + ⌊pt⌋₊) hs.le
      rw [hQs] at hqi
      have hw0 : 0 ≤ ∑ τ ∈ Finset.Ico s (t + ⌊pt⌋₊), work h L τ i :=
        Finset.sum_nonneg (fun τ _ => work_nonneg hN hε hL hrun τ i)
      by_cases hts : t ≤ s
      · have hsub : ∑ τ ∈ Finset.Ico s (t + ⌊pt⌋₊), L τ i ≤
            ∑ τ ∈ Finset.Ico t (t + ⌊pt⌋₊), L τ i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hts)
            (fun τ _ _ => hL τ i)
        linarith
      · push_neg at hts
        have hkl := KL hN hε hε' hη hη' hβ hβsum hL hrun i P0 hC1' s (t + ⌊pt⌋₊) hb
        have hlin := lindley h' L i ((1 - 2 * ε) * β i) hh' s (t - s)
        rw [show s + (t - s) = t by omega, Nat.cast_sub hts.le] at hlin
        have hQ's := queue_nonneg h' L s i
        have hsplit : ∑ τ ∈ Finset.Ico s t, L τ i + ∑ τ ∈ Finset.Ico t (t + ⌊pt⌋₊), L τ i =
            ∑ τ ∈ Finset.Ico s (t + ⌊pt⌋₊), L τ i :=
          Finset.sum_Ico_consecutive _ hts.le (by omega)
        push_cast at hkl
        linarith
    · have hQ0 : queue h L (t + ⌊pt⌋₊) i = 0 :=
        le_antisymm (not_lt.mp hQ) (queue_nonneg h L _ i)
      linarith
  · intro t
    unfold userWork
    rw [cum_work h' L i t, cum_work h L i t]
    have hQ'0 := queue_nonneg h' L t i
    have hβpt : (1 - 2 * ε) * β i * ((⌊pt⌋₊ : ℕ) : ℝ) ≤ β i * pt := by
      have h1 := mul_le_mul_of_nonneg_right haβ (Nat.cast_nonneg (⌊pt⌋₊))
      have h2 := mul_le_mul_of_nonneg_left hPpt hβ0
      linarith
    by_cases hQ : 0 < queue h L t i
    · obtain ⟨s, hs, hQs, hb⟩ := last_zero h L i t hQ
      have hqi := queue_Ico h L i s t hs.le
      rw [hQs] at hqi
      have hkl := KL hN hε hε' hη hη' hβ hβsum hL hrun i P0 hC1' s t hb
      have hlin := lindley h' L i ((1 - 2 * ε) * β i) hh' s (t - s)
      rw [show s + (t - s) = t by omega, Nat.cast_sub hs.le] at hlin
      have hQ's := queue_nonneg h' L s i
      linarith
    · have hQ0 : queue h L t i = 0 := le_antisymm (not_lt.mp hQ) (queue_nonneg h L _ i)
      have : 0 ≤ β i * pt := mul_nonneg hβ0 hpt0
      linarith
