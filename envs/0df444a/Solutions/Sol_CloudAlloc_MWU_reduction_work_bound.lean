-- Prove2me | solution 1 for CloudAlloc.MWU.reduction_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:52:53.388523+00:00
-- url     : https://prove2.me/submissions/456d4838-ce3d-4df1-a95f-0f9699b5e3ce

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_totalWork

namespace Aux_CA32

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

/-- indicator of a low-utilisation step -/
noncomputable def ind {N : ℕ} (ε : ℝ) (h L : ℕ → Fin N → ℝ) (τ : ℕ) : ℝ :=
  if ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j ≤ 1 - ε then 1 else 0

theorem ind_nonneg {N : ℕ} (ε : ℝ) (h L : ℕ → Fin N → ℝ) (τ : ℕ) : 0 ≤ ind ε h L τ := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one {N : ℕ} (ε : ℝ) (h L : ℕ → Fin N → ℝ) (τ : ℕ) : ind ε h L τ ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- allocation of idle users -/
noncomputable def inact {N : ℕ} (h L : ℕ → Fin N → ℝ) (τ : ℕ) : ℝ :=
  ∑ j, if 0 < queue h L τ j then 0 else h τ j

theorem act_add_inact {N : ℕ} {ε η : ℝ} {β : Fin N → ℝ} {L h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (τ : ℕ) :
    ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j + inact h L τ = 1 := by
  unfold inact
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  rw [← (mem_trunc hrun τ).1]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem inact_le {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) {β : Fin N → ℝ}
    {L h : ℕ → Fin N → ℝ} (hrun : IsAlg1Run N ε η β L h) (τ : ℕ) :
    inact h L τ ≤ ε + ind ε h L τ := by
  have e := act_add_inact hrun τ
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j :=
    Finset.sum_nonneg (fun j _ => (h_pos hN hε hrun τ j).le)
  unfold ind
  split_ifs with hl
  · linarith
  · push_neg at hl
    linarith

theorem waste {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (t : ℕ) :
    1 - inact h L t - 100 / 99 * inact h L (t + 1) ≤ ∑ i, work h L t i := by
  have hp := h_pos hN hε hrun
  obtain ⟨hθ0, hθ1⟩ := theta_small hN hε hε' hη hη'
  have key : ∀ j, h t j - (if 0 < queue h L t j then 0 else h t j)
      - 100 / 99 * (if 0 < queue h L (t + 1) j then 0 else h (t + 1) j) ≤ work h L t j := by
    intro j
    have hw0 := work_nonneg hN hε hL hrun t j
    have hA : 0 ≤ (if 0 < queue h L (t + 1) j then 0 else h (t + 1) j) := by
      split_ifs
      · exact le_refl 0
      · exact (hp _ _).le
    by_cases hq : 0 < queue h L t j
    · rw [if_pos hq]
      by_cases hc : h t j ≤ L t j + queue h L t j
      · have : work h L t j = h t j := min_eq_left hc
        linarith
      · push_neg at hc
        have hq1 : ¬ 0 < queue h L (t + 1) j := by
          show ¬ 0 < max 0 (L t j + queue h L t j - h t j)
          rw [max_eq_left (show L t j + queue h L t j - h t j ≤ 0 by linarith)]
          exact lt_irrefl 0
        rw [if_neg hq1]
        have hb := boost_active hN hε hε' hη hη' hrun t j hq
        have hθ : (99 / 100 : ℝ) ≤ 1 - η * (ε ^ 2 / (8 * (N : ℝ))) := by linarith
        have : h t j * (99 / 100) ≤ h (t + 1) j :=
          le_trans (mul_le_mul_of_nonneg_left hθ (hp t j).le) hb
        linarith
    · rw [if_neg hq]
      linarith
  calc 1 - inact h L t - 100 / 99 * inact h L (t + 1)
      = ∑ j, (h t j - (if 0 < queue h L t j then 0 else h t j)
          - 100 / 99 * (if 0 < queue h L (t + 1) j then 0 else h (t + 1) j)) := by
        unfold inact
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          (mem_trunc hrun t).1]
    _ ≤ ∑ j, work h L t j := Finset.sum_le_sum (fun j _ => key j)

theorem step_log {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (t : ℕ) (i : Fin N) (hq : 0 < queue h L t i) :
    Real.log (h t i) + ind ε h L t * Real.log (1 + ε * η / (2 * (N : ℝ))) +
      Real.log (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) ≤ Real.log (h (t + 1) i) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hp := h_pos hN hε hrun t i
  have hρ0 : 0 ≤ ε * η / (2 * (N : ℝ)) := by positivity
  have hρpos : (0 : ℝ) < 1 + ε * η / (2 * (N : ℝ)) := by linarith
  obtain ⟨hθ0, hθ1⟩ := theta_small hN hε hε' hη hη'
  have hθpos : (0 : ℝ) < 1 - η * (ε ^ 2 / (8 * (N : ℝ))) := by linarith
  have hlogρ : 0 ≤ Real.log (1 + ε * η / (2 * (N : ℝ))) := Real.log_nonneg (by linarith)
  have hlogθ : Real.log (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) ≤ 0 :=
    Real.log_nonpos hθpos.le (by linarith)
  unfold ind
  split_ifs with hlw
  · have h1 := boost_low hN hε hε' hη hη' hrun t hlw i hq
    have h2 := Real.log_le_log (mul_pos hp hρpos) h1
    rw [Real.log_mul hp.ne' hρpos.ne'] at h2
    linarith
  · have h1 := boost_active hN hε hε' hη hη' hrun t i hq
    have h2 := Real.log_le_log (mul_pos hp hθpos) h1
    rw [Real.log_mul hp.ne' hθpos.ne'] at h2
    linarith

theorem block_log {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (i : Fin N) (r : ℕ) : ∀ m : ℕ,
    (∀ τ, r ≤ τ → τ < r + m → 0 < queue h L τ i) →
    Real.log (h r i) + (∑ τ ∈ Finset.Ico r (r + m), ind ε h L τ) *
        Real.log (1 + ε * η / (2 * (N : ℝ))) +
      (m : ℝ) * Real.log (1 - η * (ε ^ 2 / (8 * (N : ℝ)))) ≤ Real.log (h (r + m) i) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hb
    have ih' := ih (fun τ h1 h2 => hb τ h1 (by omega))
    have hq : 0 < queue h L (r + m) i := hb (r + m) (by omega) (by omega)
    have hs := step_log hN hε hε' hη hη' hrun (r + m) i hq
    have e : r + (m + 1) = r + m + 1 := by omega
    rw [e, Finset.sum_Ico_succ_top (by omega : r ≤ r + m)]
    push_cast
    linarith

theorem block_bound {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (c st : ℝ) (hc : c = ε * η / (4 * (N : ℝ)))
    (hst : st = Real.log ((N : ℝ) / ε) / (ε * c))
    (i : Fin N) (r m : ℕ) (hb : ∀ τ, r ≤ τ → τ < r + m → 0 < queue h L τ i) :
    (∑ τ ∈ Finset.Ico r (r + m), ind ε h L τ) * 2 ≤ (1 + 2 * c) * ε * (st + 50 / 99 * m) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hεη : ε * η ≤ 1 / 30 := by
    have := mul_le_mul hε' hη' hη.le (by norm_num : (0 : ℝ) ≤ 1 / 10)
    linarith
  have hc1 : c ≤ 1 / 240 := by
    rw [hc, div_le_iff₀ (by linarith)]
    linarith
  have hεc : ε * c ≤ 1 / 2400 := by
    have := mul_le_mul hε' hc1 hc0.le (by norm_num : (0 : ℝ) ≤ 1 / 10)
    linarith
  have hεc0 : 0 < ε * c := mul_pos hε hc0
  have hρ : ε * η / (2 * (N : ℝ)) = 2 * c := by rw [hc]; ring
  have hθe : η * (ε ^ 2 / (8 * (N : ℝ))) = ε * c / 2 := by rw [hc]; ring
  have hK0 : 0 ≤ ∑ τ ∈ Finset.Ico r (r + m), ind ε h L τ :=
    Finset.sum_nonneg (fun τ _ => ind_nonneg ε h L τ)
  have hbl := block_log hN hε hε' hη hη' hrun i r m hb
  rw [hρ, hθe] at hbl
  have hup : Real.log (h (r + m) i) ≤ 0 :=
    Real.log_nonpos (h_pos hN hε hrun (r + m) i).le (h_le_one hN hε hrun (r + m) i)
  have hfl : 0 < ε / N := div_pos hε hNpos
  have hlo : Real.log (ε / N) ≤ Real.log (h r i) :=
    Real.log_le_log hfl ((mem_trunc hrun r).2 i)
  have hlogNe : Real.log (ε / N) = - Real.log (N / ε) := by rw [← Real.log_inv, inv_div]
  have hstl : Real.log (N / ε) = st * (ε * c) := by
    rw [hst, div_mul_cancel₀ _ hεc0.ne']
  have hρl : 1 - (1 + 2 * c)⁻¹ ≤ Real.log (1 + 2 * c) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have hθpos : 0 < 1 - ε * c / 2 := by linarith
  have hθl : 1 - (1 - ε * c / 2)⁻¹ ≤ Real.log (1 - ε * c / 2) :=
    Real.one_sub_inv_le_log_of_pos hθpos
  have hθinv : (1 - ε * c / 2)⁻¹ ≤ 1 + 50 / 99 * (ε * c) := by
    rw [inv_eq_one_div, div_le_iff₀ hθpos]
    nlinarith [mul_nonneg hεc0.le (by linarith : (0 : ℝ) ≤ 1 / 2400 - ε * c)]
  have hρinv : (1 - (1 + 2 * c)⁻¹) * (1 + 2 * c) = 2 * c := by
    rw [sub_mul, inv_mul_cancel₀ (show (1 : ℝ) + 2 * c ≠ 0 by positivity)]
    ring
  set K := ∑ τ ∈ Finset.Ico r (r + m), ind ε h L τ with hK
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmain : K * (1 - (1 + 2 * c)⁻¹) ≤ st * (ε * c) + m * (50 / 99 * (ε * c)) := by
    have h1 : K * (1 - (1 + 2 * c)⁻¹) ≤ K * Real.log (1 + 2 * c) :=
      mul_le_mul_of_nonneg_left hρl hK0
    have h2 : (m : ℝ) * (-Real.log (1 - ε * c / 2)) ≤ m * (50 / 99 * (ε * c)) := by
      have : -Real.log (1 - ε * c / 2) ≤ 50 / 99 * (ε * c) := by linarith
      exact mul_le_mul_of_nonneg_left this hm0
    linarith
  have h3 : K * (2 * c) ≤ (st * (ε * c) + m * (50 / 99 * (ε * c))) * (1 + 2 * c) := by
    calc K * (2 * c) = K * (1 - (1 + 2 * c)⁻¹) * (1 + 2 * c) := by rw [mul_assoc, hρinv]
      _ ≤ (st * (ε * c) + m * (50 / 99 * (ε * c))) * (1 + 2 * c) :=
        mul_le_mul_of_nonneg_right hmain (by linarith)
  have h4 : c * (K * 2) ≤ c * ((1 + 2 * c) * ε * (st + 50 / 99 * m)) := by
    have e1 : c * (K * 2) = K * (2 * c) := by ring
    have e2 : c * ((1 + 2 * c) * ε * (st + 50 / 99 * m)) =
        (st * (ε * c) + m * (50 / 99 * (ε * c))) * (1 + 2 * c) := by ring
    rw [e1, e2]
    exact h3
  exact le_of_mul_le_mul_left h4 hc0

/-- Claim 3.1 (busy user), for any block length `S` and `r ≤ T` -/
theorem busy {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) {β : Fin N → ℝ}
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (T sstar S : ℕ)
    (hG : IsGreatest {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} sstar)
    (r : ℕ) (hr : sstar < r) (hrT : r ≤ T) :
    ∃ i, ∀ r' ∈ Finset.Icc r (r + S), 0 < queue h L r' i := by
  by_contra hno
  push_neg at hno
  choose ri hri hq using hno
  have hwork : ∀ t k, 0 ≤ work h L t k := fun t k => work_nonneg hN hε hL hrun t k
  have hq0 : ∀ i, queue h L (ri i) i = 0 := fun i => le_antisymm (hq i) (queue_nonneg h L _ i)
  have hper : ∀ i, ∑ t ∈ Finset.range r, L t i ≤ ∑ t ∈ Finset.range (r + S), work h L t i := by
    intro i
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hri i)
    have e := cum_work h L i (ri i)
    rw [hq0 i, sub_zero] at e
    calc ∑ t ∈ Finset.range r, L t i ≤ ∑ t ∈ Finset.range (ri i), L t i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h1)
            (fun t _ _ => hL t i)
      _ = ∑ t ∈ Finset.range (ri i), work h L t i := e.symm
      _ ≤ ∑ t ∈ Finset.range (r + S), work h L t i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h2)
            (fun t _ _ => hwork t i)
  have hmem : r ∈ {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
      ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} := by
    rw [Set.mem_setOf_eq]
    refine ⟨hrT, ?_⟩
    calc ∑ t ∈ Finset.range r, ∑ i, L t i = ∑ i, ∑ t ∈ Finset.range r, L t i := Finset.sum_comm
      _ ≤ ∑ i, ∑ t ∈ Finset.range (r + S), work h L t i := Finset.sum_le_sum (fun i _ => hper i)
      _ = ∑ t ∈ Finset.range (r + S), ∑ i, work h L t i := Finset.sum_comm
  have := hG.2 hmem
  omega

theorem Kbound {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (T sstar S : ℕ)
    (hG : IsGreatest {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} sstar)
    (c st : ℝ) (hc : c = ε * η / (4 * (N : ℝ)))
    (hst : st = Real.log ((N : ℝ) / ε) / (ε * c)) (hst0 : 0 ≤ st) :
    ∀ d r : ℕ, r + d = T → sstar < r →
      (∑ τ ∈ Finset.Ico r (r + d), ind ε h L τ) * 2 * ((S : ℝ) + 1) ≤
        (1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) * ((S : ℝ) + 1 + d) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hblk : ∀ r, sstar < r → r ≤ T →
      (∑ τ ∈ Finset.Ico r (r + (S + 1)), ind ε h L τ) * 2 ≤
        (1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) := by
    intro r hr hrT
    obtain ⟨i, hi⟩ := busy hN hε hL hrun T sstar S hG r hr hrT
    have := block_bound hN hε hε' hη hη' hrun c st hc hst i r (S + 1)
      (fun τ h1 h2 => hi τ (Finset.mem_Icc.mpr ⟨h1, by omega⟩))
    push_cast at this
    exact this
  have hS0 : (0 : ℝ) ≤ (S : ℝ) + 1 := by positivity
  have hB0 : 0 ≤ (1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) := by positivity
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r hrd hr
    by_cases hd : d ≤ S + 1
    · have hsub : ∑ τ ∈ Finset.Ico r (r + d), ind ε h L τ ≤
          ∑ τ ∈ Finset.Ico r (r + (S + 1)), ind ε h L τ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
          (fun τ _ _ => ind_nonneg ε h L τ)
      have h1 := hblk r hr (by omega)
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      calc (∑ τ ∈ Finset.Ico r (r + d), ind ε h L τ) * 2 * ((S : ℝ) + 1)
          ≤ (1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) * ((S : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hS0
        _ ≤ (1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) * ((S : ℝ) + 1 + d) :=
            mul_le_mul_of_nonneg_left (by linarith) hB0
    · push_neg at hd
      obtain ⟨d', rfl⟩ : ∃ d', d = S + 1 + d' := ⟨d - (S + 1), by omega⟩
      have hsplit := Finset.sum_Ico_consecutive (ind ε h L)
        (show r ≤ r + (S + 1) by omega) (show r + (S + 1) ≤ r + (S + 1 + d') by omega)
      have h1 := hblk r hr (by omega)
      have h2 := ih d' (by omega) (r + (S + 1)) (by omega) (by omega)
      rw [show r + (S + 1) + d' = r + (S + 1 + d') by omega] at h2
      rw [← hsplit]
      push_cast
      have h1' := mul_le_mul_of_nonneg_right h1 hS0
      linarith

theorem card_le_ind {N : ℕ} (ε : ℝ) (h L : ℕ → Fin N → ℝ) (s : Finset ℕ) (r M : ℕ)
    (hs : ∀ τ ∈ s, r ≤ τ ∧ τ < r + M) :
    ((s.filter (fun τ => ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j ≤ 1 - ε)).card
      : ℝ) ≤ ∑ τ ∈ Finset.Ico r (r + M), ind ε h L τ := by
  calc ((s.filter (fun τ => ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j ≤
          1 - ε)).card : ℝ) = ∑ τ ∈ s, ind ε h L τ := by
        rw [Finset.natCast_card_filter]
        try rfl
    _ ≤ ∑ τ ∈ Finset.Ico r (r + M), ind ε h L τ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun τ hτ => by
            obtain ⟨h1, h2⟩ := hs τ hτ
            exact Finset.mem_Ico.mpr ⟨h1, h2⟩)
          (fun τ _ _ => ind_nonneg ε h L τ)


theorem claim32 {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h)
    (T sstar : ℕ) (c st : ℝ) (S : ℕ) (hc_def : c = ε * η / (4 * (N : ℝ)))
    (hst_def : st = Real.log ((N : ℝ) / ε) / (ε * c)) (hS_def : S = ⌊st⌋₊)
    (hG : IsGreatest {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} sstar) :
      (∀ r : ℕ, sstar ≤ r → (r : ℝ) + st ≤ T →
          ((((Finset.range T).filter (fun τ => r ≤ τ ∧ (τ : ℝ) < r + st)).filter
              (fun τ => ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j ≤ 1 - ε)).card
              : ℝ) ≤ 4 * ε * st) ∧
        (1 - 4 * ε) * ((T : ℝ) - sstar) - st ≤ ∑ t ∈ Finset.Ico sstar T, ∑ i, work h L t i := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hc0 : 0 < c := by rw [hc_def]; positivity
  have hεη : ε * η ≤ 1 / 30 := by
    have := mul_le_mul hε' hη' hη.le (by norm_num : (0 : ℝ) ≤ 1 / 10)
    linarith
  have hc1 : c ≤ 1 / 240 := by
    rw [hc_def, div_le_iff₀ (by linarith)]
    linarith
  have hεc : ε * c ≤ 1 / 2400 := by
    have := mul_le_mul hε' hc1 hc0.le (by norm_num : (0 : ℝ) ≤ 1 / 10)
    linarith
  have hεc0 : 0 < ε * c := mul_pos hε hc0
  have hlogN : 1 ≤ Real.log ((N : ℝ) / ε) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : (20 : ℝ) ≤ N / ε := by
      rw [le_div_iff₀ hε]
      linarith
    linarith
  have hstl : st * (ε * c) = Real.log ((N : ℝ) / ε) := by
    rw [hst_def]
    exact div_mul_cancel₀ _ hεc0.ne'
  have hst0 : 2400 ≤ st := by
    by_contra hcon
    push_neg at hcon
    have hstpos : 0 ≤ st := by
      rw [hst_def]; exact div_nonneg (by linarith) hεc0.le
    have := mul_le_mul_of_nonneg_left hεc hstpos
    linarith
  have hεst : 240 ≤ ε * st := by
    by_contra hcon
    push_neg at hcon
    have h1 : ε * st * c = Real.log ((N : ℝ) / ε) := by rw [← hstl]; ring
    have := mul_lt_mul_of_pos_right hcon hc0
    linarith
  have hSlt : st < (S : ℝ) + 1 := by rw [hS_def]; exact Nat.lt_floor_add_one st
  have hSle : (S : ℝ) ≤ st := by rw [hS_def]; exact Nat.floor_le (by linarith)
  have hsT : sstar ≤ T := hG.1.1
  have hP0 : 0 ≤ (1 + 2 * c) * ε := by positivity
  have hP1 : (1 + 2 * c) * ε ≤ 121 / 120 * ε := by
    have := mul_le_mul_of_nonneg_left hc1 hε.le
    linarith
  have hP2 : (1 + 2 * c) * ε ≤ 121 / 1200 := by linarith
  have hεst10 : ε * st ≤ 1 / 10 * st := mul_le_mul_of_nonneg_right hε' (by linarith)
  have hPst : (1 + 2 * c) * ε * st ≤ 121 / 120 * (ε * st) := by
    have := mul_le_mul_of_nonneg_right hP1 (by linarith : (0 : ℝ) ≤ st)
    linarith
  have hPS : (1 + 2 * c) * ε * ((S : ℝ) + 1) ≤ (1 + 2 * c) * ε * (st + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hP0
  refine ⟨?_, ?_⟩
  · intro r hr hrT
    have hrT' : r + 1 ≤ T := by
      have : (r : ℝ) < T := by linarith
      have : r < T := by exact_mod_cast this
      omega
    obtain ⟨i, hi⟩ := busy hN hε hL hrun T sstar S hG (r + 1) (by omega) hrT'
    have hbb := block_bound hN hε hε' hη hη' hrun c st hc_def hst_def i (r + 1) (S + 1)
      (fun τ h1 h2 => hi τ (Finset.mem_Icc.mpr ⟨h1, by omega⟩))
    push_cast at hbb
    have hcard := card_le_ind ε h L
      ((Finset.range T).filter (fun τ => r ≤ τ ∧ (τ : ℝ) < r + st)) r (S + 2) (by
        intro τ hτ
        rw [Finset.mem_filter] at hτ
        obtain ⟨_, h1, h2⟩ := hτ
        refine ⟨h1, ?_⟩
        have : (τ : ℝ) < r + S + 1 := by linarith
        have : τ < r + S + 1 := by exact_mod_cast this
        omega)
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : r < r + (S + 2)),
      show r + (S + 2) = r + 1 + (S + 1) by omega] at hcard
    have hi1 := ind_le_one ε h L r
    linarith
  · rcases Nat.eq_or_lt_of_le hsT with heq | hlt
    · subst heq
      rw [Finset.Ico_self, Finset.sum_empty, sub_self, mul_zero]
      linarith
    · have hW : ∀ t, 1 - inact h L t - 100 / 99 * inact h L (t + 1) ≤ ∑ i, work h L t i :=
        fun t => waste hN hε hε' hη hη' hL hrun t
      have hsum1 : ∑ t ∈ Finset.Ico sstar T, (1 - inact h L t - 100 / 99 * inact h L (t + 1)) ≤
          ∑ t ∈ Finset.Ico sstar T, ∑ i, work h L t i := Finset.sum_le_sum (fun t _ => hW t)
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hsT] at hsum1
      have hKr := Kbound hN hε hε' hη hη' hL hrun T sstar S hG c st hc_def hst_def
        (by linarith) (T - (sstar + 1)) (sstar + 1) (by omega) (by omega)
      rw [show sstar + 1 + (T - (sstar + 1)) = T by omega] at hKr
      have hdR : ((T - (sstar + 1) : ℕ) : ℝ) = (T : ℝ) - sstar - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hdR] at hKr
      obtain ⟨Kr, hKrdef⟩ : ∃ K, K = ∑ τ ∈ Finset.Ico (sstar + 1) T, ind ε h L τ := ⟨_, rfl⟩
      rw [← hKrdef] at hKr
      have hI1 : ∑ t ∈ Finset.Ico sstar T, inact h L t ≤ ε * ((T : ℝ) - sstar) + (1 + Kr) := by
        calc ∑ t ∈ Finset.Ico sstar T, inact h L t
            ≤ ∑ t ∈ Finset.Ico sstar T, (ε + ind ε h L t) :=
              Finset.sum_le_sum (fun t _ => inact_le hN hε hrun t)
          _ = ε * ((T : ℝ) - sstar) + ∑ t ∈ Finset.Ico sstar T, ind ε h L t := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
                Nat.cast_sub hsT]
              ring
          _ ≤ ε * ((T : ℝ) - sstar) + (1 + Kr) := by
              rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← hKrdef]
              linarith [ind_le_one ε h L sstar]
      have hI2 : ∑ t ∈ Finset.Ico sstar T, inact h L (t + 1) ≤
          ε * ((T : ℝ) - sstar) + (Kr + 1) := by
        calc ∑ t ∈ Finset.Ico sstar T, inact h L (t + 1)
            ≤ ∑ t ∈ Finset.Ico sstar T, (ε + ind ε h L (t + 1)) :=
              Finset.sum_le_sum (fun t _ => inact_le hN hε hrun (t + 1))
          _ = ε * ((T : ℝ) - sstar) + ∑ t ∈ Finset.Ico sstar T, ind ε h L (t + 1) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
                Nat.cast_sub hsT]
              ring
          _ ≤ ε * ((T : ℝ) - sstar) + (Kr + 1) := by
              rw [Finset.sum_Ico_add' (ind ε h L) sstar T 1,
                Finset.sum_Ico_succ_top (by omega : sstar + 1 ≤ T), ← hKrdef]
              linarith [ind_le_one ε h L T]
      -- Kr bound
      have hm0 : (0 : ℝ) < (S : ℝ) + 1 := by positivity
      have hn1 : (0 : ℝ) ≤ (T : ℝ) - sstar - 1 := by
        have : sstar + 1 ≤ T := hlt
        have : ((sstar + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast this
        push_cast at this
        linarith
      have hBd : (1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) * ((T : ℝ) - sstar - 1) ≤
          (149 / 99 * ((1 + 2 * c) * ε) * ((S : ℝ) + 1)) * ((T : ℝ) - sstar - 1) := by
        apply mul_le_mul_of_nonneg_right _ hn1
        have := mul_le_mul_of_nonneg_left
          (show st + 50 / 99 * ((S : ℝ) + 1) ≤ 149 / 99 * ((S : ℝ) + 1) by linarith) hP0
        linarith
      have hKr2 : ((S : ℝ) + 1) * (Kr * 2) ≤ ((S : ℝ) + 1) *
          ((1 + 2 * c) * ε * (st + 50 / 99 * ((S : ℝ) + 1)) +
            149 / 99 * ((1 + 2 * c) * ε) * ((T : ℝ) - sstar - 1)) := by
        linarith
      have hKr3 := le_of_mul_le_mul_left hKr2 hm0
      have hPd : (1 + 2 * c) * ε * ((T : ℝ) - sstar - 1) ≤ 121 / 120 * ε * ((T : ℝ) - sstar - 1) :=
        mul_le_mul_of_nonneg_right hP1 hn1
      have hεn : 0 ≤ ε * ((T : ℝ) - sstar - 1) := mul_nonneg hε.le hn1
      linarith

theorem upper_work {N : ℕ} (g L : ℕ → Fin N → ℝ) (T sstar : ℕ) (hsT : sstar ≤ T) (B : ℝ)
    (hg : ∀ t, sstar ≤ t → t < T → ∑ i, g t i ≤ B) :
    totalWork g L T ≤ ∑ t ∈ Finset.range sstar, ∑ i, L t i + B * ((T : ℝ) - sstar) := by
  unfold totalWork
  rw [← Finset.sum_range_add_sum_Ico _ hsT]
  have h1 : ∑ t ∈ Finset.range sstar, ∑ i, work g L t i ≤
      ∑ t ∈ Finset.range sstar, ∑ i, L t i := by
    calc ∑ t ∈ Finset.range sstar, ∑ i, work g L t i
        = ∑ i, ∑ t ∈ Finset.range sstar, work g L t i := Finset.sum_comm
      _ ≤ ∑ i, ∑ t ∈ Finset.range sstar, L t i := by
          apply Finset.sum_le_sum
          intro i _
          rw [cum_work g L i sstar]
          linarith [queue_nonneg g L sstar i]
      _ = ∑ t ∈ Finset.range sstar, ∑ i, L t i := Finset.sum_comm
  have h2 : ∑ t ∈ Finset.Ico sstar T, ∑ i, work g L t i ≤ ∑ t ∈ Finset.Ico sstar T, B := by
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Ico] at ht
    calc ∑ i, work g L t i ≤ ∑ i, g t i := Finset.sum_le_sum (fun i _ => work_le g L t i)
      _ ≤ B := hg t ht.1 ht.2
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hsT] at h2
  linarith

theorem lower_pre {N : ℕ} {ε η : ℝ} {β : Fin N → ℝ} {L h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) (sstar S : ℕ)
    (hP : ∑ t ∈ Finset.range sstar, ∑ i, L t i ≤
      ∑ t ∈ Finset.range (sstar + S), ∑ i, work h L t i) :
    ∑ t ∈ Finset.range sstar, ∑ i, L t i - S ≤ ∑ t ∈ Finset.range sstar, ∑ i, work h L t i := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : sstar ≤ sstar + S)] at hP
  have h2 : ∑ t ∈ Finset.Ico sstar (sstar + S), ∑ i, work h L t i ≤
      ∑ t ∈ Finset.Ico sstar (sstar + S), (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro t _
    calc ∑ i, work h L t i ≤ ∑ i, h t i := Finset.sum_le_sum (fun i _ => work_le h L t i)
      _ = 1 := (mem_trunc hrun t).1
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
    show sstar + S - sstar = S by omega] at h2
  linarith

end Aux_CA32

set_option maxHeartbeats 1600000 in
open CloudAlloc.MWU Aux_CA32 in
theorem solution {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    ∀ (T : ℕ) (hs : ℕ → Fin N → ℝ), (∀ t < T, (∀ i, 0 ≤ hs t i) ∧ ∑ i, hs t i ≤ 1) →
      totalWork (fun t j => (1 - 4 * ε) * hs t j) L T
          - 8 * (N : ℝ) / ((ε / 4) ^ 2 * η) * Real.log (4 * (N : ℝ) / ε) ≤ totalWork h L T ∧
        (1 - 4 * ε) * totalWork hs L T
          - 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) ≤ totalWork h L T := by
  intro T hs hhs
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ε * η / (4 * (N : ℝ)) := ⟨_, rfl⟩
  obtain ⟨st, hst⟩ : ∃ st : ℝ, st = Real.log ((N : ℝ) / ε) / (ε * c) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = ⌊st⌋₊ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hNε : (0 : ℝ) < N / ε := div_pos hNpos hε
  have hlog0 : 0 ≤ Real.log ((N : ℝ) / ε) :=
    Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hst0 : 0 ≤ st := by rw [hst]; exact div_nonneg hlog0 (mul_pos hε hc0).le
  have hSle : (S : ℝ) ≤ st := by rw [hS]; exact Nat.floor_le hst0
  have hwork0 : ∀ t i, 0 ≤ work h L t i := fun t i => work_nonneg hN hε hL hrun t i
  have hGr : IsGreatest {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
      ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i}
      (Nat.findGreatest (fun s => ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i) T) := by
    have hP0 : ∑ t ∈ Finset.range 0, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (0 + S), ∑ i, work h L t i := by
      rw [Finset.sum_range_zero]
      exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun i _ => hwork0 t i))
    refine ⟨⟨Nat.findGreatest_le T, Nat.findGreatest_spec (P := fun s => ∑ t ∈ Finset.range s,
      ∑ i, L t i ≤ ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i) (Nat.zero_le T) hP0⟩, ?_⟩
    intro s hs'
    exact Nat.le_findGreatest (P := fun s => ∑ t ∈ Finset.range s,
      ∑ i, L t i ≤ ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i) hs'.1 hs'.2
  generalize (Nat.findGreatest (fun s => ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i) T)
      = sstar at hGr
  have hsT : sstar ≤ T := hGr.1.1
  have hPs := hGr.1.2
  have hcl := (claim32 hN hε hε' hη hη' hL hrun T sstar c st S hc hst hS hGr).2
  have hlow := lower_pre hrun sstar S hPs
  have hsplit : totalWork h L T = ∑ t ∈ Finset.range sstar, ∑ i, work h L t i +
      ∑ t ∈ Finset.Ico sstar T, ∑ i, work h L t i := by
    unfold totalWork
    rw [Finset.sum_range_add_sum_Ico _ hsT]
  have hCL0 : 0 ≤ ∑ t ∈ Finset.range sstar, ∑ i, L t i :=
    Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun i _ => hL t i))
  have hst4 : st * (ε ^ 2 * η) = 4 * N * Real.log ((N : ℝ) / ε) := by
    have e : ε * c * (4 * (N : ℝ)) = ε ^ 2 * η := by
      rw [hc, mul_assoc, div_mul_cancel₀ _ (ne_of_gt (by linarith : (0 : ℝ) < 4 * N))]
      ring
    have e2 : st * (ε * c) = Real.log ((N : ℝ) / ε) := by
      rw [hst]; exact div_mul_cancel₀ _ (mul_pos hε hc0).ne'
    calc st * (ε ^ 2 * η) = st * (ε * c) * (4 * N) := by rw [← e]; ring
      _ = 4 * N * Real.log ((N : ℝ) / ε) := by rw [e2]; ring
  have hD : 0 < ε ^ 2 * η := by positivity
  have hε4 : 0 ≤ 1 - 4 * ε := by linarith
  have hNl : 0 ≤ (N : ℝ) * Real.log ((N : ℝ) / ε) := mul_nonneg hNpos.le hlog0
  constructor
  · have hup := upper_work (fun t j => (1 - 4 * ε) * hs t j) L T sstar hsT (1 - 4 * ε) (by
      intro t _ ht
      show ∑ i, (1 - 4 * ε) * hs t i ≤ 1 - 4 * ε
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right hε4 (hhs t ht).2)
    have hlogle : Real.log ((N : ℝ) / ε) ≤ Real.log (4 * (N : ℝ) / ε) :=
      Real.log_le_log hNε (by rw [mul_div_assoc]; linarith)
    have hbound : 2 * st ≤ 8 * (N : ℝ) / ((ε / 4) ^ 2 * η) * Real.log (4 * (N : ℝ) / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have e : 2 * st * ((ε / 4) ^ 2 * η) = st * (ε ^ 2 * η) / 8 := by ring
      rw [e, hst4]
      have := mul_le_mul_of_nonneg_left hlogle hNpos.le
      linarith
    linarith
  · have hup := upper_work hs L T sstar hsT 1 (fun t _ ht => (hhs t ht).2)
    have hbound : 2 * st ≤ 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hD]
      have e : 2 * st * (ε ^ 2 * η) = 2 * (st * (ε ^ 2 * η)) := by ring
      rw [e, hst4]
      linarith
    have hm := mul_le_mul_of_nonneg_left hup hε4
    have hεCL := mul_nonneg hε.le hCL0
    linarith
