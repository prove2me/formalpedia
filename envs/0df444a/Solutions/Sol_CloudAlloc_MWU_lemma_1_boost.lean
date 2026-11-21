-- Prove2me | solution 1 for CloudAlloc.MWU.lemma_1_boost
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:04:02.533772+00:00
-- url     : https://prove2.me/submissions/d5ad80e2-b66e-4a46-b043-96da10ac4701

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run

namespace Aux_CA_boost

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

end Aux_CA_boost

set_option maxHeartbeats 1600000 in
open CloudAlloc.MWU Aux_CA_boost in
theorem solution {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let c := ε * η / (4 * (N : ℝ))
    (∀ t, ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L t j), h t j ≤ 1 - ε →
        ∀ i, 0 < queue h L t i → h t i * (1 + c) ≤ h (t + 1) i) ∧
      (∀ t i, 0 < queue h L t i → h t i < β i → h t i ≤ h (t + 1) i) ∧
      (∀ t i, 0 < queue h L t i → β i ≤ h t i → h t i * (1 - ε * c) ≤ h (t + 1) i) := by
  intro c
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  have hmem := mem_trunc hrun
  have hlow : ∀ t k, ε / N ≤ h t k := fun t k => (hmem t).2 k
  have hsum1 : ∀ t, ∑ k, h t k = 1 := fun t => (hmem t).1
  have hpos : ∀ t k, 0 < h t k := fun t k => lt_of_lt_of_le hfl (hlow t k)
  set a := ε ^ 2 / (8 * (N : ℝ)) with ha
  have ha0 : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by positivity
  -- the weights
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
  -- cross-multiplied form
  have hfoc' : ∀ t i j, ε / N < h (t + 1) j →
      h (t + 1) j * (h t i * E t i) ≤ h (t + 1) i * (h t j * E t j) := by
    intro t i j hj
    have := hfoc t i j hj
    rwa [div_le_div_iff₀ (hy t j) (hy t i)] at this
  refine ⟨?_, ?_, ?_⟩
  · -- (a) low utilisation boosts every busy user
    intro t hS i hq
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
    -- ratio of user i is below κ
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
    -- every coordinate is clamped or has ratio below κ
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
          show ε * η / (4 * (N : ℝ)) ≤ η
          rw [div_le_iff₀ (by linarith)]
          have : ε ≤ 4 * N := by linarith
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
    -- per-coordinate upper bounds
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
    -- summing up
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
    -- numerical contradiction
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
      have hc_eq : c = η * u / 4 := by
        rw [hu]; show ε * η / (4 * (N : ℝ)) = η * (ε / N) / 4; ring
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
      have P : 0 < 3 / 4 - η - u / 4 + η * u / 4 - η ^ 2 * u / 4 - ε / 4 - η * ε * u / 16 := by
        linarith
      have key : (1 - (1 + c) * (1 - η + η ^ 2)) * u - (c + 2 * (η * a) + 2 * c * (η * a)) =
          η * u * (3 / 4 - η - u / 4 + η * u / 4 - η ^ 2 * u / 4 - ε / 4 - η * ε * u / 16) := by
        rw [hc_eq, ha_eq]; ring
      have hpos' : 0 < η * u * (3 / 4 - η - u / 4 + η * u / 4 - η ^ 2 * u / 4 - ε / 4 -
          η * ε * u / 16) := mul_pos (mul_pos hη hu0) P
      have h1 : (1 - (1 + c) * (1 - η + η ^ 2)) * u ≤ (1 - κ) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have h2 : K - 1 ≤ c + 2 * (η * a) + 2 * c * (η * a) := by
        have : (1 + c) * (1 + 2 * (η * a)) = 1 + c + 2 * (η * a) + 2 * c * (η * a) := by ring
        linarith
      linarith
    linarith
  · -- (b)
    intro t i hq hlt
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
    -- x_j h_i E_i ≤ x_i h_j E_j ≤ x_i h_j E_i, and x_j > h_j
    have h2 : h (t + 1) i * (h t j * E t j) ≤ h (t + 1) i * (h t j * E t i) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (lt_of_lt_of_le hfl (hlow (t + 1) i)))
      exact mul_le_mul_of_nonneg_left hEij hpj.le
    have h3 : h t j * (h t i * E t i) < h (t + 1) j * (h t i * E t i) :=
      mul_lt_mul_of_pos_right hj (mul_pos hp hEi)
    have h4 : h t i * (h t j * E t i) < h (t + 1) i * (h t j * E t i) := by linarith
    have h5 := lt_of_mul_lt_mul_right h4 (mul_pos hpj hEi).le
    linarith
  · -- (c)
    intro t i hq hge
    by_contra hcon
    push_neg at hcon
    have hεc : ε * c ≤ 1 := by
      have : c ≤ 1 := by
        show ε * η / (4 * (N : ℝ)) ≤ 1
        rw [div_le_one (by linarith)]
        have : ε * η ≤ 1 := mul_le_one₀ (by linarith) hη.le (by linarith)
        linarith
      exact mul_le_one₀ (by linarith) hc0 this
    have hlt : h (t + 1) i < h t i := by
      have := hpos t i
      have : h t i * (1 - ε * c) ≤ h t i :=
        mul_le_of_le_one_right (hpos t i).le (by linarith [mul_nonneg hε.le hc0])
      linarith
    obtain ⟨j, hj⟩ := exists_gt (h (t + 1)) (h t) (hsum1 (t + 1)) (hsum1 t) i hlt
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
    -- h_j h_i e^η < x_j h_i e^η ≤ x_i h_j E_j ≤ x_i h_j e^η e^{ηa}
    have h3 : h t j * (h t i * E t i) < h (t + 1) j * (h t i * E t i) :=
      mul_lt_mul_of_pos_right hj (mul_pos hp (by rw [hEi]; exact Real.exp_pos _))
    have h4 : h (t + 1) i * (h t j * E t j) ≤
        h (t + 1) i * (h t j * (Real.exp η * Real.exp (η * a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEj hpj.le) hxi.le
    rw [hEi] at h3 h1
    have h5 : h t i < h (t + 1) i * Real.exp (η * a) := by
      have h6 : h t j * Real.exp η * h t i < h t j * Real.exp η * (h (t + 1) i * Real.exp (η * a)) := by
        linarith
      exact lt_of_mul_lt_mul_left h6 (mul_pos hpj (Real.exp_pos η)).le
    -- e^{ηa} ≤ 1/(1 - ηa) and ηa ≤ εc
    have hηa : η * a ≤ ε * c := by
      have hdiff : ε * c - η * a = ε ^ 2 * η / (8 * N) := by
        rw [ha]; show ε * (ε * η / (4 * (N : ℝ))) - η * (ε ^ 2 / (8 * N)) = _; ring
      have : 0 ≤ ε ^ 2 * η / (8 * (N : ℝ)) := by positivity
      linarith
    have hexp : Real.exp (-(η * a)) * Real.exp (η * a) = 1 := by rw [← Real.exp_add]; simp
    have h7 : 1 - η * a ≤ Real.exp (-(η * a)) := by linarith [Real.add_one_le_exp (-(η * a))]
    -- x_i ≥ h_i e^{-ηa} ≥ h_i (1 - ηa) ≥ h_i (1 - εc)
    have h8 : h t i * Real.exp (-(η * a)) < h (t + 1) i := by
      have := mul_lt_mul_of_pos_right h5 (Real.exp_pos (-(η * a)))
      have e : h (t + 1) i * Real.exp (η * a) * Real.exp (-(η * a)) = h (t + 1) i := by
        rw [mul_assoc, ← Real.exp_add]; simp
      linarith
    have h9 : h t i * (1 - ε * c) ≤ h t i * Real.exp (-(η * a)) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      linarith
    linarith
