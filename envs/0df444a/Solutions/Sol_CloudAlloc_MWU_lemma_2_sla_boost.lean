-- Prove2me | solution 1 for CloudAlloc.MWU.lemma_2_sla_boost
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:14:50.867862+00:00
-- url     : https://prove2.me/submissions/652e901b-fe6e-4863-8bae-f8cec2725ae2

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run

namespace Aux_CA_sla2

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

end Aux_CA_sla2

set_option maxHeartbeats 1600000 in
open CloudAlloc.MWU Aux_CA_sla2 in
theorem solution {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, 2 * ε / N ≤ β j) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let lam := ε ^ 2 / (8 * (N : ℝ))
    let c' := ε * η * lam / (2 * (N : ℝ))
    ∀ t i, 0 < queue h L t i → h t i < β i → h t i * (1 + c') ≤ h (t + 1) i := by
  intro lam c' t i hq hlt
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hfl : 0 < ε / N := div_pos hε hNpos
  have hmem := mem_trunc hrun
  have hlow : ∀ t k, ε / N ≤ h t k := fun t k => (hmem t).2 k
  have hsum1 : ∀ t, ∑ k, h t k = 1 := fun t => (hmem t).1
  have hpos : ∀ t k, 0 < h t k := fun t k => lt_of_lt_of_le hfl (hlow t k)
  have hlam_eq : lam = ε ^ 2 / (8 * (N : ℝ)) := rfl
  have hlampos : 0 < lam := by rw [hlam_eq]; exact div_pos (pow_pos hε 2) (by linarith)
  have hlam0 : 0 ≤ lam := hlampos.le
  have hc0 : 0 ≤ c' := by
    show 0 ≤ ε * η * lam / (2 * (N : ℝ))
    exact div_nonneg (mul_nonneg (mul_nonneg hε.le hη.le) hlam0) (by linarith)
  have hβ2 : ∀ j, 2 * (ε / N) ≤ β j := by
    intro j; have := hβ j; rw [mul_div_assoc] at this; exact this
  set u := ε / N with hu
  have hu1 : u ≤ 1 / 20 := by rw [hu, div_le_iff₀ hNpos]; linarith
  -- weights
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
    exact e
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
    show ε * η * lam / (2 * (N : ℝ)) = η * lam * (ε / N) / 2; ring
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
      have : η ≤ η * (1 + lam) := by linarith
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
  have hμhalf : 1 / 2 ≤ μ := by
    rw [hμ]
    have := Real.add_one_le_exp (-(η * lam))
    have h1 : 1 / 2 ≤ Real.exp (-(η * lam)) := by linarith
    have := mul_le_mul (show (1 : ℝ) ≤ 1 + c' by linarith) h1 (by norm_num) hc1
    linarith
  -- (1 - μ) u is larger than c'
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
  -- per-coordinate bounds
  have hbound : ∀ j, h (t + 1) j ≤ (if 0 < queue h L t j then
      (if h t j < β j then (1 + c') * h t j else μ * h t j) else κ * h t j + (1 - κ) * u) := by
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
      · have h2 : 2 * u ≤ h t j := le_trans (hβ2 j) hbj'
        have := mul_le_mul hμhalf h2 (by linarith) (by linarith)
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
      · have := mul_nonneg hκ0 (sub_nonneg.mpr (hlow t j))
        linarith
      · rw [hEj, mul_one] at h1
        have : 0 ≤ (1 - κ) * u := mul_nonneg (by linarith) hfl.le
        linarith
  -- summation
  have htot : (1 : ℝ) ≤ ∑ j, (if 0 < queue h L t j then
      (if h t j < β j then (1 + c') * h t j else μ * h t j) else κ * h t j + (1 - κ) * u) := by
    calc (1 : ℝ) = ∑ j, h (t + 1) j := (hsum1 (t + 1)).symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hbound j)
  rw [Finset.sum_ite, Finset.sum_ite] at htot
  set Bs := Finset.univ.filter (fun j => 0 < queue h L t j) with hBs
  set Is := Finset.univ.filter (fun j => ¬ 0 < queue h L t j) with hIs
  set G1 := Bs.filter (fun j => h t j < β j) with hG1
  set G2 := Bs.filter (fun j => ¬ h t j < β j) with hG2
  have e1 : ∑ j ∈ G1, (1 + c') * h t j = (1 + c') * ∑ j ∈ G1, h t j := by rw [Finset.mul_sum]
  have e2 : ∑ j ∈ G2, μ * h t j = μ * ∑ j ∈ G2, h t j := by rw [Finset.mul_sum]
  have e3 : ∑ j ∈ Is, (κ * h t j + (1 - κ) * u) =
      κ * ∑ j ∈ Is, h t j + Is.card * ((1 - κ) * u) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
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
  have hG2β : (G2.card : ℝ) * (2 * u) ≤ ∑ j ∈ G2, β j := by
    have := Finset.card_nsmul_le_sum G2 β (2 * u) (fun j _ => hβ2 j)
    rwa [nsmul_eq_mul] at this
  have hIβ : (Is.card : ℝ) * (2 * u) ≤ ∑ j ∈ Is, β j := by
    have := Finset.card_nsmul_le_sum Is β (2 * u) (fun j _ => hβ2 j)
    rwa [nsmul_eq_mul] at this
  have hIh : (Is.card : ℝ) * u ≤ ∑ j ∈ Is, h t j := by
    have := Finset.card_nsmul_le_sum Is (h t) u (fun j _ => hlow t j)
    rwa [nsmul_eq_mul] at this
  have hS1le : ∑ j ∈ G1, h t j ≤ 1 := by
    have : 0 ≤ ∑ j ∈ G2, h t j := Finset.sum_nonneg (fun j _ => (hpos t j).le)
    have : 0 ≤ ∑ j ∈ Is, h t j := Finset.sum_nonneg (fun j _ => (hpos t j).le)
    linarith
  have hkey : (1 - μ) * ∑ j ∈ G2, h t j + (1 - κ) * (∑ j ∈ Is, h t j - Is.card * u) ≤
      c' * ∑ j ∈ G1, h t j := by
    linarith
  have hlarge : 2 * ((G2.card : ℝ) + Is.card) * u < ∑ j ∈ G2, h t j + ∑ j ∈ Is, h t j := by
    linarith
  by_cases hcard : G2.card + Is.card = 0
  · have h2 : G2.card = 0 := by omega
    have h3 : Is.card = 0 := by omega
    rw [Finset.card_eq_zero] at h2 h3
    simp [h2, h3] at hlarge
  · have hcR : (1 : ℝ) ≤ (G2.card : ℝ) + Is.card := by
      have : 1 ≤ G2.card + Is.card := by omega
      exact_mod_cast this
    have hlow2 : u ≤ ∑ j ∈ G2, h t j + ∑ j ∈ Is, h t j - Is.card * u := by
      have hA : (Is.card : ℝ) * u ≤ ((G2.card : ℝ) + Is.card) * u :=
        mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) G2.card]) hfl.le
      have hB : 1 * u ≤ ((G2.card : ℝ) + Is.card) * u := mul_le_mul_of_nonneg_right hcR hfl.le
      linarith
    have hδ : (1 - μ) * (∑ j ∈ G2, h t j + ∑ j ∈ Is, h t j - Is.card * u) ≤
        (1 - μ) * ∑ j ∈ G2, h t j + (1 - κ) * (∑ j ∈ Is, h t j - Is.card * u) := by
      have : 0 ≤ ∑ j ∈ Is, h t j - Is.card * u := by linarith
      have := mul_le_mul_of_nonneg_right (show 1 - μ ≤ 1 - κ by linarith) this
      linarith
    have h4 := mul_le_mul_of_nonneg_left hlow2 hμ1
    have h5 : c' * ∑ j ∈ G1, h t j ≤ c' := by
      have := mul_le_mul_of_nonneg_left hS1le hc0
      linarith
    linarith
