-- Prove2me | solution 1 for CloudMWU.Bicriteria.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:03:35.374986+00:00
-- url     : https://prove2.me/submissions/360e3df5-6615-44ed-9d3a-b7932344f814

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model
import Theorems.Thm_CloudMWU_Bicriteria_proposition_1b

open Finset CloudMWU.Bicriteria

theorem cmw_simplex {N : ℕ} (ε η : ℝ) (β : Fin N → ℝ) (L h : ℕ → Fin N → ℝ)
    (hrun : IsAlg1Run ε η β L h) (t : ℕ) : h t ∈ truncSimplex N ε := by
  cases t with
  | zero => exact hrun.1
  | succ t => exact (hrun.2 t).2.1

theorem cmw_exp_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Real.exp x ≤ 1 + 2 * x := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos x
  nlinarith

/-- lower bound coming from Proposition 1(b): `h_{t+1}(k) ≥ y(k) · C`. -/
theorem cmw_proj_lb (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (y x : Fin N → ℝ) (hx : IsKLProj ε y x) :
    ∃ S : Finset (Fin N), (∀ j ∈ S, x j = ε / (N : ℝ)) ∧
      0 < ∑ j ∈ Sᶜ, y j ∧
      ∑ j ∈ Sᶜ, x j = 1 - ε / (N : ℝ) * (S.card : ℝ) ∧
      0 < 1 - ε / (N : ℝ) * (S.card : ℝ) ∧
      (S.card : ℝ) ≤ (N : ℝ) - 1 ∧
      ∀ k, y k * ((1 - ε / (N : ℝ) * (S.card : ℝ)) / ∑ j ∈ Sᶜ, y j) ≤ x k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεN : 0 < ε / (N : ℝ) := by positivity
  have hy := hx.1
  obtain ⟨μ, hμ0, _, hμx⟩ := proposition_1b N hN ε hε hε' y hy x hx
  obtain ⟨_, ⟨hsum, hfl⟩, _⟩ := hx
  set S := univ.filter (fun j => x j = ε / (N : ℝ)) with hS
  have hSc : Sᶜ = univ.filter (fun j => x j ≠ ε / (N : ℝ)) := by
    ext j; simp [hS]
  have hxpos : ∀ k, 0 < x k := fun k => lt_of_lt_of_le hεN (hfl k)
  have hSsum : ∑ k ∈ S, x k = ε / (N : ℝ) * (S.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.mp hk).2)]
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hScsum : ∑ j ∈ Sᶜ, x j = 1 - ε / (N : ℝ) * (S.card : ℝ) := by
    have := Finset.sum_add_sum_compl S x
    linarith
  have hScne : Sᶜ.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hSu : S = univ := by
      rw [← compl_compl S, hne, compl_empty]
    have : ∑ k, x k = ε := by
      have h1 : ∑ k, x k = ∑ k ∈ S, x k := by rw [hSu]
      rw [h1, hSsum, hSu, Finset.card_univ, Fintype.card_fin]
      field_simp
    linarith
  have hMpos : 0 < 1 - ε / (N : ℝ) * (S.card : ℝ) := by
    rw [← hScsum]; exact Finset.sum_pos (fun k _ => hxpos k) hScne
  have hYpos : 0 < ∑ j ∈ Sᶜ, y j := Finset.sum_pos (fun k _ => hy k) hScne
  have hcard : (S.card : ℝ) ≤ (N : ℝ) - 1 := by
    have h1 : S.card + Sᶜ.card = N := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    have h2 : 1 ≤ Sᶜ.card := Finset.card_pos.mpr hScne
    have : S.card ≤ N - 1 := by omega
    have h3 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
    rw [← h3]; exact_mod_cast this
  refine ⟨S, fun j hj => (Finset.mem_filter.mp hj).2, hYpos, hScsum, hMpos, hcard, ?_⟩
  intro k
  have hC : 0 ≤ (1 - ε / (N : ℝ) * (S.card : ℝ)) / ∑ j ∈ Sᶜ, y j := by positivity
  have hk := hμx k
  rw [← hSc] at hk
  rw [hk]
  have he : 1 ≤ Real.exp (μ k) := Real.one_le_exp (hμ0 k)
  have hyk := (hy k).le
  calc y k * ((1 - ε / (N : ℝ) * (S.card : ℝ)) / ∑ j ∈ Sᶜ, y j)
      = y k * 1 * ((1 - ε / (N : ℝ) * (S.card : ℝ)) / ∑ j ∈ Sᶜ, y j) := by ring
    _ ≤ y k * Real.exp (μ k) * ((1 - ε / (N : ℝ) * (S.card : ℝ)) / ∑ j ∈ Sᶜ, y j) := by
        gcongr

theorem cmw_num3 (x u Ea M c' : ℝ) (hc' : c' = x * u / 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hEa1 : 1 + x ≤ Ea) (hEa2 : Ea ≤ 1 + 2 * x) (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hu : 0 < u) :
    (1 + c') * (Ea * M - (Ea - 1) * u) ≤ Ea * M := by
  have hc0 : 0 ≤ c' := by rw [hc']; positivity
  have h1 : c' * (Ea * M) ≤ c' * Ea := by
    have : Ea * M ≤ Ea * 1 := mul_le_mul_of_nonneg_left hM1 (by linarith)
    nlinarith
  have h2 : c' * Ea ≤ x * u := by
    have : c' * Ea ≤ c' * (1 + 2 * x) := mul_le_mul_of_nonneg_left hEa2 hc0
    have : c' * (1 + 2 * x) ≤ 2 * c' := by nlinarith
    rw [hc'] at *; linarith
  have h3 : x * u ≤ (Ea - 1) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  have h4 : 0 ≤ (Ea - 1) * u := by nlinarith
  have h5 : (Ea - 1) * u ≤ (1 + c') * ((Ea - 1) * u) := by nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
theorem cmw_lemma2_core (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j)
    (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    ∀ i ∈ active h L t, h t i < β i → h t i * (1 + cLem2 N ε η) ≤ h (t + 1) i := by
  intro i hi hib
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεN : 0 < ε / (N : ℝ) := by positivity
  obtain ⟨hHsum, hHfl⟩ := cmw_simplex ε η β L h hrun t
  have hH0 : ∀ k, 0 ≤ h t k := fun k => le_trans hεN.le (hHfl k)
  obtain ⟨S, hS, hY, hScx, hM, hcard, hlb⟩ := cmw_proj_lb N hN ε hε hε' _ _ (hrun.2 t)
  set y := boosted ε η β (h t) (runQueue h L t) with hy_def
  set M := 1 - ε / (N : ℝ) * (S.card : ℝ) with hM_def
  set Y := ∑ j ∈ Sᶜ, y j with hY_def
  set A := active h L t with hA_def
  set E1 := Real.exp η with hE1
  set Ea := Real.exp (lam N ε * η) with hEa
  have hlam : lam N ε = ε ^ 2 / (8 * (N : ℝ)) := rfl
  have hlampos : 0 ≤ lam N ε := by rw [hlam]; positivity
  have hlam0 : 0 ≤ lam N ε * η := by positivity
  have hlam1 : lam N ε * η ≤ 1 / 2 := by
    have : lam N ε ≤ 1 := by
      rw [hlam, div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hEa1 : 1 + lam N ε * η ≤ Ea := by rw [hEa]; linarith [Real.add_one_le_exp (lam N ε * η)]
  have hEa2 : Ea ≤ 1 + 2 * (lam N ε * η) := cmw_exp_le _ hlam0 hlam1
  have hE1pos : 0 < E1 := Real.exp_pos η
  have hexp_split : Real.exp (η * (1 + lam N ε)) = E1 * Ea := by
    rw [hE1, hEa, ← Real.exp_add]; ring_nf
  have hy_eq : ∀ k, y k = h t k * Real.exp (η * gain N ε β (h t) (runQueue h L t) k) := by
    intro k; rfl
  have hy_le : ∀ k, y k ≤ h t k * (E1 * Ea) := by
    intro k
    rw [hy_eq, ← hexp_split]
    apply mul_le_mul_of_nonneg_left _ (hH0 k)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hη.le
    unfold gain
    split_ifs <;> linarith
  have hy_ge : ∀ k, h t k ≤ y k := by
    intro k
    rw [hy_eq]
    have : 0 ≤ η * gain N ε β (h t) (runQueue h L t) k := by
      apply mul_nonneg hη.le; unfold gain; split_ifs <;> linarith
    have := Real.one_le_exp this
    nlinarith [hH0 k]
  have hy_A2 : ∀ k, ¬ h t k < β k → y k ≤ h t k * E1 := by
    intro k hk
    rw [hy_eq]
    apply mul_le_mul_of_nonneg_left _ (hH0 k)
    apply Real.exp_le_exp.mpr
    unfold gain
    split_ifs <;> linarith
  have hiA : 0 < runQueue h L t i := (Finset.mem_filter.mp hi).2
  have hy_i : y i = h t i * (E1 * Ea) := by
    rw [hy_eq, ← hexp_split]; unfold gain; rw [if_pos hiA, if_pos hib]
  have hSmass : ε / (N : ℝ) * (S.card : ℝ) ≤ ∑ k ∈ S, h t k := by
    have := Finset.card_nsmul_le_sum S (h t) (ε / (N : ℝ)) (fun k _ => hHfl k)
    rw [nsmul_eq_mul] at this; linarith
  have hDle : ∑ k ∈ Sᶜ, h t k ≤ M := by
    have := Finset.sum_add_sum_compl S (h t)
    rw [hM_def]; linarith
  have hM1 : M ≤ 1 := by
    rw [hM_def]; have : 0 ≤ ε / (N : ℝ) * (S.card : ℝ) := by positivity
    linarith
  have hsumY : ∀ B : Finset (Fin N), ∑ k ∈ B, y k ≤ (E1 * Ea) * ∑ k ∈ B, h t k := by
    intro B
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => by have := hy_le k; linarith)
  have hYle : Y ≤ E1 * Ea * M := by
    have := hsumY Sᶜ
    have h2 : (E1 * Ea) * ∑ k ∈ Sᶜ, h t k ≤ (E1 * Ea) * M :=
      mul_le_mul_of_nonneg_left hDle (by positivity)
    linarith
  -- some user above its SLA
  obtain ⟨j, hj⟩ : ∃ j, β j < h t j := by
    by_contra hcon
    push_neg at hcon
    have : ∑ k, h t k < ∑ k, β k :=
      Finset.sum_lt_sum (fun k _ => hcon k) ⟨i, Finset.mem_univ _, hib⟩
    linarith
  -- j ∉ S
  have hjS : j ∈ Sᶜ := by
    rw [Finset.mem_compl]
    intro hjS
    have hx := hS j hjS
    have h1 := hlb j
    rw [hx] at h1
    -- h t j * (M / Y) ≤ ε / N, and M / Y ≥ 1 / (E1 * Ea)
    have h2 : h t j * (M / Y) ≤ ε / (N : ℝ) := le_trans (mul_le_mul_of_nonneg_right (hy_ge j)
      (by positivity)) h1
    have h3 : h t j * M ≤ ε / (N : ℝ) * Y := by
      rw [mul_div_assoc', div_le_iff₀ hY] at h2; exact h2
    have h4 : ε / (N : ℝ) * Y ≤ ε / (N : ℝ) * (E1 * Ea * M) :=
      mul_le_mul_of_nonneg_left hYle hεN.le
    have h5 : h t j ≤ ε / (N : ℝ) * (E1 * Ea) := by
      have : h t j * M ≤ (ε / (N : ℝ) * (E1 * Ea)) * M := by nlinarith
      exact le_of_mul_le_mul_right this hM
    have h6 := hβ j
    rw [hexp_split] at h6
    have : Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) = ε / (N : ℝ) * (E1 * Ea) := by
      rw [hexp_split]; ring
    rw [hexp_split] at this
    linarith
  have hjb : ¬ h t j < β j := by linarith
  -- bound Y
  have hYsplit : Y = y j + ∑ k ∈ Sᶜ.erase j, y k := (Finset.add_sum_erase _ _ hjS).symm
  have hDsplit : ∑ k ∈ Sᶜ, h t k = h t j + ∑ k ∈ Sᶜ.erase j, h t k :=
    (Finset.add_sum_erase _ _ hjS).symm
  have hYb : Y ≤ E1 * (Ea * M - (Ea - 1) * (ε / (N : ℝ))) := by
    have p1 := hsumY (Sᶜ.erase j)
    have p2 := hy_A2 j hjb
    have p3 : E1 * Ea * ∑ k ∈ Sᶜ, h t k ≤ E1 * Ea * M := mul_le_mul_of_nonneg_left hDle (by positivity)
    have p4 : E1 * (Ea - 1) * (ε / (N : ℝ)) ≤ E1 * (Ea - 1) * h t j :=
      mul_le_mul_of_nonneg_left (hHfl j) (by nlinarith)
    have e : E1 * (Ea * M - (Ea - 1) * (ε / (N : ℝ)))
        = E1 * Ea * M - E1 * (Ea - 1) * (ε / (N : ℝ)) := by ring
    rw [e, hYsplit]
    rw [hDsplit] at p3
    have e2 : E1 * Ea * (h t j + ∑ k ∈ Sᶜ.erase j, h t k)
        = E1 * (Ea - 1) * h t j + h t j * E1 + E1 * Ea * ∑ k ∈ Sᶜ.erase j, h t k := by ring
    rw [e2] at p3
    linarith
  have hc' : cLem2 N ε η = (lam N ε * η) * (ε / (N : ℝ)) / 2 := by
    unfold cLem2; field_simp
  have key := cmw_num3 (lam N ε * η) (ε / (N : ℝ)) Ea M (cLem2 N ε η) hc' hlam0 hlam1 hEa1 hEa2
    hM.le hM1 hεN
  have hc0 : 0 ≤ cLem2 N ε η := by rw [hc']; positivity
  -- conclude
  have h1 := hlb i
  rw [hy_i] at h1
  have hfin : (1 + cLem2 N ε η) * Y ≤ E1 * Ea * M := by
    have := mul_le_mul_of_nonneg_left hYb (by linarith : (0:ℝ) ≤ 1 + cLem2 N ε η)
    have e : (1 + cLem2 N ε η) * (E1 * (Ea * M - (Ea - 1) * (ε / (N : ℝ))))
        = E1 * ((1 + cLem2 N ε η) * (Ea * M - (Ea - 1) * (ε / (N : ℝ)))) := by ring
    rw [e] at this
    have h7 := mul_le_mul_of_nonneg_left key hE1pos.le
    have e3 : E1 * (Ea * M) = E1 * Ea * M := by ring
    rw [e3] at h7
    exact le_trans this h7
  have h2 : h t i * (1 + cLem2 N ε η) ≤ h t i * (E1 * Ea) * (M / Y) := by
    rw [← mul_div_assoc, le_div_iff₀ hY]
    have h8 := mul_le_mul_of_nonneg_left hfin (hH0 i)
    have e4 : h t i * (1 + cLem2 N ε η) * Y = h t i * ((1 + cLem2 N ε η) * Y) := by ring
    have e5 : h t i * (E1 * Ea) * M = h t i * (E1 * Ea * M) := by ring
    rw [e4, e5]; exact h8
  linarith

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, 2 * ε / (N : ℝ) ≤ β j) (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    ∀ i ∈ active h L t, h t i < β i → h t i * (1 + cLem2 N ε η) ≤ h (t + 1) i := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j := by
    intro j
    refine lt_of_lt_of_le ?_ (hβ j)
    apply div_lt_div_of_pos_right _ hNpos
    have hlam : lam N ε ≤ 1 / 100 := by
      unfold lam
      rw [div_le_iff₀ (by positivity)]
      have : (2:ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have hlam0 : 0 ≤ lam N ε := by unfold lam; positivity
    have hx : η * (1 + lam N ε) < Real.log 2 := by
      have := Real.log_two_gt_d9
      nlinarith
    have : Real.exp (η * (1 + lam N ε)) < 2 := by
      calc Real.exp (η * (1 + lam N ε)) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hx
        _ = 2 := Real.exp_log (by norm_num)
    nlinarith
  exact cmw_lemma2_core N hN ε η hε hε' hη hη' β hexp hβsum L h hrun t
