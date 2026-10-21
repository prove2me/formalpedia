-- Prove2me | solution 1 for CloudMWU.Bicriteria.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:58:31.623118+00:00
-- url     : https://prove2.me/submissions/8eb9f46c-1361-4a46-a47d-81df6f0322fe

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

theorem cmw_num1 (c ε u Ea Em M : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (hu : 0 < u) (hEa1 : 1 ≤ Ea) (hEa2 : Ea ≤ 1 + ε * c)
    (hEm1 : Em ≤ 1) (hgap : 3 * c ≤ (1 - Em) * u) (hM0 : 0 ≤ M) (hM1 : M ≤ 1) :
    (1 + c) * (Ea * M - (Ea - Em) * u) ≤ M := by
  have hx : 0 ≤ (1 + c) * Ea - 1 := by nlinarith
  have hA1 : ((1 + c) * Ea - 1) * M ≤ ((1 + c) * Ea - 1) * 1 := mul_le_mul_of_nonneg_left hM1 hx
  have hA2 : (1 - Em) * u ≤ (Ea - Em) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  have hA2' : 0 ≤ (Ea - Em) * u := by nlinarith
  have hA3 : (Ea - Em) * u ≤ (1 + c) * ((Ea - Em) * u) := by nlinarith
  have hA4 : (1 + c) * Ea ≤ (1 + c) * (1 + ε * c) := mul_le_mul_of_nonneg_left hEa2 (by linarith)
  have hA5 : (1 + c) * (1 + ε * c) - 1 ≤ 3 * c := by
    have : ε * c ≤ c / 10 := by nlinarith
    have : c * (ε * c) ≤ c / 10 := by nlinarith
    nlinarith
  nlinarith

theorem cmw_num2 (c ε u Ea : ℝ) (hc0 : 0 < c) (hc1 : c ≤ u / 12) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (hu : 0 < u) (hu1 : u ≤ 1) (hEa2 : Ea ≤ 1 + ε * c) :
    (1 + c) * Ea * (1 - ε) ≤ 1 - ε + u := by
  have h1 : (1 + c) * Ea * (1 - ε) ≤ (1 + c) * (1 + ε * c) * (1 - ε) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hEa2 (by linarith)
  have hc1' : c ≤ 1 := by linarith
  have h2 : (1 + c) * (1 + ε * c) * (1 - ε) ≤ 1 - ε + 2 * c := by
    have : ε * c ≤ c / 10 := by nlinarith
    have : c * (ε * c) ≤ c / 10 := by nlinarith
    have e : (1 + c) * (1 + ε * c) * (1 - ε) = (1 - ε) + (1 - ε) * (c + ε * c + c * (ε * c)) := by ring
    rw [e]
    have : 0 ≤ c + ε * c + c * (ε * c) := by positivity
    nlinarith
  linarith

theorem cmw_gap (η u : ℝ) (hη : 0 < η) (hη' : η < 1 / 3) (hu : 0 < u) :
    3 * (η * u / 4) ≤ (1 - Real.exp (-η)) * u := by
  have hEm : Real.exp (-η) * Real.exp η = 1 := by rw [← Real.exp_add]; simp
  have he := Real.add_one_le_exp η
  have hEm0 := Real.exp_pos (-η)
  have h1 : Real.exp (-η) * (1 + η) ≤ 1 := by nlinarith
  have h2 : 3 / 4 * η ≤ 1 - Real.exp (-η) := by nlinarith
  nlinarith

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    (∑ j ∈ active h L t, h t j ≤ 1 - ε →
      ∀ i ∈ active h L t, h t i * (1 + cLem1 N ε η) ≤ h (t + 1) i) ∧
    (∀ i ∈ active h L t, h t i < β i → h t i ≤ h (t + 1) i) ∧
    (∀ i ∈ active h L t, β i ≤ h t i → h t i * (1 - ε * cLem1 N ε η) ≤ h (t + 1) i) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεN : 0 < ε / (N : ℝ) := by positivity
  obtain ⟨hHsum, hHfl⟩ := cmw_simplex ε η β L h hrun t
  have hH0 : ∀ k, 0 ≤ h t k := fun k => le_trans hεN.le (hHfl k)
  obtain ⟨S, hS, hY, hScx, hM, hcard, hlb⟩ := cmw_proj_lb N hN ε hε hε' _ _ (hrun.2 t)
  set y := boosted ε η β (h t) (runQueue h L t) with hy_def
  set M := 1 - ε / (N : ℝ) * (S.card : ℝ) with hM_def
  set Y := ∑ j ∈ Sᶜ, y j with hY_def
  set A := active h L t with hA_def
  set c := cLem1 N ε η with hc_def
  set E1 := Real.exp η with hE1
  set Ea := Real.exp (lam N ε * η) with hEa
  have hlam : lam N ε = ε ^ 2 / (8 * (N : ℝ)) := rfl
  have hc : c = ε * η / (4 * (N : ℝ)) := rfl
  have hc' : c = η * (ε / (N : ℝ)) / 4 := by rw [hc]; field_simp
  have hlamη : lam N ε * η = ε * c / 2 := by rw [hlam, hc]; field_simp; ring
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ ε / (N : ℝ) / 12 := by
    rw [hc']; have := hεN; nlinarith
  have hεN1 : ε / (N : ℝ) ≤ 1 / 20 := by
    rw [div_le_iff₀ hNpos]; nlinarith
  have hlam0 : 0 ≤ lam N ε * η := by rw [hlamη]; positivity
  have hEa1 : 1 ≤ Ea := Real.one_le_exp hlam0
  have hEa2 : Ea ≤ 1 + ε * c := by
    have hh : lam N ε * η ≤ 1 / 2 := by
      rw [hlamη]; have : ε * c ≤ 1 / 10 * (1 / 240) := by
        apply mul_le_mul hε' (by linarith) hc0.le (by norm_num)
      linarith
    have := cmw_exp_le (lam N ε * η) hlam0 hh
    rw [hEa]; rw [hlamη] at this ⊢; linarith
  have hE1pos : 0 < E1 := Real.exp_pos η
  have hexp_split : Real.exp (η * (1 + lam N ε)) = E1 * Ea := by
    rw [hE1, hEa, ← Real.exp_add]; ring_nf
  have hlampos : 0 ≤ lam N ε := by rw [hlam]; positivity
  -- description of y
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
  have hy_act : ∀ k ∈ A, h t k * E1 ≤ y k := by
    intro k hk
    have hk' : 0 < runQueue h L t k := (Finset.mem_filter.mp hk).2
    rw [hy_eq]
    apply mul_le_mul_of_nonneg_left _ (hH0 k)
    apply Real.exp_le_exp.mpr
    unfold gain
    rw [if_pos hk']
    split_ifs
    · have := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1 + lam N ε) hη.le
      linarith
    · linarith
  have hy_A1 : ∀ k ∈ A, h t k < β k → y k = h t k * (E1 * Ea) := by
    intro k hk hkb
    have hk' : 0 < runQueue h L t k := (Finset.mem_filter.mp hk).2
    rw [hy_eq, ← hexp_split]
    unfold gain
    rw [if_pos hk', if_pos hkb]
  have hy_B : ∀ k, k ∉ A → y k = h t k := by
    intro k hk
    have hk' : ¬ 0 < runQueue h L t k := by
      intro hh; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    rw [hy_eq]
    unfold gain
    rw [if_neg hk']; simp
  -- mass of the complement of S
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
  have hlb' : ∀ k, y k * M / Y ≤ h (t + 1) k := by
    intro k; have := hlb k; rw [mul_div_assoc]; exact this
  have hEm : Real.exp (-η) * E1 = 1 := by rw [hE1, ← Real.exp_add]; simp
  have hEm0 : 0 < Real.exp (-η) := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    intro hlow i hi
    have hHi := hH0 i
    suffices hsuff : (1 + c) * Y ≤ E1 * M by
      have h1 := hlb' i
      have h2 := hy_act i hi
      have h3 : h t i * (1 + c) ≤ h t i * E1 * M / Y := by
        rw [le_div_iff₀ hY]
        have := mul_le_mul_of_nonneg_left hsuff hHi
        linarith
      have h4 : h t i * E1 * M / Y ≤ y i * M / Y := by
        apply div_le_div_of_nonneg_right _ hY.le
        exact mul_le_mul_of_nonneg_right h2 hM.le
      linarith
    by_cases hcase : ∃ j ∈ Sᶜ, j ∉ A
    · obtain ⟨j, hjS, hjA⟩ := hcase
      set D := ∑ k ∈ Sᶜ, h t k with hD
      set b := ∑ k ∈ Sᶜ.filter (fun k => k ∉ A), h t k with hb
      set DA := ∑ k ∈ Sᶜ.filter (fun k => k ∈ A), h t k with hDA
      have hbj : ε / (N : ℝ) ≤ b := by
        have : h t j ≤ b := Finset.single_le_sum (f := h t) (fun k _ => hH0 k)
          (Finset.mem_filter.mpr ⟨hjS, hjA⟩)
        linarith [hHfl j]
      have hYsplit : Y = ∑ k ∈ Sᶜ.filter (fun k => k ∈ A), y k
          + ∑ k ∈ Sᶜ.filter (fun k => k ∉ A), y k :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hDsplit : D = DA + b := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hYA := hsumY (Sᶜ.filter (fun k => k ∈ A))
      have hYB : ∑ k ∈ Sᶜ.filter (fun k => k ∉ A), y k = b := by
        rw [hb]; apply Finset.sum_congr rfl
        intro k hk; exact hy_B k (Finset.mem_filter.mp hk).2
      have hY2 : Y ≤ E1 * Ea * DA + b := by
        rw [hYsplit, hYB]; linarith
      have hY3 : Real.exp (-η) * Y ≤ Ea * DA + Real.exp (-η) * b := by
        have := mul_le_mul_of_nonneg_left hY2 hEm0.le
        have e : Real.exp (-η) * (E1 * Ea * DA + b) = Ea * DA + Real.exp (-η) * b := by
          have : Real.exp (-η) * (E1 * Ea * DA) = (Real.exp (-η) * E1) * Ea * DA := by ring
          rw [mul_add, this, hEm]; ring
        linarith
      have hEm1 : Real.exp (-η) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have hY4 : Ea * DA + Real.exp (-η) * b
          ≤ Ea * M - (Ea - Real.exp (-η)) * (ε / (N : ℝ)) := by
        have p1 := mul_le_mul_of_nonneg_left hDle (by linarith : (0:ℝ) ≤ Ea)
        have p2 := mul_le_mul_of_nonneg_left hbj (by linarith : (0:ℝ) ≤ Ea - Real.exp (-η))
        have e : Ea * DA + Real.exp (-η) * b = Ea * D - (Ea - Real.exp (-η)) * b := by
          rw [hDsplit]; ring
        rw [e]; linarith
      have hgap := cmw_gap η (ε / (N : ℝ)) hη hη' hεN
      rw [← hc'] at hgap
      have key := cmw_num1 c ε (ε / (N : ℝ)) Ea (Real.exp (-η)) M hc0 (by linarith) hε hε'
        hεN hEa1 hEa2 hEm1 hgap hM.le hM1
      have hfin : (1 + c) * (Real.exp (-η) * Y) ≤ M := by
        have := mul_le_mul_of_nonneg_left (le_trans hY3 hY4) (by linarith : (0:ℝ) ≤ 1 + c)
        linarith
      have e : (1 + c) * Y = E1 * ((1 + c) * (Real.exp (-η) * Y)) := by
        have : E1 * ((1 + c) * (Real.exp (-η) * Y)) = (1 + c) * (Real.exp (-η) * E1) * Y := by
          ring
        rw [this, hEm]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hfin hE1pos.le
    · push_neg at hcase
      have hDA : ∑ k ∈ Sᶜ, h t k ≤ ∑ j ∈ A, h t j :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => hcase k hk) (fun k _ _ => hH0 k)
      have hY2 : Y ≤ E1 * Ea * (1 - ε) := by
        have := hsumY Sᶜ
        have h2 : (E1 * Ea) * ∑ k ∈ Sᶜ, h t k ≤ (E1 * Ea) * (1 - ε) :=
          mul_le_mul_of_nonneg_left (le_trans hDA hlow) (by positivity)
        linarith
      have hMlow : 1 - ε + ε / (N : ℝ) ≤ M := by
        rw [hM_def]
        have : ε / (N : ℝ) * (S.card : ℝ) ≤ ε / (N : ℝ) * ((N : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hcard hεN.le
        have e : ε / (N : ℝ) * ((N : ℝ) - 1) = ε - ε / (N : ℝ) := by field_simp
        linarith
      have key := cmw_num2 c ε (ε / (N : ℝ)) Ea hc0 hc1 hε hε' hεN (by linarith) hEa2
      calc (1 + c) * Y ≤ (1 + c) * (E1 * Ea * (1 - ε)) :=
            mul_le_mul_of_nonneg_left hY2 (by linarith)
        _ = E1 * ((1 + c) * Ea * (1 - ε)) := by ring
        _ ≤ E1 * M := mul_le_mul_of_nonneg_left (le_trans key hMlow) hE1pos.le
  · -- part 2
    intro i hi hib
    have h1 := hlb' i
    rw [hy_A1 i hi hib] at h1
    have h2 : h t i ≤ h t i * (E1 * Ea) * M / Y := by
      rw [le_div_iff₀ hY]
      have := mul_le_mul_of_nonneg_left hYle (hH0 i)
      have e : h t i * (E1 * Ea) * M = h t i * (E1 * Ea * M) := by ring
      rw [e]; linarith
    linarith
  · -- part 3
    intro i hi _
    have h1 := hlb' i
    have h2 := hy_act i hi
    have hHi := hH0 i
    have hεc : ε * c ≤ 1 / 100 := by
      have : ε * c ≤ 1 / 10 * (1 / 240) := by
        apply mul_le_mul hε' (by linarith) hc0.le (by norm_num)
      linarith
    have hk : (1 - ε * c) * Ea ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hEa2 (by linarith : (0:ℝ) ≤ 1 - ε * c)
      nlinarith
    have hpos1 : 0 ≤ 1 - ε * c := by linarith
    have hk2 : (1 - ε * c) * Y ≤ E1 * M := by
      calc (1 - ε * c) * Y ≤ (1 - ε * c) * (E1 * Ea * M) := mul_le_mul_of_nonneg_left hYle hpos1
        _ = E1 * M * ((1 - ε * c) * Ea) := by ring
        _ ≤ E1 * M * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
        _ = E1 * M := by ring
    have h3 : h t i * (1 - ε * c) ≤ h t i * E1 * M / Y := by
      rw [le_div_iff₀ hY]
      have := mul_le_mul_of_nonneg_left hk2 hHi
      have e1 : h t i * (1 - ε * c) * Y = h t i * ((1 - ε * c) * Y) := by ring
      have e2 : h t i * E1 * M = h t i * (E1 * M) := by ring
      rw [e1, e2]; exact this
    have h4 : h t i * E1 * M / Y ≤ y i * M / Y := by
      apply div_le_div_of_nonneg_right _ hY.le
      exact mul_le_mul_of_nonneg_right h2 hM.le
    linarith
