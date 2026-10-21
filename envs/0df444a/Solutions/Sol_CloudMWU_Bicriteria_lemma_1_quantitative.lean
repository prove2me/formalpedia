-- Prove2me | solution 1 for CloudMWU.Bicriteria.lemma_1_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:11:45.729613+00:00
-- url     : https://prove2.me/submissions/51ccbc93-1680-4096-b2e7-068eabf01a56

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

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    ∀ i ∈ active h L t,
      h t i ≤ h (t + 1) i * (Real.exp (lam N ε * η)
        - (Real.exp (lam N ε * η) - Real.exp (-η))
          * (∑ j ∈ (active h L t)ᶜ, h t j - Real.exp (η * (1 + lam N ε)) * ε)) := by
  intro i hi
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
  set Em := Real.exp (-η) with hEm_def
  have hlam : lam N ε = ε ^ 2 / (8 * (N : ℝ)) := rfl
  have hlampos : 0 ≤ lam N ε := by rw [hlam]; positivity
  have hlam0 : 0 ≤ lam N ε * η := by positivity
  have hEa1 : 1 ≤ Ea := Real.one_le_exp hlam0
  have hE1pos : 0 < E1 := Real.exp_pos η
  have hEm0 : 0 < Em := Real.exp_pos _
  have hEm1 : Em ≤ 1 := by rw [hEm_def, Real.exp_le_one_iff]; linarith
  have hEm : Em * E1 = 1 := by rw [hEm_def, hE1, ← Real.exp_add]; simp
  have hexp_split : Real.exp (η * (1 + lam N ε)) = E1 * Ea := by
    rw [hE1, hEa, ← Real.exp_add]; ring_nf
  rw [hexp_split]
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
  have hy_B : ∀ k, k ∉ A → y k = h t k := by
    intro k hk
    have hk' : ¬ 0 < runQueue h L t k := by
      intro hh; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    rw [hy_eq]
    unfold gain
    rw [if_neg hk']; simp
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
  -- users in S had small allocation
  have hSsmall : ∀ j ∈ S, h t j ≤ ε / (N : ℝ) * (E1 * Ea) := by
    intro j hjS
    have hx := hS j hjS
    have h1 := hlb j
    rw [hx] at h1
    have h2 : h t j * (M / Y) ≤ ε / (N : ℝ) := le_trans (mul_le_mul_of_nonneg_right (hy_ge j)
      (by positivity)) h1
    have h3 : h t j * M ≤ ε / (N : ℝ) * Y := by
      rw [mul_div_assoc', div_le_iff₀ hY] at h2; exact h2
    have h4 : ε / (N : ℝ) * Y ≤ ε / (N : ℝ) * (E1 * Ea * M) :=
      mul_le_mul_of_nonneg_left hYle hεN.le
    have : h t j * M ≤ (ε / (N : ℝ) * (E1 * Ea)) * M := by
      have e : ε / (N : ℝ) * (E1 * Ea * M) = (ε / (N : ℝ) * (E1 * Ea)) * M := by ring
      linarith
    exact le_of_mul_le_mul_right this hM
  -- decompose
  set DA := ∑ k ∈ Sᶜ.filter (fun k => k ∈ A), h t k with hDA
  set b' := ∑ k ∈ Sᶜ.filter (fun k => k ∉ A), h t k with hb'
  set b := ∑ j ∈ Aᶜ, h t j with hb
  have hDsplit : ∑ k ∈ Sᶜ, h t k = DA + b' := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hYsplit : Y = ∑ k ∈ Sᶜ.filter (fun k => k ∈ A), y k
      + ∑ k ∈ Sᶜ.filter (fun k => k ∉ A), y k := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hYA := hsumY (Sᶜ.filter (fun k => k ∈ A))
  have hYB : ∑ k ∈ Sᶜ.filter (fun k => k ∉ A), y k = b' := by
    rw [hb']; apply Finset.sum_congr rfl
    intro k hk; exact hy_B k (Finset.mem_filter.mp hk).2
  have hb'0 : 0 ≤ b' := Finset.sum_nonneg (fun k _ => hH0 k)
  have hbsplit : b = ∑ k ∈ Aᶜ.filter (fun k => k ∈ S), h t k
      + ∑ k ∈ Aᶜ.filter (fun k => k ∉ S), h t k := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsets : Aᶜ.filter (fun k => k ∉ S) = Sᶜ.filter (fun k => k ∉ A) := by
    ext k; simp [and_comm]
  have hbS : ∑ k ∈ Aᶜ.filter (fun k => k ∈ S), h t k ≤ E1 * Ea * ε := by
    have h1 := Finset.sum_le_card_nsmul (Aᶜ.filter (fun k => k ∈ S)) (h t)
      (ε / (N : ℝ) * (E1 * Ea)) (fun k hk => hSsmall k (Finset.mem_filter.mp hk).2)
    rw [nsmul_eq_mul] at h1
    have hc : ((Aᶜ.filter (fun k => k ∈ S)).card : ℝ) ≤ N := by
      have := Finset.card_le_univ (Aᶜ.filter (fun k => k ∈ S))
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have h2 : ((Aᶜ.filter (fun k => k ∈ S)).card : ℝ) * (ε / (N : ℝ) * (E1 * Ea))
        ≤ (N : ℝ) * (ε / (N : ℝ) * (E1 * Ea)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    have e : (N : ℝ) * (ε / (N : ℝ) * (E1 * Ea)) = E1 * Ea * ε := by field_simp
    linarith
  have hb'b : b - E1 * Ea * ε ≤ b' := by
    rw [hbsplit, hsets] at *
    linarith
  -- main inequality: Em * Y ≤ Z * M
  set Z := Ea - (Ea - Em) * (b - E1 * Ea * ε) with hZ
  have hk0 : 0 ≤ Ea - Em := by linarith
  have hEmY : Em * Y ≤ Ea * DA + Em * b' := by
    have hY2 : Y ≤ E1 * Ea * DA + b' := by rw [hYsplit, hYB]; linarith
    have := mul_le_mul_of_nonneg_left hY2 hEm0.le
    have e : Em * (E1 * Ea * DA + b') = Ea * DA + Em * b' := by
      have : Em * (E1 * Ea * DA) = (Em * E1) * Ea * DA := by ring
      rw [mul_add, this, hEm]; ring
    linarith
  have hb'M : (b - E1 * Ea * ε) * M ≤ b' := by
    rcases le_or_gt (b - E1 * Ea * ε) 0 with hneg | hpos'
    · have : (b - E1 * Ea * ε) * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hM.le
      linarith
    · have : (b - E1 * Ea * ε) * M ≤ (b - E1 * Ea * ε) * 1 := mul_le_mul_of_nonneg_left hM1 hpos'.le
      linarith
  have hmain : Em * Y ≤ Z * M := by
    have p1 : Ea * DA + Em * b' = Ea * (DA + b') - (Ea - Em) * b' := by ring
    have p2 : Ea * (DA + b') ≤ Ea * M := by
      rw [← hDsplit]; exact mul_le_mul_of_nonneg_left hDle (by linarith)
    have p3 : (Ea - Em) * ((b - E1 * Ea * ε) * M) ≤ (Ea - Em) * b' :=
      mul_le_mul_of_nonneg_left hb'M hk0
    have e : Z * M = Ea * M - (Ea - Em) * ((b - E1 * Ea * ε) * M) := by rw [hZ]; ring
    rw [e]; linarith
  -- conclude
  have h1 := hlb i
  have h2 := hy_act i hi
  have hxi : h t i * E1 * (M / Y) ≤ h (t + 1) i := by
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ M / Y)
    linarith
  have hZ' : Em * Y / M ≤ Z := by rw [div_le_iff₀ hM]; exact hmain
  have hEmYM : 0 ≤ Em * Y / M := by positivity
  have hx0 : 0 ≤ h t i * E1 * (M / Y) := by have := hH0 i; positivity
  calc h t i = h t i * E1 * (M / Y) * (Em * Y / M) := by
        field_simp
        have : E1 * Em = 1 := by rw [mul_comm]; exact hEm
        rw [mul_assoc, this, mul_one]
    _ ≤ h (t + 1) i * Z := mul_le_mul hxi hZ' hEmYM (le_trans hx0 hxi)
