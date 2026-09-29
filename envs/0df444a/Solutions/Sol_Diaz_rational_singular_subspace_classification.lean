-- Prove2me | solution 1 for Diaz.rational_singular_subspace_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:10:12.960743+00:00
-- url     : https://prove2.me/submissions/b04197c2-516e-4e9e-90bb-4fe1ac6cff14

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution
    {K : Subfield ℂ} {S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ)}
    (hK : S ≤ Submodule.span ℂ {A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ S ∧ ∀ i j, A i j ∈ K})
    (hsing : ∀ A ∈ S, A.det = 0)
    {N : Matrix (Fin 2) (Fin 2) ℂ} (hN : N ∈ S) (hN0 : ∀ i j, N i j ≠ 0) :
    Module.finrank ℂ S ≤ 2 ∧
      ((∃ a : Fin 2 → ℂ, (∀ i, a i ∈ K) ∧ (∀ i, a i ≠ 0) ∧
          ∀ A ∈ S, ∃ b : Fin 2 → ℂ, ∀ i j, A i j = a i * b j) ∨
       (∃ b : Fin 2 → ℂ, (∀ j, b j ∈ K) ∧ (∀ j, b j ≠ 0) ∧
          ∀ A ∈ S, ∃ a : Fin 2 → ℂ, ∀ i j, A i j = a i * b j)) := by
  classical
  -- rank-one factorisation of a singular 2x2 matrix
  have rk1 : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.det = 0 →
      ∃ p q : Fin 2 → ℂ, ∀ i j, M i j = p i * q j := by
    intro M hM
    rw [Matrix.det_fin_two] at hM
    by_cases h00 : M 0 0 = 0
    · by_cases h01 : M 0 1 = 0
      · refine ⟨![0, 1], ![M 1 0, M 1 1], ?_⟩
        intro i j; fin_cases i <;> fin_cases j <;> simp [h00, h01]
      · have h10 : M 1 0 = 0 := by
          have hz : M 0 1 * M 1 0 = 0 := by linear_combination -hM + M 1 1 * h00
          rcases mul_eq_zero.mp hz with hz1 | hz1
          · exact absurd hz1 h01
          · exact hz1
        refine ⟨![M 0 1, M 1 1], ![0, 1], ?_⟩
        intro i j; fin_cases i <;> fin_cases j <;> simp [h00, h10]
    · refine ⟨![M 0 0, M 1 0], ![1, M 0 1 / M 0 0], ?_⟩
      intro i j; fin_cases i <;> fin_cases j <;> simp
      · field_simp
      · field_simp
        linear_combination hM
  -- the polarisation of the determinant vanishes on S
  have hbil : ∀ A ∈ S, ∀ B ∈ S,
      A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1 = 0 := by
    intro A hA B hB
    have h1 := hsing A hA
    have h2 := hsing B hB
    have h3 := hsing (A + B) (S.add_mem hA hB)
    rw [Matrix.det_fin_two] at h1 h2 h3
    simp only [Matrix.add_apply] at h3
    linear_combination h3 - h1 - h2
  -- proportionality of two vectors with vanishing 2x2 determinant
  have prop2 : ∀ x y : Fin 2 → ℂ, x 0 ≠ 0 → x 0 * y 1 - x 1 * y 0 = 0 →
      ∀ i, y i = (y 0 / x 0) * x i := by
    intro x y hx0 h
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hx0]
    · rw [div_mul_eq_mul_div, eq_div_iff hx0]; linear_combination h
  -- the distinguished element
  obtain ⟨p, q, hpq⟩ := rk1 N (hsing N hN)
  have hp : ∀ i, p i ≠ 0 := by
    intro i hi
    exact hN0 i 0 (by rw [hpq i 0, hi, zero_mul])
  have hq : ∀ j, q j ≠ 0 := by
    intro j hj
    exact hN0 0 j (by rw [hpq 0 j, hj, mul_zero])
  -- a nonzero K-rational element of S
  have hex : ∃ M, M ∈ S ∧ (∀ i j, M i j ∈ K) ∧ M ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : {A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ S ∧ ∀ i j, A i j ∈ K}
        ⊆ (↑(⊥ : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ)) : Set _) := by
      rintro A ⟨hA1, hA2⟩
      simpa using hcon A hA1 hA2
    have hbot : Submodule.span ℂ {A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ S ∧ ∀ i j, A i j ∈ K}
        ≤ ⊥ := Submodule.span_le.2 hsub
    have := Submodule.mem_bot ℂ |>.1 (hbot (hK hN))
    exact hN0 0 0 (by rw [this]; rfl)
  -- the dichotomy: common image line, or common kernel line
  have main : (∀ A ∈ S, ∃ b : Fin 2 → ℂ, ∀ i j, A i j = p i * b j) ∨
      (∀ A ∈ S, ∃ a : Fin 2 → ℂ, ∀ i j, A i j = a i * q j) := by
    by_cases hP : ∀ A ∈ S, ∃ b : Fin 2 → ℂ, ∀ i j, A i j = p i * b j
    · exact Or.inl hP
    · right
      push_neg at hP
      obtain ⟨A, hA, hA'⟩ := hP
      obtain ⟨r, s, hrs⟩ := rk1 A (hsing A hA)
      have hNA := hbil N hN A hA
      have hfac : (p 0 * r 1 - p 1 * r 0) * (q 0 * s 1 - q 1 * s 0) = 0 := by
        rw [hpq 0 0, hpq 1 1, hpq 0 1, hpq 1 0, hrs 0 0, hrs 1 1, hrs 0 1, hrs 1 0] at hNA
        linear_combination hNA
      have hd1 : p 0 * r 1 - p 1 * r 0 ≠ 0 := by
        intro hd
        have hri := prop2 p r (hp 0) hd
        obtain ⟨i, j, hij⟩ := hA' (fun j => (r 0 / p 0) * s j)
        exact hij (by rw [hrs i j, hri i]; ring)
      have hs : q 0 * s 1 - q 1 * s 0 = 0 := by
        rcases mul_eq_zero.mp hfac with h | h
        · exact absurd h hd1
        · exact h
      set lam : ℂ := s 0 / q 0 with hlam
      have hsq : ∀ j, s j = lam * q j := prop2 q s (hq 0) hs
      have hA0 : A ≠ 0 := by
        intro h
        obtain ⟨i, j, hij⟩ := hA' 0
        exact hij (by simp [h])
      have hlam0 : lam ≠ 0 := by
        intro h
        refine hA0 ?_
        ext i j
        rw [hrs i j, hsq j, h]
        simp
      -- now every element of S has rows proportional to q
      intro B hB
      obtain ⟨t, w, htw⟩ := rk1 B (hsing B hB)
      have hNB := hbil N hN B hB
      have hfacB : (p 0 * t 1 - p 1 * t 0) * (q 0 * w 1 - q 1 * w 0) = 0 := by
        rw [hpq 0 0, hpq 1 1, hpq 0 1, hpq 1 0, htw 0 0, htw 1 1, htw 0 1, htw 1 0] at hNB
        linear_combination hNB
      have hAB := hbil A hA B hB
      have hfacAB : (r 0 * t 1 - r 1 * t 0) * (s 0 * w 1 - s 1 * w 0) = 0 := by
        rw [hrs 0 0, hrs 1 1, hrs 0 1, hrs 1 0, htw 0 0, htw 1 1, htw 0 1, htw 1 0] at hAB
        linear_combination hAB
      by_cases hw : q 0 * w 1 - q 1 * w 0 = 0
      · set mu : ℂ := w 0 / q 0 with hmu
        have hwq : ∀ j, w j = mu * q j := prop2 q w (hq 0) hw
        exact ⟨fun i => t i * mu, fun i j => by rw [htw i j, hwq j]; ring⟩
      · -- forced B = 0
        have h1 : p 0 * t 1 - p 1 * t 0 = 0 := by
          rcases mul_eq_zero.mp hfacB with h | h
          · exact h
          · exact absurd h hw
        set c : ℂ := t 0 / p 0 with hc
        have htp : ∀ i, t i = c * p i := prop2 p t (hp 0) h1
        have h2 : s 0 * w 1 - s 1 * w 0 = 0 ∨ r 0 * t 1 - r 1 * t 0 = 0 := by
          rcases mul_eq_zero.mp hfacAB with h | h
          · exact Or.inr h
          · exact Or.inl h
        have hsw : s 0 * w 1 - s 1 * w 0 = lam * (q 0 * w 1 - q 1 * w 0) := by
          rw [hsq 0, hsq 1]; ring
        have h3 : r 0 * t 1 - r 1 * t 0 = 0 := by
          rcases h2 with h | h
          · exfalso
            rw [hsw] at h
            rcases mul_eq_zero.mp h with h' | h'
            · exact hlam0 h'
            · exact hw h'
          · exact h
        have hc0 : c = 0 := by
          rw [htp 0, htp 1] at h3
          have : c * (p 1 * r 0 - p 0 * r 1) = 0 := by linear_combination h3
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd (by linear_combination -h) hd1
        refine ⟨0, fun i j => ?_⟩
        rw [htw i j, htp i, hc0]
        simp
  -- upgrade the shared line to a K-rational one
  obtain ⟨M, hMS, hMK, hM0⟩ := hex
  -- finrank bound
  have frI : ∀ a : Fin 2 → ℂ, (∀ A ∈ S, ∃ b : Fin 2 → ℂ, ∀ i j, A i j = a i * b j) →
      Module.finrank ℂ S ≤ 2 := by
    intro a ha
    let f : (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
      { toFun := fun b => Matrix.of fun i j => a i * b j
        map_add' := by intro x y; ext i j; simp [mul_add]
        map_smul' := by intro c x; ext i j; simp; ring }
    have hle : S ≤ LinearMap.range f := by
      intro A hA
      obtain ⟨b, hb⟩ := ha A hA
      exact ⟨b, by ext i j; simpa [f] using (hb i j).symm⟩
    calc Module.finrank ℂ S ≤ Module.finrank ℂ (LinearMap.range f) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank ℂ (Fin 2 → ℂ) := f.finrank_range_le
      _ = 2 := by simp
  have frK : ∀ b : Fin 2 → ℂ, (∀ A ∈ S, ∃ a : Fin 2 → ℂ, ∀ i j, A i j = a i * b j) →
      Module.finrank ℂ S ≤ 2 := by
    intro b hb
    let f : (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
      { toFun := fun a => Matrix.of fun i j => a i * b j
        map_add' := by intro x y; ext i j; simp [add_mul]
        map_smul' := by intro c x; ext i j; simp; ring }
    have hle : S ≤ LinearMap.range f := by
      intro A hA
      obtain ⟨a, ha⟩ := hb A hA
      exact ⟨a, by ext i j; simpa [f] using (ha i j).symm⟩
    calc Module.finrank ℂ S ≤ Module.finrank ℂ (LinearMap.range f) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank ℂ (Fin 2 → ℂ) := f.finrank_range_le
      _ = 2 := by simp
  rcases main with hI | hK2
  · obtain ⟨b, hb⟩ := hI M hMS
    have hbne : ∃ j, b j ≠ 0 := by
      by_contra hcb
      push_neg at hcb
      exact hM0 (by ext i j; simp [hb i j, hcb j])
    obtain ⟨j0, hj0⟩ := hbne
    refine ⟨frI p hI, Or.inl ⟨fun i => M i j0, fun i => hMK i j0, ?_, ?_⟩⟩
    · intro i
      show M i j0 ≠ 0
      rw [hb i j0]
      exact mul_ne_zero (hp i) hj0
    · intro A hA
      obtain ⟨c, hc⟩ := hI A hA
      refine ⟨fun j => c j / b j0, fun i j => ?_⟩
      show A i j = M i j0 * (c j / b j0)
      rw [hc i j, hb i j0]
      field_simp
  · obtain ⟨a, ha⟩ := hK2 M hMS
    have hane : ∃ i, a i ≠ 0 := by
      by_contra hca
      push_neg at hca
      exact hM0 (by ext i j; simp [ha i j, hca i])
    obtain ⟨i0, hi0⟩ := hane
    refine ⟨frK q hK2, Or.inr ⟨fun j => M i0 j, fun j => hMK i0 j, ?_, ?_⟩⟩
    · intro j
      show M i0 j ≠ 0
      rw [ha i0 j]
      exact mul_ne_zero hi0 (hq j)
    · intro A hA
      obtain ⟨c, hc⟩ := hK2 A hA
      refine ⟨fun i => c i / a i0, fun i j => ?_⟩
      show A i j = c i / a i0 * M i0 j
      rw [hc i j, ha i0 j]
      field_simp
