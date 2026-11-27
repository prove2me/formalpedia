-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:38.943774+00:00
-- url     : https://prove2.me/submissions/124995e6-0f17-4724-b8b7-da8f8d9c81aa

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:5 (Hestenes–Stiefel 1952, p. 416): the formulas (5:10), (5:11), the bounds (5:12)
and the eigenvalue bracket for `1/aᵢ`; `m` is the step at which the cg-method terminates. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ,
      cgAlpha A (cgIter A k x₀ i) = ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgAlpha A (cgIter A k x₀ i) = ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).r) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgAlpha A (cgIter A k x₀ i) = ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ 0).r) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p))) ∧
    (∀ i : ℕ,
      cgBeta A k x₀ i = ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
        ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgBeta A k x₀ i = -((cgIter A k x₀ (i + 1)).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgBeta A k x₀ i = -((cgIter A k x₀ (i + 1)).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).r)) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p))) ∧
    1 / cgAlpha A (cgIter A k x₀ 0) = rayleigh A (cgIter A k x₀ 0).r ∧
    (∀ i : ℕ, 0 < i → i < m →
      rayleigh A (cgIter A k x₀ i).p < 1 / cgAlpha A (cgIter A k x₀ i) ∧
        1 / cgAlpha A (cgIter A k x₀ i) < rayleigh A (cgIter A k x₀ i).r) ∧
    (∀ i : ℕ, i < m → ∃ j₁ j₂ : Fin n,
      hA.1.eigenvalues j₁ ≤ 1 / cgAlpha A (cgIter A k x₀ i) ∧
        1 / cgAlpha A (cgIter A k x₀ i) ≤ hA.1.eigenvalues j₂) := by
          obtain ⟨R, hR⟩ : ∃ R : ℕ → Fin n → ℝ, R = fun i => (cgIter A k x₀ i).r := ⟨_, rfl⟩
          obtain ⟨P, hP⟩ : ∃ P : ℕ → Fin n → ℝ, P = fun i => (cgIter A k x₀ i).p := ⟨_, rfl⟩
          have hRi : ∀ i, (cgIter A k x₀ i).r = R i := by intro i; rw [hR]
          have hPi : ∀ i, (cgIter A k x₀ i).p = P i := by intro i; rw [hP]
          obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun i => R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i)) := ⟨_, rfl⟩
          obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun i => R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i) := ⟨_, rfl⟩
          have hai : ∀ i, R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i)) = a i := by intro i; rw [ha]
          have hbi : ∀ i, R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i) = b i := by intro i; rw [hb]
          have hr : ∀ i, R (i+1) = R i - a i • (A *ᵥ P i) := by
            intro i; rw [← hai, ← hRi, ← hRi, ← hPi]; rfl
          have hp : ∀ i, P (i+1) = R (i+1) + b i • P i := by
            intro i; rw [← hbi, ← hRi, ← hRi, ← hPi, ← hPi]; rfl
          have hp0 : P 0 = R 0 := by rw [← hRi, ← hPi]; rfl
          have hRP : ∀ i, R (i+1) = P (i+1) - b i • P i := by
            intro i; rw [hp i]; abel
          simp only [cgAlpha, cgBeta, rayleigh, hRi, hPi, hai, hbi] at hm hact ⊢
          clear hRi hPi hR hP
          -- basic facts about A
          have hT : Aᵀ = A := by
            have := hA.1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
          have hsym : ∀ x y : Fin n → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
            intro x y
            rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
          have hPD : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := by
            intro x hx
            simpa using hA.dotProduct_mulVec_pos hx
          have hPZ : ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = 0 → x = 0 := by
            intro x hx; by_contra h; have := hPD x h; linarith
          have hself : ∀ x : Fin n → ℝ, x ⬝ᵥ x = 0 → x = 0 := fun x hx => dotProduct_self_eq_zero.mp hx
          have hZ : ∀ i, R i = 0 → P i = 0 := by
            intro i hi
            cases i with
            | zero => rw [hp0, hi]
            | succ i => rw [hp, hi, ← hbi, hi]; simp
          have hL1 : ∀ i, P i ⬝ᵥ R i = R i ⬝ᵥ R i := by
            intro i
            induction i with
            | zero => rw [hp0]
            | succ i ih =>
              have hC3 : P i ⬝ᵥ R (i+1) = 0 := by
                rw [hr, dotProduct_sub, dotProduct_smul, ih, smul_eq_mul, ← hai]
                by_cases h : P i ⬝ᵥ (A *ᵥ P i) = 0
                · have := hPZ _ h
                  rw [this] at ih; simp at ih; rw [← ih]; simp
                · field_simp; ring
              rw [hp, add_dotProduct, smul_dotProduct, hC3, smul_zero, add_zero]
          have hE : ∀ i, a i * (P i ⬝ᵥ (A *ᵥ P i)) = R i ⬝ᵥ R i := by
            intro i
            rw [← hai]
            by_cases h : P i ⬝ᵥ (A *ᵥ P i) = 0
            · have h0 := hPZ _ h
              have := hL1 i
              rw [h0] at this; simp at this; rw [← this, h]; simp
            · field_simp
          have hC3 : ∀ i, P i ⬝ᵥ R (i+1) = 0 := by
            intro i
            rw [hr, dotProduct_sub, dotProduct_smul, hL1, smul_eq_mul, hE]; ring
          have hane : ∀ i, R i ≠ 0 → a i ≠ 0 := by
            intro i hi h
            have := hE i
            rw [h, zero_mul] at this
            exact hi (hself _ this.symm)
          have hsmulAP : ∀ i, a i • (A *ᵥ P i) = R i - R (i+1) := by
            intro i; rw [hr]; abel
          have hdotAP : ∀ i (x : Fin n → ℝ), a i * (x ⬝ᵥ (A *ᵥ P i)) = x ⬝ᵥ R i - x ⬝ᵥ R (i+1) := by
            intro i x
            rw [← smul_eq_mul, ← dotProduct_smul, hsmulAP, dotProduct_sub]
          have main : ∀ i, ∀ j < i, R i ⬝ᵥ R j = 0 ∧ P i ⬝ᵥ (A *ᵥ P j) = 0 := by
            intro i
            induction i with
            | zero => intro j hj; omega
            | succ i ih =>
              have hL2 : R i ⬝ᵥ (A *ᵥ P i) = P i ⬝ᵥ (A *ᵥ P i) := by
                cases i with
                | zero => rw [hp0]
                | succ i =>
                  rw [hRP i, sub_dotProduct, smul_dotProduct, hsym (P i), (ih i (by omega)).2]
                  simp
              have hC1 : R (i+1) ⬝ᵥ R i = 0 := by
                rw [hr, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), hL2, smul_eq_mul,
                  hE]; ring
              have hRAP : ∀ j < i, R j ⬝ᵥ (A *ᵥ P i) = 0 := by
                intro j hj
                cases j with
                | zero => rw [← hp0, hsym, (ih 0 hj).2]
                | succ j =>
                  rw [hRP j, sub_dotProduct, smul_dotProduct, hsym (P (j+1)), hsym (P j),
                    (ih (j+1) hj).2, (ih j (by omega)).2]; simp
              have hRR : ∀ j < i+1, R (i+1) ⬝ᵥ R j = 0 := by
                intro j hj
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
                · rw [hr, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), hRAP j hj,
                    (ih j hj).1]; simp
                · rw [hj]; exact hC1
              intro j hj
              refine ⟨hRR j hj, ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
              · rw [hp, add_dotProduct, smul_dotProduct, (ih j hj').2, smul_zero, add_zero]
                by_cases hRj : R j = 0
                · rw [hZ j hRj]; simp
                · have := hdotAP j (R (i+1))
                  rw [hRR j hj, hRR (j+1) (by omega), sub_zero] at this
                  exact (mul_eq_zero.mp this).resolve_left (hane j hRj)
              · subst hj'
                by_cases hRj : R j = 0
                · rw [hZ j hRj]; simp
                · have h1 := hdotAP j (R (j+1))
                  rw [hC1] at h1
                  have hRj2 : R j ⬝ᵥ R j ≠ 0 := fun h => hRj (hself _ h)
                  have hb' : b j * (R j ⬝ᵥ R j) = R (j+1) ⬝ᵥ R (j+1) := by
                    rw [← hbi]; field_simp
                  have h2 : a j * (P (j + 1) ⬝ᵥ (A *ᵥ P j)) = 0 := by
                    rw [hp, add_dotProduct, smul_dotProduct, smul_eq_mul, mul_add, h1, ← hb', ← hE j]
                    ring
                  exact (mul_eq_zero.mp h2).resolve_left (hane j hRj)
          have hconj : ∀ i j, j < i → P i ⬝ᵥ (A *ᵥ P j) = 0 := fun i j h => (main i j h).2
          have hRAPT : ∀ i j, j < i → R (i+1) ⬝ᵥ (A *ᵥ P j) = 0 := by
            intro i j h
            rw [hRP i, sub_dotProduct, smul_dotProduct, hconj (i+1) j (by omega), hconj i j h]; simp
          have hS : ∀ i, P i ⬝ᵥ R 0 = P i ⬝ᵥ R i := by
            intro i
            have : ∀ j ≤ i, P i ⬝ᵥ R j = P i ⬝ᵥ R 0 := by
              intro j
              induction j with
              | zero => intro _; rfl
              | succ j ih =>
                intro hj
                rw [hr, dotProduct_sub, dotProduct_smul, hconj i j (by omega), ih (by omega)]; simp
            exact (this i le_rfl).symm
          have hpAp0 : ∀ i, P i ⬝ᵥ (A *ᵥ P i) = 0 → R i = 0 := by
            intro i h
            have h0 := hPZ _ h
            have := hL1 i
            rw [h0] at this; simp at this
            exact hself _ this.symm
          have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ x := fun x hx =>
            lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
              (fun h => hx (hself _ h.symm))
          have hPne : ∀ i, R i ≠ 0 → P i ≠ 0 := by
            intro i hi h
            have := hL1 i
            rw [h] at this; simp at this
            exact hi (hself _ this.symm)
          have hb2 : ∀ i, b i = -(R (i + 1) ⬝ᵥ (A *ᵥ P i)) / (P i ⬝ᵥ (A *ᵥ P i)) := by
            intro i
            by_cases h : P i ⬝ᵥ (A *ᵥ P i) = 0
            · have := hpAp0 i h
              rw [h, div_zero, ← hbi, this]; simp
            · rw [eq_div_iff h]
              have := hconj (i+1) i (by omega)
              rw [hp, add_dotProduct, smul_dotProduct, smul_eq_mul] at this
              linarith
          have hpart4 : ∀ i, 0 < i → i < m → P i ⬝ᵥ (A *ᵥ P i) / (P i ⬝ᵥ P i) < 1 / a i ∧
              1 / a i < R i ⬝ᵥ (A *ᵥ R i) / (R i ⬝ᵥ R i) := by
            intro i hi0 him
            obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            have hR1 : R (i+1) ≠ 0 := hact (i+1) him
            have hR0 : R i ≠ 0 := hact i (by omega)
            have hRR1 := hpos _ hR1
            have hRR0 := hpos _ hR0
            have hP1 := hPD _ (hPne _ hR1)
            have hP0 := hPD _ (hPne _ hR0)
            have hPP0 := hpos _ (hPne _ hR0)
            have hbpos : 0 < b i := by rw [← hbi]; exact div_pos hRR1 hRR0
            rw [← hai, one_div_div]
            constructor
            · have hPP : P (i+1) ⬝ᵥ P (i+1) = R (i+1) ⬝ᵥ R (i+1) + b i ^ 2 * (P i ⬝ᵥ P i) := by
                have hc := hC3 i
                rw [dotProduct_comm] at hc
                rw [hp, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
                  dotProduct_smul, dotProduct_smul, dotProduct_comm (P i) (R (i+1)), hc]
                simp [smul_eq_mul]; ring
              apply div_lt_div_of_pos_left hP1 hRR1
              rw [hPP]; nlinarith [mul_pos (pow_pos hbpos 2) hPP0]
            · have hRAR : R (i+1) ⬝ᵥ (A *ᵥ R (i+1)) =
                  P (i+1) ⬝ᵥ (A *ᵥ P (i+1)) + b i ^ 2 * (P i ⬝ᵥ (A *ᵥ P i)) := by
                have hc := hconj (i+1) i (by omega)
                have hc' : P i ⬝ᵥ (A *ᵥ P (i+1)) = 0 := by rw [hsym]; exact hc
                rw [hRP i, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
                  smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hc, hc']
                simp [smul_eq_mul]; ring
              apply div_lt_div_of_pos_right _ hRR1
              rw [hRAR]; nlinarith [mul_pos (pow_pos hbpos 2) hP0]
          have heig : ∀ z : Fin n → ℝ, z ≠ 0 →
                (∃ j, hA.1.eigenvalues j ≤ (z ⬝ᵥ (A *ᵥ z)) / (z ⬝ᵥ z)) ∧
                (∃ j, (z ⬝ᵥ (A *ᵥ z)) / (z ⬝ᵥ z) ≤ hA.1.eigenvalues j) := by
            open scoped Pointwise in
            intro z hz
            have hzz : 0 < z ⬝ᵥ z := by
              have := (Matrix.PosDef.one (n := Fin n) (R := ℝ)).dotProduct_mulVec_pos hz
              simpa using this
            set c := (z ⬝ᵥ (A *ᵥ z)) / (z ⬝ᵥ z) with hc
            have hcz : c * (z ⬝ᵥ z) = z ⬝ᵥ (A *ᵥ z) := by rw [hc]; field_simp
            constructor
            · by_contra hcon
              push Not at hcon
              set B : Matrix (Fin n) (Fin n) ℝ := A - algebraMap ℝ _ c with hB
              have hBh : B.IsHermitian := by
                rw [hB, Algebra.algebraMap_eq_smul_one]
                exact hA.1.sub (isHermitian_one.smul (IsSelfAdjoint.all c))
              have hBpos : B.PosDef := by
                rw [hBh.posDef_iff_eigenvalues_pos]
                intro j
                have hmem : hBh.eigenvalues j ∈ (spectrum ℝ A - ({c} : Set ℝ)) := by
                  rw [spectrum.sub_singleton_eq]; exact hBh.eigenvalues_mem_spectrum_real j
                rw [hA.1.spectrum_real_eq_range_eigenvalues] at hmem
                obtain ⟨x, ⟨j', rfl⟩, y, hy, hxy⟩ := hmem
                rw [Set.mem_singleton_iff] at hy
                subst hy
                rw [← hxy]
                linarith [hcon j']
              have := hBpos.dotProduct_mulVec_pos hz
              simp [hB, Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, dotProduct_sub] at this
              nlinarith
            · by_contra hcon
              push Not at hcon
              set B : Matrix (Fin n) (Fin n) ℝ := algebraMap ℝ _ c - A with hB
              have hBh : B.IsHermitian := by
                rw [hB, Algebra.algebraMap_eq_smul_one]
                exact (isHermitian_one.smul (IsSelfAdjoint.all c)).sub hA.1
              have hBpos : B.PosDef := by
                rw [hBh.posDef_iff_eigenvalues_pos]
                intro j
                have hmem : hBh.eigenvalues j ∈ (({c} : Set ℝ) - spectrum ℝ A) := by
                  rw [spectrum.singleton_sub_eq]; exact hBh.eigenvalues_mem_spectrum_real j
                rw [hA.1.spectrum_real_eq_range_eigenvalues] at hmem
                obtain ⟨y, hy, x, ⟨j', rfl⟩, hxy⟩ := hmem
                rw [Set.mem_singleton_iff] at hy
                subst hy
                rw [← hxy]
                linarith [hcon j']
              have := hBpos.dotProduct_mulVec_pos hz
              simp [hB, Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, dotProduct_sub] at this
              nlinarith
          refine ⟨?_, ?_, ?_, hpart4, ?_⟩
          · intro i
            refine ⟨trivial, ?_, ?_⟩
            · rw [hL1, hai]
            · rw [hS, hL1, hai]
          · intro i
            refine ⟨trivial, hb2 i, ?_⟩
            have hnum : R (i + 1) ⬝ᵥ (A *ᵥ R i) = R (i + 1) ⬝ᵥ (A *ᵥ P i) := by
              cases i with
              | zero => rw [hp0]
              | succ i =>
                rw [show R (i+1) = P (i+1) - b i • P i from hRP i, mulVec_sub, mulVec_smul,
                  dotProduct_sub, dotProduct_smul, hRAPT (i+1) i (by omega)]
                simp
            rw [hnum, hb2]
          · rw [← hai, hp0, one_div_div]
          · intro i him
            have hRne : R i ≠ 0 := hact i him
            have hPne' := hPne i hRne
            have hbr : P i ⬝ᵥ (A *ᵥ P i) / (P i ⬝ᵥ P i) ≤ 1 / a i ∧
                1 / a i ≤ R i ⬝ᵥ (A *ᵥ R i) / (R i ⬝ᵥ R i) := by
              rcases Nat.eq_zero_or_pos i with h0 | h0
              · subst h0
                rw [← hai, hp0, one_div_div]
                exact ⟨le_rfl, le_rfl⟩
              · have := hpart4 i h0 him
                exact ⟨this.1.le, this.2.le⟩
            obtain ⟨⟨j₁, hj₁⟩, -⟩ := heig _ hPne'
            obtain ⟨-, ⟨j₂, hj₂⟩⟩ := heig _ hRne
            exact ⟨j₁, j₂, hj₁.trans hbr.1, hbr.2.trans hj₂⟩
