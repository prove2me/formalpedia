-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_7_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:06.685276+00:00
-- url     : https://prove2.me/submissions/73b4e94b-d048-4cfd-9d53-5c3fd7125c27

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:2 (Hestenes–Stiefel 1952, p. 418): `x̄ᵢ` lies in the convex hull `Sᵢ` of
`x₀, …, xᵢ`, is the unique minimizer of `|k − Ax|²` on the plane `Pᵢ`, satisfies (7:4), and the
squared residuals `|r̄ᵢ|²` decrease, strictly through termination step `m`, by (7:5). -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, smoothX A k x₀ i ∈
      convexHull ℝ (Set.range fun j : Fin (i + 1) => (cgIter A k x₀ j).x)) ∧
    (∀ i : ℕ, smoothX A k x₀ i ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i ∧
      ∀ y ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i, y ≠ smoothX A k x₀ i →
        (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) <
          (k - A *ᵥ y) ⬝ᵥ (k - A *ᵥ y)) ∧
    (∀ i : ℕ,
      (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) =
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i ∧
        (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) =
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ^ 2 /
            ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p)) ∧
    (∀ i : ℕ, (k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1)) ≤
      (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i + 1 ≤ m →
      (k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1)) <
        (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) ∧
    (∀ i : ℕ, (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) -
        (k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1)) =
      (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) /
        smoothC A k x₀ (i + 1)) := by
          have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
            intro u v
            have hT : Aᵀ = A := by
              have := hA.1
              rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
          have hpos : ∀ w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (A *ᵥ w) := by
            intro w hw
            simpa using hA.dotProduct_mulVec_pos hw
          have hnn : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
            intro w
            by_cases hw : w = 0
            · simp [hw]
            · exact (hpos w hw).le
          have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
          have hself : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
            Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
          suffices key : ∀ (X R P : ℕ → (Fin n → ℝ)) (α β C : ℕ → ℝ) (Xb : ℕ → (Fin n → ℝ)),
              X 0 = x₀ → R 0 = k - A *ᵥ X 0 → P 0 = R 0 →
              (∀ i, α i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
              (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
              (∀ i, X (i+1) = X i + α i • P i) →
              (∀ i, R (i+1) = R i - α i • (A *ᵥ P i)) →
              (∀ i, P (i+1) = R (i+1) + β i • P i) →
              C 0 = 1 → Xb 0 = x₀ →
              (∀ i, C (i+1) = 1 + β i * C i) →
              (∀ i, Xb (i+1) = (1 + β i * C i)⁻¹ • (X (i+1) + (β i * C i) • Xb i)) →
              R m = 0 → (∀ j < m, R j ≠ 0) →
            (∀ i : ℕ, Xb i ∈ convexHull ℝ (Set.range fun j : Fin (i + 1) => X j)) ∧
            (∀ i : ℕ, Xb i ∈ cdPlane x₀ P i ∧
              ∀ y ∈ cdPlane x₀ P i, y ≠ Xb i →
                (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) < (k - A *ᵥ y) ⬝ᵥ (k - A *ᵥ y)) ∧
            (∀ i : ℕ,
              (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) = (R i ⬝ᵥ R i) / C i ∧
                (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) = (R i ⬝ᵥ R i) ^ 2 / (P i ⬝ᵥ P i)) ∧
            (∀ i : ℕ, (k - A *ᵥ Xb (i + 1)) ⬝ᵥ (k - A *ᵥ Xb (i + 1)) ≤
              (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i)) ∧
            (∀ i : ℕ, i + 1 ≤ m →
              (k - A *ᵥ Xb (i + 1)) ⬝ᵥ (k - A *ᵥ Xb (i + 1)) < (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i)) ∧
            (∀ i : ℕ, (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) - (k - A *ᵥ Xb (i + 1)) ⬝ᵥ (k - A *ᵥ Xb (i + 1)) =
              (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) / C (i + 1)) by
            exact key (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
              (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
              (fun i => cgBeta A k x₀ i) (fun i => smoothC A k x₀ i) (fun i => smoothX A k x₀ i)
              rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              rfl rfl (fun _ => rfl) (fun _ => rfl)
              hm hact
          intro X R P α β C Xb hX0 hR0 hP0 hα hβ hX hRs hPs hC0 hXb0 hCs hXbs hm hact
          have hRX : ∀ i, R i = k - A *ᵥ X i := by
            intro i
            induction i with
            | zero => exact hR0
            | succ i ih =>
              rw [hRs, hX, ih, Matrix.mulVec_add, Matrix.mulVec_smul]; abel
          have hRP0 : ∀ i, R i = 0 → P i = 0 := by
            intro i hi
            cases i with
            | zero => rw [hP0, hi]
            | succ i => rw [hPs, hβ, hi]; simp
          have hαP : ∀ i, α i = 0 → P i = 0 := by
            intro i hi
            rw [hα, div_eq_zero_iff] at hi
            rcases hi with hi | hi
            · exact hRP0 i (hzero _ hi)
            · by_contra hne
              exact (hpos _ hne).ne' hi
          have hQ : ∀ i, (∀ j < i, R i ⬝ᵥ P j = 0 ∧ R i ⬝ᵥ R j = 0 ∧ P i ⬝ᵥ (A *ᵥ P j) = 0) ∧
              R i ⬝ᵥ P i = R i ⬝ᵥ R i := by
            intro i
            induction i with
            | zero => exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [hP0]⟩
            | succ i ih =>
              obtain ⟨ih1, ih2⟩ := ih
              have hii : R (i+1) ⬝ᵥ P i = 0 := by
                by_cases hp : P i = 0
                · rw [hp]; simp
                · have hpp := hpos _ hp
                  rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ih2, hα]
                  simp only [smul_eq_mul]
                  field_simp
                  ring
              have ha : ∀ j < i + 1, R (i+1) ⬝ᵥ P j = 0 := by
                intro j hj
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
                · rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ← hsym,
                    (ih1 j hj).1, (ih1 j hj).2.2]
                  simp
                · rw [hj]; exact hii
              have hb : ∀ j < i + 1, R (i+1) ⬝ᵥ R j = 0 := by
                intro j hj
                cases j with
                | zero => rw [← hP0]; exact ha 0 hj
                | succ j =>
                  have e : R (j+1) = P (j+1) - β j • P j := by rw [hPs]; abel
                  rw [e, dotProduct_sub, dotProduct_smul, ha _ hj, ha j (by omega)]
                  simp
              have hRA' : ∀ j < i, R (i+1) ⬝ᵥ (A *ᵥ P j) = 0 := by
                intro j hj
                by_cases h0 : α j = 0
                · rw [hαP j h0]; simp
                · have e : α j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
                  have : α j * (R (i+1) ⬝ᵥ (A *ᵥ P j)) = 0 := by
                    rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega),
                      hb (j+1) (by omega)]
                    simp
                  rcases mul_eq_zero.mp this with h1 | h1
                  · exact absurd h1 h0
                  · exact h1
              refine ⟨fun j hj => ⟨ha j hj, hb j hj, ?_⟩, ?_⟩
              · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
                · rw [hPs, add_dotProduct, smul_dotProduct, hRA' j hj, (ih1 j hj).2.2]; simp
                · subst hj
                  by_cases h0 : α j = 0
                  · rw [hαP j h0]; simp
                  · have e : α j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
                    have h1 : α j * (R (j+1) ⬝ᵥ (A *ᵥ P j)) = - (R (j+1) ⬝ᵥ R (j+1)) := by
                      rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega)]
                      simp
                    have hp : P j ≠ 0 := by
                      intro hp; apply h0; rw [hα, hp]; simp
                    have hpp := hpos _ hp
                    have hrr : R j ⬝ᵥ R j ≠ 0 := by
                      intro hr; apply h0; rw [hα, hr]; simp
                    rw [hPs, add_dotProduct, smul_dotProduct, hβ, smul_eq_mul]
                    rw [hα] at h1
                    field_simp at h1 ⊢
                    linear_combination h1
              · rw [hPs, dotProduct_add, dotProduct_smul, hii]; simp
          have hN : ∀ i < m, 0 < R i ⬝ᵥ R i := by
            intro i hi
            rcases (hself (R i)).lt_or_eq with h1 | h1
            · exact h1
            · exact absurd (hzero _ h1.symm) (hact i hi)
          have hβnn : ∀ i, 0 ≤ β i := fun i => by rw [hβ]; exact div_nonneg (hself _) (hself _)
          have hC1 : ∀ i, 1 ≤ C i := by
            intro i
            induction i with
            | zero => rw [hC0]
            | succ i ih => rw [hCs]; nlinarith [hβnn i]
          have hCne : ∀ i, C i ≠ 0 := fun i => by linarith [hC1 i]
          have hXb' : ∀ i, Xb (i+1) = (C (i+1))⁻¹ • (X (i+1) + (β i * C i) • Xb i) := by
            intro i; rw [hXbs, hCs]
          have hRX' := hRX
          have part1 : ∀ i : ℕ, P i = C i • (k - A *ᵥ Xb i) := by
            intro i
            induction i with
            | zero => rw [hP0, hR0, hC0, hXb0, hX0, one_smul]
            | succ i ih =>
              rw [hXb' i, Matrix.mulVec_smul, smul_sub, smul_smul, mul_inv_cancel₀ (hCne _), one_smul,
                Matrix.mulVec_add, Matrix.mulVec_smul, hPs, ih, hRX (i+1), hCs]
              module
          have part5 : ∀ i : ℕ, k - A *ᵥ Xb i = (1 / C i) • P i := by
            intro i
            rw [part1 i, smul_smul, one_div, inv_mul_cancel₀ (hCne _), one_smul]
          have hRP : ∀ i, R (i+1) ⬝ᵥ P i = 0 := fun i => ((hQ (i+1)).1 i (Nat.lt_succ_self i)).1
          have hβR : ∀ i, β i * (R i ⬝ᵥ R i) = R (i+1) ⬝ᵥ R (i+1) := by
            intro i
            rw [hβ]
            by_cases h0 : R i ⬝ᵥ R i = 0
            · have hr := hzero _ h0
              have : R (i+1) = 0 := by
                rw [hRs, hα, hr, hRP0 i hr]; simp
              rw [h0, this]; simp
            · field_simp
          have hCRP : ∀ i, C i * (R i ⬝ᵥ R i) = P i ⬝ᵥ P i := by
            intro i
            induction i with
            | zero => rw [hC0, hP0, one_mul]
            | succ i ih =>
              have hrp := hRP i
              have hpr : P i ⬝ᵥ R (i+1) = 0 := by rw [dotProduct_comm]; exact hrp
              rw [hPs (i), dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_smul,
                dotProduct_smul, smul_dotProduct, smul_dotProduct, hrp, hpr, ← ih, hCs, ← hβR i]
              simp only [smul_eq_mul]
              ring
          have hCpos : ∀ i, 0 < C i := fun i => by linarith [hC1 i]
          have hE : ∀ i, (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) = (R i ⬝ᵥ R i) / C i := by
            intro i
            rw [part5 i, smul_dotProduct, dotProduct_smul, ← hCRP i, smul_eq_mul, smul_eq_mul]
            have := hCne i
            field_simp
          -- plane facts
          have hupd : ∀ (i : ℕ) (γ : ℕ → ℝ) (c : ℝ),
              ∑ j ∈ Finset.range (i+1), Function.update γ i c j • P j =
                ∑ j ∈ Finset.range i, γ j • P j + c • P i := by
            intro i γ c
            rw [Finset.sum_range_succ, Function.update_self]
            congr 1
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [Function.update_of_ne (Finset.mem_range.mp hj).ne]
          have hcombo : ∀ (i : ℕ) (u v : Fin n → ℝ) (a b : ℝ), u ∈ cdPlane x₀ P i →
              v ∈ cdPlane x₀ P i → a + b = 1 → a • u + b • v ∈ cdPlane x₀ P i := by
            rintro i u v a b ⟨γ, rfl⟩ ⟨γ', rfl⟩ hab
            refine ⟨fun j => a * γ j + b * γ' j, ?_⟩
            simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
            obtain rfl : b = 1 - a := by linarith
            module
          have hmono : ∀ (i : ℕ) (v : Fin n → ℝ), v ∈ cdPlane x₀ P i → v ∈ cdPlane x₀ P (i+1) := by
            rintro i v ⟨γ, rfl⟩
            refine ⟨Function.update γ i 0, ?_⟩
            rw [hupd]; simp
          have hXplane : ∀ i, X i ∈ cdPlane x₀ P i := by
            intro i
            induction i with
            | zero => exact ⟨0, by simp [hX0]⟩
            | succ i ih =>
              obtain ⟨γ, hγ⟩ := ih
              refine ⟨Function.update γ i (α i), ?_⟩
              rw [hupd, hX, hγ, add_assoc]
          have hXbplane : ∀ i, Xb i ∈ cdPlane x₀ P i := by
            intro i
            induction i with
            | zero => exact ⟨0, by simp [hXb0]⟩
            | succ i ih =>
              have hne : (1 + β i * C i) ≠ 0 := by rw [← hCs]; exact hCne _
              have e : Xb (i+1) = (1 + β i * C i)⁻¹ • X (i+1) +
                  ((1 + β i * C i)⁻¹ * (β i * C i)) • Xb i := by
                rw [hXbs, smul_add, smul_smul]
              rw [e]
              refine hcombo _ _ _ _ _ (hXplane _) (hmono _ _ ih) ?_
              field_simp
          have hmin : ∀ i, ∀ y ∈ cdPlane x₀ P i, y ≠ Xb i →
              (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) < (k - A *ᵥ y) ⬝ᵥ (k - A *ᵥ y) := by
            intro i y hy hne
            obtain ⟨γ, hγ⟩ := hy
            obtain ⟨γ', hγ'⟩ := hXbplane i
            set d := y - Xb i with hd
            have hdsum : d = ∑ j ∈ Finset.range i, (γ j - γ' j) • P j := by
              rw [hd, hγ, hγ']
              simp only [sub_smul, Finset.sum_sub_distrib]
              abel
            have horth : P i ⬝ᵥ (A *ᵥ d) = 0 := by
              rw [hdsum, Matrix.mulVec_sum, dotProduct_sum]
              refine Finset.sum_eq_zero (fun j hj => ?_)
              rw [Matrix.mulVec_smul, dotProduct_smul, ((hQ i).1 j (Finset.mem_range.mp hj)).2.2]
              simp
            have hd0 : d ≠ 0 := by rw [hd]; exact sub_ne_zero.mpr hne
            have hAd : A *ᵥ d ≠ 0 := by
              intro h
              have := hpos d hd0
              rw [h] at this; simp at this
            have hAdpos : 0 < (A *ᵥ d) ⬝ᵥ (A *ᵥ d) :=
              lt_of_le_of_ne (hself _) (fun h => hAd (hzero _ h.symm))
            have hy' : k - A *ᵥ y = (k - A *ᵥ Xb i) - A *ᵥ d := by
              rw [hd, Matrix.mulVec_sub]; abel
            have horth' : (k - A *ᵥ Xb i) ⬝ᵥ (A *ᵥ d) = 0 := by
              rw [part5 i, smul_dotProduct, horth]; simp
            have horth'' : (A *ᵥ d) ⬝ᵥ (k - A *ᵥ Xb i) = 0 := by rw [dotProduct_comm]; exact horth'
            rw [hy']
            generalize k - A *ᵥ Xb i = r at horth' horth'' ⊢
            rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, horth', horth'']
            linarith
          have hdiff : ∀ i, (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) -
              (k - A *ᵥ Xb (i + 1)) ⬝ᵥ (k - A *ᵥ Xb (i + 1)) =
              (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) / C (i + 1) := by
            intro i
            rw [hE, hE, ← hβR i]
            have h1 := hCne i
            have h2 := hCne (i+1)
            have h3 := hCs i
            field_simp
            rw [h3]; ring
          refine ⟨?_, fun i => ⟨hXbplane i, hmin i⟩, ?_, ?_, ?_, hdiff⟩
          · intro i
            induction i with
            | zero =>
              rw [hXb0, ← hX0]
              exact subset_convexHull ℝ _ ⟨0, rfl⟩
            | succ i ih =>
              have hne : (1 + β i * C i) ≠ 0 := by rw [← hCs]; exact hCne _
              have e : Xb (i+1) = (1 + β i * C i)⁻¹ • X (i+1) +
                  ((1 + β i * C i)⁻¹ * (β i * C i)) • Xb i := by
                rw [hXbs, smul_add, smul_smul]
              have hpos1 : 0 < 1 + β i * C i := by rw [← hCs]; exact hCpos _
              rw [e]
              refine (convex_convexHull ℝ _) (subset_convexHull ℝ (Set.range fun j : Fin (i+1+1) => X j) ⟨Fin.last (i+1), rfl⟩)
                (convexHull_mono ?_ ih) (inv_nonneg.mpr hpos1.le)
                (mul_nonneg (inv_nonneg.mpr hpos1.le) (mul_nonneg (hβnn i) (hCpos i).le)) ?_
              · rintro _ ⟨j, rfl⟩; exact ⟨Fin.castSucc j, rfl⟩
              · field_simp
          · intro i
            refine ⟨hE i, ?_⟩
            rw [hE i, ← hCRP i]
            by_cases h0 : R i ⬝ᵥ R i = 0
            · rw [h0]; simp
            · have := hCne i
              field_simp
          · intro i
            have := hdiff i
            have h1 : 0 ≤ (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) / C (i + 1) :=
              div_nonneg (hself _) (hCpos _).le
            linarith
          · intro i hi
            have := hdiff i
            have hr : 0 < R i ⬝ᵥ R i := hN i (by omega)
            have h1 : 0 < (k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i) / C (i + 1) := by
              rw [hE i]; exact div_pos (div_pos hr (hCpos i)) (hCpos _)
            linarith
