-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_6_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:21.385567+00:00
-- url     : https://prove2.me/submissions/e623b5cc-5476-4a46-a8f8-eb496aa5245d

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:7 (Hestenes–Stiefel 1952, p. 417): the gradient of `f` at `xᵢ` in the plane `πᵢ`
(the vector of the direction space `conjDir A p i` of `πᵢ` representing the derivative of `f`
at `xᵢ` on that space) is a scalar multiple `c pᵢ` of `pᵢ`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    ∃ c : ℝ, c • (cgIter A k x₀ i).p ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i ∧
      ∀ v ∈ conjDir A (fun j => (cgIter A k x₀ j).p) i,
        fderiv ℝ (errorFun A h) (cgIter A k x₀ i).x v = c * ((cgIter A k x₀ i).p ⬝ᵥ v) := by
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
          have hself : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
            Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
          have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
          have hfd : ∀ x v : Fin n → ℝ, fderiv ℝ (errorFun A h) x v =
              -(v ⬝ᵥ (A *ᵥ (h - x)) + (h - x) ⬝ᵥ (A *ᵥ v)) := by
            intro x v
            have hd : DifferentiableAt ℝ (errorFun A h) x := by
              unfold errorFun
              simp only [dotProduct, Matrix.mulVec]
              fun_prop
            have hin : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
              simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
            have hd' : HasFDerivAt (errorFun A h) (fderiv ℝ (errorFun A h) x) (x + (0:ℝ) • v) := by
              simpa using hd.hasFDerivAt
            have h1 : HasDerivAt (fun t : ℝ => errorFun A h (x + t • v)) (fderiv ℝ (errorFun A h) x v) 0 :=
              HasFDerivAt.comp_hasDerivAt (l := errorFun A h) (f := fun t : ℝ => x + t • v) (0:ℝ) hd' hin
            have e : (fun t : ℝ => errorFun A h (x + t • v)) = fun t =>
                (h - x) ⬝ᵥ (A *ᵥ (h - x)) - t * (v ⬝ᵥ (A *ᵥ (h - x)) + (h - x) ⬝ᵥ (A *ᵥ v))
                  + t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
              funext t
              have : h - (x + t • v) = (h - x) - t • v := by abel
              simp only [errorFun, this, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
                dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
              ring
            have h2 : HasDerivAt (fun t : ℝ => errorFun A h (x + t • v))
                (-(v ⬝ᵥ (A *ᵥ (h - x)) + (h - x) ⬝ᵥ (A *ᵥ v))) 0 := by
              rw [e]
              have := ((((hasDerivAt_id' (0:ℝ)).mul_const (v ⬝ᵥ (A *ᵥ (h - x)) + (h - x) ⬝ᵥ (A *ᵥ v))).const_sub
                ((h - x) ⬝ᵥ (A *ᵥ (h - x)))).add ((hasDerivAt_pow 2 (0:ℝ)).mul_const (v ⬝ᵥ (A *ᵥ v))))
              exact this.congr_deriv (by norm_num)
            exact h1.unique h2
          suffices key : ∀ (X R P : ℕ → (Fin n → ℝ)) (α β : ℕ → ℝ),
              X 0 = x₀ → R 0 = k - A *ᵥ X 0 → P 0 = R 0 →
              (∀ i, α i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
              (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
              (∀ i, X (i+1) = X i + α i • P i) →
              (∀ i, R (i+1) = R i - α i • (A *ᵥ P i)) →
              (∀ i, P (i+1) = R (i+1) + β i • P i) →
            ∃ c : ℝ, c • P i ∈ conjDir A P i ∧
              ∀ v ∈ conjDir A P i, fderiv ℝ (errorFun A h) (X i) v = c * (P i ⬝ᵥ v) by
            exact key (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
              (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
              (fun i => (cgIter A k x₀ (i+1)).r ⬝ᵥ (cgIter A k x₀ (i+1)).r /
                ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r))
              rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          intro X R P α β hX0 hR0 hP0 hα hβ hX hRs hPs
          have hRX : ∀ i, R i = k - A *ᵥ X i := by
            intro i
            induction i with
            | zero => exact hR0
            | succ i ih =>
              rw [hRs, hX, ih, Matrix.mulVec_add, Matrix.mulVec_smul]; abel
          have hAE : ∀ i, A *ᵥ (h - X i) = R i := by
            intro i; rw [Matrix.mulVec_sub, hh, hRX]
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
          have hmem : ∀ v, v ∈ conjDir A P i ↔ ∀ j < i, (A *ᵥ P j) ⬝ᵥ v = 0 := by
            intro v
            simp only [conjDir, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Matrix.mulVec,
              Pi.zero_apply]
            constructor
            · intro H j hj
              have := H ⟨j, hj⟩
              simpa [dotProduct, Matrix.mulVec] using this
            · intro H j
              have := H j j.2
              simpa [dotProduct, Matrix.mulVec] using this
          have hβnn : ∀ j, 0 ≤ β j := fun j => by rw [hβ]; exact div_nonneg (hself _) (hself _)
          have hG : ∀ i, ∃ γ : ℝ, 1 ≤ γ ∧ ∀ v, (∀ j < i, (A *ᵥ P j) ⬝ᵥ v = 0) →
              P i ⬝ᵥ v = γ * (R i ⬝ᵥ v) := by
            intro i
            induction i with
            | zero => exact ⟨1, le_rfl, fun v _ => by rw [hP0]; ring⟩
            | succ i ih =>
              obtain ⟨γ, hγ, hv⟩ := ih
              refine ⟨1 + β i * γ, by nlinarith [hβnn i], fun v hvj => ?_⟩
              have h1 := hv v (fun j hj => hvj j (by omega))
              have h2 : R i ⬝ᵥ v = R (i+1) ⬝ᵥ v := by
                rw [hRs, sub_dotProduct, smul_dotProduct, hvj i (by omega)]; simp
              rw [hPs, add_dotProduct, smul_dotProduct, h1, ← h2, smul_eq_mul]
              ring
          obtain ⟨γ, hγ, hv⟩ := hG i
          refine ⟨-2 / γ, ?_, ?_⟩
          · rw [hmem]
            intro j hj
            rw [dotProduct_smul, dotProduct_comm, ((hQ i).1 j hj).2.2]; simp
          · intro v hvm
            rw [hmem] at hvm
            rw [hfd, hv v hvm, hAE, ← hsym, hAE, dotProduct_comm v]
            field_simp
            ring
