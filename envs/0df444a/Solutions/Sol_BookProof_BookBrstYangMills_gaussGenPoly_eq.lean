-- Prove2me | solution 1 for BookProof.BookBrstYangMills.gaussGenPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T06:20:46.883991+00:00
-- url     : https://prove2.me/submissions/b328ad43-54da-4166-85ce-d88563cc2266

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.gaussGenPoly_eq
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_gaussDer_apply
import Theorems.Thm_BookProof_BookBrstYangMills_pderiv_X_mul
import Theorems.Thm_BookProof_BookBrstYangMills_AfieldPoly_apply
import Theorems.Thm_BookProof_BookBrstYangMills_momPoly_apply
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin N) :
    gaussGenPoly G c = (-Complex.I) •
      ((∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.momPoly μ a)
        - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.momPoly μ a * AfieldPoly μ b))) := by

  classical
  refine LinearMap.ext fun p => ?_
  have hL : gaussGenPoly G c p = ∑ μ, ∑ a, gaussVec G c (μ, a) * pderiv (μ, a) p := by
    have h0 : gaussGenPoly G c p = gaussDer G c p := rfl
    rw [h0, gaussDer_apply]
    exact Fintype.sum_prod_type _
  have hterm : ∀ (μ : Fin 4) (a : Fin N),
      gaussVec G c (μ, a) * pderiv (μ, a) p
        = (-Complex.I) • ((((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.momPoly μ a) p
            - ∑ b, (((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.momPoly μ a * AfieldPoly μ b)) p) := by
    intro μ a
    have hb : ∀ b : Fin N,
        (((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.momPoly μ a * AfieldPoly μ b)) p
          = ((G.f a b c : ℝ) : ℂ) • ((-Complex.I) •
              ((if (μ, a) = (μ, b) then p else 0) + X (μ, b) * pderiv (μ, a) p)) := by
      intro b
      simp only [LinearMap.smul_apply, Module.End.mul_apply, AfieldPoly_apply, momPoly_apply,
        pderiv_X_mul]
    have hdiag : ((G.f a a c : ℝ) : ℂ) = 0 := by
      have : G.f a a c = 0 := by
        have h := G.antisymm a a c
        linarith
      rw [this]
      simp
    have hsum : (∑ b, (((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.momPoly μ a * AfieldPoly μ b)) p)
        = ∑ b, ((G.f a b c : ℝ) : ℂ) • ((-Complex.I) • (X (μ, b) * pderiv (μ, a) p)) := by
      rw [Finset.sum_congr rfl fun b _ => hb b]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h : a = b
      · subst h
        rw [hdiag]
        simp
      · have h' : ¬ ((μ, a) = (μ, b)) := by
          intro hc
          exact h (congrArg Prod.snd hc)
        rw [if_neg h']
        simp
    rw [hsum]
    simp only [LinearMap.smul_apply, momPoly_apply, gaussVec, vecComb, smul_smul]
    rw [add_mul, Finset.sum_mul]
    simp only [smul_mul_assoc, one_mul, Complex.ofReal_neg]
    rw [smul_sub, Finset.smul_sum]
    have hIz : ∀ z : ℂ, -Complex.I * (z * -Complex.I) = -z := fun z => by
      linear_combination z * Complex.I_sq
    have hx : ∀ x : Fin N,
        (-Complex.I) • ((((G.f a x c : ℝ) : ℂ) * -Complex.I) • (X (μ, x) * pderiv (μ, a) p))
          = -((((G.f a x c : ℝ) : ℂ)) • (X (μ, x) * pderiv (μ, a) p)) := by
      intro x
      rw [smul_smul, hIz, neg_smul]
    have hd0 : (-Complex.I) • ((((G.D μ c a : ℝ) : ℂ) * -Complex.I) • (pderiv (μ, a) p))
        = -((((G.D μ c a : ℝ) : ℂ)) • (pderiv (μ, a) p)) := by
      rw [smul_smul, hIz, neg_smul]
    rw [hd0, Finset.sum_congr rfl fun x _ => hx x, Finset.sum_neg_distrib, sub_neg_eq_add,
      neg_smul]
  have hR : ((-Complex.I) •
      ((∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.momPoly μ a)
        - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.momPoly μ a * AfieldPoly μ b)))) p
      = ∑ μ, ∑ a, (-Complex.I) • ((((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.momPoly μ a) p
          - ∑ b, (((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.momPoly μ a * AfieldPoly μ b)) p) := by
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sum_apply, smul_sub,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a _ => hterm μ a
