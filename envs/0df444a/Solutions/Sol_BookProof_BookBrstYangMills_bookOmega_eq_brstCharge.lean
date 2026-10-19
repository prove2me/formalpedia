-- Prove2me | solution 1 for BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:38:28.742847+00:00
-- url     : https://prove2.me/submissions/68324079-7379-4c70-838b-3fe6b1b059e3

import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_BookBrstYangMills_I_smul_gaussGen
import Theorems.Thm_BookProof_BookBrstYangMills_rsmul_eq_csmul
-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
open BookProof.BRSTNilpotent
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.YangMillsGhost
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)
theorem h44_bookOmega_eq {N : ℕ} (G : BookProof.BookBrstYangMills.GaugeAlgebra N) :
    BookProof.BookBrstYangMills.bookOmega G = Complex.I • BookProof.QuantumGravityBrstCharge.brstCharge G.f
      (BookProof.BookBrstYangMills.gaussGen G) BookProof.BookBrstYangMills.chiOp
      BookProof.BookBrstYangMills.betaOp := by
  have P1 : (∑ μ, ∑ a, BookProof.BookBrstYangMills.mom μ a * dChi G μ a)
      = ∑ c, (∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.mom μ a) * chiOp c := by
    unfold dChi
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, BookProof.BookBrstYangMills.rsmul_eq_csmul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    conv_rhs => rw [Finset.sum_comm]
  have P2 : (∑ μ, ∑ a, ∑ b, ∑ c, (G.f a b c) • (BookProof.BookBrstYangMills.mom μ a * Afield μ b * chiOp c))
      = ∑ c, (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.mom μ a * Afield μ b)) * chiOp c := by
    simp only [Finset.sum_mul, smul_mul_assoc, BookProof.BookBrstYangMills.rsmul_eq_csmul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
  have P3 : ∀ C : Module.End ℂ (BookState N), Complex.I • ((1 / 2 : ℝ) • C) = (Complex.I / 2) • C := by
    intro C
    rw [BookProof.BookBrstYangMills.rsmul_eq_csmul, smul_smul]; congr 1; push_cast; ring
  unfold bookOmega brstCharge glin Q
  rw [P1, P2, smul_sub, P3, Finset.smul_sum (s := Finset.univ) (f := fun a => gaussGen G a * chiOp a)]
  have h4 : ∀ a, Complex.I • (gaussGen G a * chiOp a) = (Complex.I • gaussGen G a) * chiOp a :=
    fun a => (smul_mul_assoc _ _ _).symm
  simp only [h4, I_smul_gaussGen]
  congr 1
  have h5 : ∀ c, (∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.mom μ a -
      ∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.mom μ a * Afield μ b)) * chiOp c
      = (∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • BookProof.BookBrstYangMills.mom μ a) * chiOp c -
      (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (BookProof.BookBrstYangMills.mom μ a * Afield μ b)) * chiOp c :=
    fun c => LinearMap.ext fun x => rfl
  rw [Finset.sum_congr rfl (fun c _ => h5 c)]
  exact (Finset.sum_sub_distrib (G := Module.End ℂ (BookState N)) _ _).symm

theorem solution :
    bookOmega G = Complex.I • brstCharge G.f (gaussGen G) chiOp betaOp := by
  exact h44_bookOmega_eq G

