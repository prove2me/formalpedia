-- Prove2me | solution 1 for BookProof.BookBrstYangMills.gauss_field_identity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:29:01.47274+00:00
-- url     : https://prove2.me/submissions/8a07d879-4056-466f-9034-1072a782d6cd

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.gauss_field_identity
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_strProd_symm
import Theorems.Thm_BookProof_BookBrstYangMills_strProd_swap12
import Theorems.Thm_BookProof_BookBrstYangMills_strProd_swap34
import Theorems.Thm_BookProof_BookBrstYangMills_strProd_jacobi
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (a c e g : Fin N) :
    (∑ b, G.f a b e * G.f b g c) - (∑ b, G.f a b c * G.f b g e)
      = ∑ h, G.f c e h * G.f a g h := by

  have t1 : (∑ b, G.f a b e * G.f b g c) = strProd G e a g c := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [G.cyclic a b e, G.cyclic b e a, G.cyclic b g c]
  have t2 : (∑ b, G.f a b c * G.f b g e) = strProd G c a g e := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [G.cyclic a b c, G.cyclic b c a, G.cyclic b g e]
  have t3 : (∑ h, G.f c e h * G.f a g h) = strProd G c e a g := rfl
  rw [t1, t2, t3]
  have J1 := strProd_jacobi G e a g c
  have J2 := strProd_jacobi G c a g e
  have J3 := strProd_jacobi G a c g e
  have r1 : strProd G a g e c = -strProd G a g c e := strProd_swap34 G a g e c
  have r2 : strProd G g e a c = strProd G a c g e := strProd_symm G g e a c
  have r3 : strProd G g c a e = -strProd G c g a e := strProd_swap12 G g c a e
  have r4 : strProd G g a c e = -strProd G a g c e := strProd_swap12 G g a c e
  have r5 : strProd G c e a g = strProd G a g c e := strProd_symm G c e a g
  rw [r5]
  linarith [J1, J2, J3, r1, r2, r3, r4]
