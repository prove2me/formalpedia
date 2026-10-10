-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.uField2_pderiv_uD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:25.668843+00:00
-- url     : https://prove2.me/submissions/7e3db1c1-5180-4f62-90cd-b24758da6491

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.uField2_pderiv_uD
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (m k i : Fin 3) :
    pderiv (NSVar.uD m k) (uField2 i) = if m = i then X (NSVar.y k) else 0 := by

  have h1 : pderiv (NSVar.uD m k) (X (NSVar.u i) : NSAlg) = 0 := by simp [pderiv_X]
  have h3 : ∀ l : Fin 3,
      pderiv (NSVar.uD m k) (X (NSVar.uL i) * (X (NSVar.y l) * X (NSVar.y l)) : NSAlg) = 0 := by
    intro l; rw [pderiv_mul, pderiv_mul]; simp [pderiv_X]
  by_cases hm : m = i
  · subst hm
    have h2 : ∀ l : Fin 3, pderiv (NSVar.uD m k) (X (NSVar.uD m l) * X (NSVar.y l) : NSAlg)
        = if k = l then X (NSVar.y l) else 0 := by
      intro l; rw [pderiv_mul]
      by_cases hl : k = l
      · subst hl; simp [pderiv_X]
      · simp [pderiv_X, hl, Ne.symm hl]
    rw [uField2, map_add, map_add, h1, map_sum, MvPolynomial.pderiv_C_mul, map_sum,
      Finset.sum_eq_zero (fun l _ => h3 l), Finset.sum_congr rfl (fun l _ => h2 l),
      Finset.sum_ite_eq Finset.univ k (fun l => X (NSVar.y l)), if_pos (Finset.mem_univ k)]
    simp
  · have h2 : ∀ l : Fin 3, pderiv (NSVar.uD m k) (X (NSVar.uD i l) * X (NSVar.y l) : NSAlg)
        = 0 := by
      intro l; rw [pderiv_mul]
      simp [pderiv_X, hm]
    rw [uField2, map_add, map_add, h1, map_sum, MvPolynomial.pderiv_C_mul, map_sum,
      Finset.sum_eq_zero (fun l _ => h3 l), Finset.sum_eq_zero (fun l _ => h2 l)]
    simp [hm]
