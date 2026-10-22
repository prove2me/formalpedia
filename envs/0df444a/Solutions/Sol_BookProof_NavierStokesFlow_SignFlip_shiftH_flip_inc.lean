-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.shiftH_flip_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:21:40.359146+00:00
-- url     : https://prove2.me/submissions/2ea5046c-b706-483c-827e-856bb5d4d20e

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.shiftH_flip_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
open BookProof.NavierStokesFlow.ShiftHamiltonian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (S : ShiftData ι) (p : ι → ℕ) (k : ℕ)
    (hp : ∀ β, p (S.shift β) = p β + k) (x : maxDom S.sym) :
    (flipU p (ShiftData.shiftH S x) : L2I ι)
      = (-1 : ℂ) ^ k • (ShiftData.shiftH S ⟨flipU p (x : L2I ι),
          flipU_mem_maxDom p S.sym x.2⟩ : L2I ι) := by

  refine lp.ext (funext fun β => ?_)
  have hX : ((⟨flipU p (x : L2I ι), flipU_mem_maxDom p S.sym x.2⟩ :
      maxDom S.sym) : L2I ι) = flipU p (x : L2I ι) := rfl
  simp only [flipU_coe, ShiftData.shiftH_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hfun : ((flipU p (x : L2I ι) : L2I ι) : ι → ℂ) = flipFun p ((x : L2I ι) : ι → ℂ) := rfl
  rw [hfun, hFun_flip S p k hp]
  rcases negOne_pow_eq k with hB | hB <;> rw [hB] <;> ring
