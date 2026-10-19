-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genX_genY_commute
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:39:25.780085+00:00
-- url     : https://prove2.me/submissions/159e09f9-9d40-4d38-b317-95c0b8a004b3

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genX_genY_commute
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow
noncomputable def h43_DY (k : Fin 3) : Derivation ℂ NSAlg NSAlg :=
  MvPolynomial.pderiv (NSVar.y k)
    - ((MvPolynomial.X (NSVar.uD 0 k) : NSAlg) • MvPolynomial.pderiv (NSVar.u 0)
      + (MvPolynomial.X (NSVar.uD 1 k) : NSAlg) • MvPolynomial.pderiv (NSVar.u 1)
      + (MvPolynomial.X (NSVar.uD 2 k) : NSAlg) • MvPolynomial.pderiv (NSVar.u 2))

theorem h43_DY_eq (k : Fin 3) : (h43_DY k : Module.End ℂ NSAlg) = genY k := by
  apply LinearMap.ext; intro p
  simp [h43_DY, genY, Fin.sum_univ_three, Derivation.sub_apply, smul_eq_mul]

theorem solution (j k : Fin 3) : ⁅genX j, genY k⁆ = 0 := by
  rw [← h43_DY_eq, show genX j = ((pderiv (NSVar.x j) : Derivation ℂ NSAlg NSAlg) : Module.End ℂ NSAlg) from rfl,
    ← Derivation.commutator_coe_linear_map]
  have : ⁅(pderiv (NSVar.x j) : Derivation ℂ NSAlg NSAlg), h43_DY k⁆ = 0 := by
    apply MvPolynomial.derivation_ext; intro v
    rw [Derivation.commutator_apply]
    cases v <;> simp [h43_DY, pderiv_X, Pi.single_apply, smul_eq_mul] <;> split_ifs <;>
      simp [pderiv_X, Pi.single_apply]
  rw [this]; rfl

