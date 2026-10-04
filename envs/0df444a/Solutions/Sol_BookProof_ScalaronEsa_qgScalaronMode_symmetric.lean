-- Prove2me | solution 1 for BookProof.ScalaronEsa.qgScalaronMode_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:50:20.471031+00:00
-- url     : https://prove2.me/submissions/a32ba924-95b0-4bba-9c23-5f9c7aa4b9f2

import Mathlib
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQuantumGravityDensitized

set_option autoImplicit false

open BookProof.FarisLavine in
theorem mulHamiltonian_symm_9aba (lam : ℕ → ℝ) :
    SymmetricOn (mulSymbolDomain lam) (mulHamiltonian lam) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  simp only [mulHamiltonian, mulSymbolOp, LinearMap.coe_mk, AddHom.coe_mk, mulSymbolFun,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

open BookProof.FarisLavine BookProof.QuantumGravityDensitized BookProof.ScalaronEsa in
theorem solution (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ) :
    SymmetricOn (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) := by
  exact mulHamiltonian_symm_9aba _
