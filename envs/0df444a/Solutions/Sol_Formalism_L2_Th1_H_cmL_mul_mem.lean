-- Prove2me | solution 1 for Formalism.L2.Th1.H.cmL_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:37.153588+00:00
-- url     : https://prove2.me/submissions/f3099989-859d-484f-8ef9-69cbabb9f798

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
import Theorems.Thm_Formalism_L2_Th1_H_cmPair_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (k : ℂ)
    (hk : InK d k) : ∃ N : ℕ, 0 < N ∧ ∀ z ∈ (cmL a b d ha hd lam hlam).lattice,
      (N : ℂ) * k * z ∈ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨N, hN, hmul⟩ := cmPair_mul_mem a b d ha hd k hk
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  have h0 : ((m : ℂ) * (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₁ + n * (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₂)
      ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice :=
    PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩
  obtain ⟨m', n', hmn⟩ := PeriodPair.mem_lattice.1 (hmul _ h0)
  rw [PeriodPair.mem_lattice]
  refine ⟨m', n', ?_⟩
  simp only [cmL, Formalism.L2.Th1.F.scalePair]
  linear_combination lam * hmn
end Formalism.L2.Th1.H
