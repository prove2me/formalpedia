-- Prove2me | solution 1 for Formalism.L2.Th1.H.taylorMv_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:28.955885+00:00
-- url     : https://prove2.me/submissions/4c55d7b8-bdcd-473f-a279-8a167914db38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_Formalism_L2_Th1_H_cntVec_apply

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) (k : ℕ) (ν : n →₀ ℕ)
    (h : ν.degree = k) :
    MvPowerSeries.coeff ν (taylorMv F) = ((k.factorial : ℕ) : ℂ)⁻¹ *
      ∑ f : Fin k → n with cntVec f = ν, iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by
  subst h
  change ((ν.degree.factorial : ℕ) : ℂ)⁻¹ * _ = _
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; ext i; exact h i
  · intro h i; exact (cntVec_apply f i).symm.trans (DFunLike.congr_fun h i)
end Formalism.L2.Th1.H
