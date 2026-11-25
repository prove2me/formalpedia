-- Prove2me | solution 1 for Formalism.L2.Th1.H.entries_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:49:52.904941+00:00
-- url     : https://prove2.me/submissions/d5b421ef-305a-4e73-b7b5-c0ca2c30f5c9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
import Theorems.Thm_Formalism_L2_Th1_H_cmL_mul_mem
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat


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
theorem _root_.solution (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    {m : Type*} [Fintype m] [DecidableEq m] (f : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (hf : ∀ w w', InK d (f (Pi.single w' 1) w)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ stdLat (cmL a b d ha hd lam hlam) m, N • f x ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  choose Nf hNf hmem using fun p : m × m => cmL_mul_mem a b d ha hd lam hlam _ (hf p.1 p.2)
  refine ⟨∏ p, Nf p, Finset.prod_pos fun p _ => hNf p, fun x hx => ?_⟩
  rw [mem_stdLat] at hx ⊢
  intro w
  have hfx : f x w = ∑ w', x w' * f (Pi.single w' 1) w := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [show (Pi.single w' (x w') : m → ℂ) = x w' • (Pi.single w' (1 : ℂ) : m → ℂ) by
      ext j; simp [Pi.single_apply]]
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  show (∏ p, Nf p) • f x w ∈ _
  rw [hfx, Finset.smul_sum]
  refine Submodule.sum_mem _ fun w' _ => ?_
  have h1 := hmem (w, w') (x w') (hx w')
  obtain ⟨r, hr⟩ : Nf (w, w') ∣ ∏ p, Nf p := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  rw [hr]
  have hre : (Nf (w, w') * r) • (x w' * f (Pi.single w' 1) w)
      = r • ((Nf (w, w') : ℂ) * f (Pi.single w' 1) w * x w') := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hre]
  exact nsmul_mem h1 r
end Formalism.L2.Th1.H
