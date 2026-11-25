-- Prove2me | solution 1 for Formalism.L2.Th1.H.ThStd_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:23.529037+00:00
-- url     : https://prove2.me/submissions/64e8685c-25ca-4789-a56d-9203b75d6c38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_th_split
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key


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
theorem _root_.solution : ThStd := by
  intro L ω₀ n _ _ h0 hh α hα G hG
  have key : ∀ (s : Finset n) (z : n → ℂ),
      G z = (∏ i ∈ s, Formalism.L2.Th1.F.th0 L (ω₀ / 2) (z i)) * G (fun j => if j ∈ s then 0 else z j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro z; simp
    | insert i s hi ih =>
      intro z
      rw [ih z, th_split L ω₀ n h0 hh α hα G hG (fun j => if j ∈ s then 0 else z j) i,
        Finset.prod_insert hi]
      have h1 : Function.update (fun j => if j ∈ s then 0 else z j) i 0
          = fun j => if j ∈ insert i s then 0 else z j := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Finset.mem_insert, hj]
      rw [h1]
      simp only [hi, if_false]
      ring
  funext z
  have h := key Finset.univ z
  simp only [Finset.mem_univ, if_true] at h
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul, F0, prodFn]
  rw [mul_comm]
  rfl
end Formalism.L2.Th1.H
