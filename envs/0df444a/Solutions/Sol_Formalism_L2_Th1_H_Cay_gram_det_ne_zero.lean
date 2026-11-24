-- Prove2me | solution 1 for Formalism.L2.Th1.H.Cay.gram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:19.121882+00:00
-- url     : https://prove2.me/submissions/56a6888a-675f-43ab-9186-17ab1f01982b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf

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
open Formalism.L2.Th1.H.Cay
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.Th1.H.Cay
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (H : Sesq V) (hpos : IsPosDef H)
    (e : Module.Basis ι ℂ V) : (Matrix.of fun i j => H (e i) (e j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hHw : H (∑ i, v i • e i) = 0 := by
    apply e.ext
    intro j
    have h := congrFun hM j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    exact h
  have hw0 : (∑ i, v i • e i) ≠ 0 := by
    intro h0
    exact hv (funext fun i => Fintype.linearIndependent_iff.1 e.linearIndependent v h0 i)
  have h := hpos _ hw0
  rw [hHw, LinearMap.zero_apply, Complex.zero_re] at h
  exact lt_irrefl _ h
end Formalism.L2.Th1.H.Cay
