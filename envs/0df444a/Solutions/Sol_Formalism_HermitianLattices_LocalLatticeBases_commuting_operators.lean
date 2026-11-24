-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.commuting_operators
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:44.246587+00:00
-- url     : https://prove2.me/submissions/7fa351fc-d907-4542-85ff-adf61beac648

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : HeckeProductCommutation := by
  intro R _ M _ _ U K c h
  have A : ∀ j p, (K j).comp ((U j) ^ p) = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp (K j) := by
    intro j p
    induction p with
    | zero => ext; simp
    | succ p ih =>
      have h' : (K j).comp (U j) = (((c j)⁻¹ : Rˣ) : R) • (U (j+1)).comp (K j) := by
        rw [h j, smul_smul]; simp
      calc (K j).comp ((U j) ^ (p+1)) = ((K j).comp ((U j)^p)).comp (U j) := by rw [pow_succ]; rfl
        _ = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp ((K j).comp (U j)) := by rw [ih]; rfl
        _ = _ := by
          rw [h', LinearMap.comp_smul, smul_smul, pow_succ, pow_succ]; push_cast; rfl
  have B : ∀ m p, (chainK R M K m).comp ((U 0) ^ (m + p)) =
      ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + p) : Rˣ) : R) • ((U m) ^ p).comp (chainUK R M U K m) := by
    intro m
    induction m with
    | zero => intro p; ext; simp [chainK, chainUK]
    | succ m ih =>
      intro p
      have e0 : m + 1 + p = m + (p + 1) := by ring
      have e1 : ∏ j ∈ range (m+1), (c j)⁻¹ ^ (m + 1 - j + p) =
          (∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1))) * (c m)⁻¹ ^ (p+1) := by
        rw [Finset.prod_range_succ]
        congr 1
        · apply Finset.prod_congr rfl
          intro j hj
          have := Finset.mem_range.mp hj
          congr 1; omega
        · congr 1; omega
      calc (chainK R M K (m+1)).comp ((U 0) ^ (m + 1 + p))
          = (K m).comp ((chainK R M K m).comp ((U 0) ^ (m + (p+1)))) := by rw [e0]; rfl
        _ = ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1)) : Rˣ) : R) •
              ((K m).comp ((U m) ^ (p+1))).comp (chainUK R M U K m) := by
            rw [ih (p+1), LinearMap.comp_smul]; rfl
        _ = _ := by
            rw [A m (p+1), e1, LinearMap.smul_comp, smul_smul, pow_succ ((U (m+1)))]; push_cast; rfl
  intro m
  have := B m 0
  simp only [add_zero, pow_zero] at this
  rw [this]; rfl
end Formalism.HermitianLattices.LocalLatticeBases
