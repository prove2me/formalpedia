-- Prove2me | solution 1 for Formalism.L2.Th1.H.semicharacterHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:30.92634+00:00
-- url     : https://prove2.me/submissions/a0aef2ac-77ec-48b1-8c46-2ac561bc092a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergMul
import Theorems.Thm_Formalism_L2_Th1_H_semicharacterBasic

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
theorem _root_.solution : SemiHom := by
  intro V _ _ H hH Λ α hα x hx y hy F z
  have hU : opU H x (fun v => α y * opU H y F v) z = α y * opU H x (opU H y F) z := by
    simp only [opU]; ring
  have hd : x ∈ dualLat H Λ := (semicharacterBasic V H hH Λ α hα).2.2 hx
  obtain ⟨m, hm⟩ := (show ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ) from hd) y hy
  have hexp : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    rw [hm]
    push_cast
    ring
  rw [hU, heisenbergMul V H hH x y F z, hα.2 x hx y hy, hexp]
  ring
end Formalism.L2.Th1.H
