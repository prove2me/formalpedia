-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.monic_extract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:12.851268+00:00
-- url     : https://prove2.me/submissions/394e45fb-611e-46bb-8992-62f80c5402d8

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_lead_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_evR_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (ev : M →ₗ[ℂ] V) (n : ℕ) (A₀ : R[X])
    (hA : A₀.Monic) (hn : A₀.natDegree = n) (y : Fin (n + 1) → ℝ) (hy : Function.Injective y)
    (x : M) : ∑ i, ((lagCo y i : ℝ) : ℂ) • ev (evR A₀ (y i) • x) = ev x := by
  have hc1 : A₀.coeff n = 1 := by
    rw [← hn]
    exact hA.coeff_natDegree
  have h := lead_c n y hy (fun k : Fin (n + 1) => ev (A₀.coeff k • x))
  simp only [Fin.val_last, hc1, one_smul] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [evR_smul A₀ n hn.le (y i) x, map_sum, Finset.sum_range]
  simp only [map_smul]
end Formalism.FourierDecayAlt.P.WordMonicExtraction
