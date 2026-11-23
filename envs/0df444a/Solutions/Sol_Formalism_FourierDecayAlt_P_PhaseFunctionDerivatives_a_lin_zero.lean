-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_lin_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:18.504264+00:00
-- url     : https://prove2.me/submissions/5aabb034-8654-4af4-9105-3044274374fd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (x : Fin n → ℂ) :
    iteratedFDeriv ℂ (j + 1) (fun x : Fin n → ℂ => ∑ k, x k) x = 0 := by
  obtain ⟨L, hL⟩ : ∃ L : (Fin n → ℂ) →L[ℂ] ℂ, L = ∑ k, ContinuousLinearMap.proj k := ⟨_, rfl⟩
  have h : (fun x : Fin n → ℂ => ∑ k, x k) = L := by
    funext y; rw [hL]; simp
  rw [h, iteratedFDeriv_succ_eq_comp_right]
  have h2 : (fun y => fderiv ℂ (L : (Fin n → ℂ) → ℂ) y) = fun _ => L := by
    funext y; exact L.fderiv
  rw [h2, Function.comp_apply, iteratedFDeriv_const_of_ne (by omega)]
  simp
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
