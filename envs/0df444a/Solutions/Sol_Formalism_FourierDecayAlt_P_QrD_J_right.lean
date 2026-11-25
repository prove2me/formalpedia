-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.J_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:53:03.188834+00:00
-- url     : https://prove2.me/submissions/439bf67f-6527-4c23-adfc-f0dccf51e5b1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg 1 h1z h hh
  rw [one_mul, mul_one, hπ'.1] at e1
  have e1' : π 1 ∘SL J g = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [one_mul] at e2
  rw [e2, ← ContinuousLinearMap.comp_assoc, e1']
end Formalism.FourierDecayAlt.P.QrD
