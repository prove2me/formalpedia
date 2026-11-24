-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:46.205933+00:00
-- url     : https://prove2.me/submissions/288d918c-29ef-4878-863b-4732a3aecb9f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_hasFDerivAt_star_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_hasFDerivAt_inv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j : Fin 6) (v : Fin m → ℂ) :
    fderiv ℝ (coef k j) x v =
      if (j : ℕ) < 3 then ck k j x * v k else ck k j x * star (v k) := by
  have hxk : x k ≠ 0 := hx k
  match j with
  | 0 =>
    show fderiv ℝ (fun y : Fin m → ℂ => y k) x v = _
    rw [(hasFDerivAt_apply (𝕜 := ℝ) k x).fderiv]
    simp [ck]
  | 1 =>
    show fderiv ℝ (fun y : Fin m → ℂ => y k) x v = _
    rw [(hasFDerivAt_apply (𝕜 := ℝ) k x).fderiv]
    simp [ck]
  | 2 =>
    show fderiv ℝ (fun y : Fin m → ℂ => (y k)⁻¹) x v = _
    rw [(hasFDerivAt_inv_apply k hxk).fderiv]
    simp [ck, mul_comm]
  | 3 =>
    show fderiv ℝ (fun y : Fin m → ℂ => star (y k)) x v = _
    rw [(hasFDerivAt_star_apply k x).fderiv]
    simp [ck]
  | 4 =>
    show fderiv ℝ (fun y : Fin m → ℂ => star (y k)) x v = _
    rw [(hasFDerivAt_star_apply k x).fderiv]
    simp [ck]
  | 5 =>
    show fderiv ℝ (fun y : Fin m → ℂ => (star (y k))⁻¹) x v = _
    have hs : star (x k) ≠ 0 := star_ne_zero.mpr hxk
    have h5 : HasFDerivAt (fun y : Fin m → ℂ => (star (y k))⁻¹)
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(star (x k) ^ 2)⁻¹)).restrictScalars ℝ).comp
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) k))) x :=
      ((hasDerivAt_inv hs).hasFDerivAt.restrictScalars ℝ).comp x (hasFDerivAt_star_apply k x)
    rw [h5.fderiv]
    simp [ck, mul_comm]
end Formalism.QuantumDeterminants.WirtingerDerivatives
