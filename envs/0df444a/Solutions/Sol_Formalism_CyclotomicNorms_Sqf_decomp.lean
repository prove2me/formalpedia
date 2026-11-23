-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:27.753268+00:00
-- url     : https://prove2.me/submissions/049b373b-9719-465b-b5da-adf974edbb4b

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]
namespace Formalism.CyclotomicNorms.Sqf
theorem _root_.solution (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) (hsq : ¬ Squarefree f) :
    ∃ P h : K[X], P.Monic ∧ h.Monic ∧ 1 ≤ P.natDegree ∧ P.coeff 0 ≠ 0 ∧ f = P * P * h := by
  unfold Squarefree at hsq
  push_neg at hsq
  obtain ⟨x, ⟨g, hg⟩, hx⟩ := hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hg)
  have hc : x.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hx0
  have hP : (x * C x.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hx0
  have hu : C x.leadingCoeff⁻¹ * C x.leadingCoeff = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have key : f = (x * C x.leadingCoeff⁻¹) * (x * C x.leadingCoeff⁻¹) *
      (C x.leadingCoeff * C x.leadingCoeff * g) := by
    rw [hg]
    linear_combination (-(x * x * g * (C x.leadingCoeff⁻¹ * C x.leadingCoeff + 1))) * hu
  refine ⟨x * C x.leadingCoeff⁻¹, C x.leadingCoeff * C x.leadingCoeff * g, hP,
    Monic.of_mul_monic_left (hP.mul hP) (by rw [← key]; exact hf), ?_, ?_, key⟩
  · by_contra hlt
    push_neg at hlt
    have h1 : x * C x.leadingCoeff⁻¹ = 1 := (Monic.natDegree_eq_zero hP).mp (by omega)
    exact hx (isUnit_iff_exists_inv.mpr ⟨_, h1⟩)
  · intro hz
    apply h0
    rw [key, mul_coeff_zero, mul_coeff_zero, hz]
    simp
end Formalism.CyclotomicNorms.Sqf
