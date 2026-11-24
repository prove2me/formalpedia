-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.rdV_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:10.683478+00:00
-- url     : https://prove2.me/submissions/3570d378-783a-4e8a-bfa6-8fd828e10d8d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_exp_uh
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hasDerivAt_phase
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_one
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_exp_S
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_inS_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_memN_S
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (X : Mx k r) (hS : InS k r l (g * X * g⁻¹))
    (hk : Hpk k r * (g * X * g⁻¹)ᴴ * Hpk k r = -(g * X * g⁻¹)) :
    RdV X f g = (Complex.I * (((cStd * ell k r z (g * X * g⁻¹)).re : ℝ) : ℂ)) • f g := by
  have ell_sm : ∀ (c : ℂ) (M : Mx k r), ell k r z (c • M) = c * ell k r z M := by
    intro c M
    simp only [ell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨hgG, hgD⟩ := hg
  have hgU : g ∈ UH (Hpk k r) := by
    have h := hgG
    simp only [Glev, Set.mem_setOf_eq] at h
    exact h.1
  have hleft : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hgU
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [mul_assoc]
      _ = 1 := by rw [hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq k r]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hdet
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  set Y := g * X * g⁻¹ with hYdef
  have hconj : ∀ u : ℝ, g * NormedSpace.exp ((u : ℂ) • X) = NormedSpace.exp ((u : ℂ) • Y) * g := by
    intro u
    have h1 : (u : ℂ) • Y = g * ((u : ℂ) • X) * g⁻¹ := by
      rw [hYdef, mul_smul_comm, smul_mul_assoc]
    rw [h1, Matrix.exp_conj _ _ hU, mul_assoc, hgi, mul_one]
  have hSu : ∀ u : ℝ, InS k r l ((u : ℂ) • Y) := fun u => inS_smul _ hS
  have hmemN : ∀ u : ℝ, NormedSpace.exp ((u : ℂ) • Y) ∈ Nlev k r l.castSucc := by
    intro u
    have hUu := exp_uh hk u
    rw [exp_S (hSu u)] at hUu ⊢
    exact memN_S (hSu u) hUu
  have hfe : ∀ u : ℝ, f (g * NormedSpace.exp ((u : ℂ) • X)) =
      psi k r z cStd (NormedSpace.exp ((u : ℂ) • Y)) • f g := by
    intro u
    rw [hconj u]
    exact hL g ⟨hgG, hgD⟩ _ (hmemN u)
  have hell : ∀ u : ℝ, ell k r z (NormedSpace.exp ((u : ℂ) • Y)) =
      (u : ℂ) * ell k r z Y + (u : ℂ) ^ 2 * ((1 / 2 : ℂ) * ell k r z (Y * Y)) := by
    intro u
    rw [exp_S (hSu u), ell_add, ell_add, ell_one z hz]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ell_sm]
    ring
  have hfun : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =
      fun u : ℝ => Complex.exp (Complex.I * (((cStd * ((u : ℂ) * ell k r z Y +
        (u : ℂ) ^ 2 * ((1 / 2 : ℂ) * ell k r z (Y * Y)))).re : ℝ) : ℂ)) • f g := by
    funext u
    rw [hfe u, ← hell u]
    rfl
  have hd := (hasDerivAt_phase (ell k r z Y) ((1 / 2 : ℂ) * ell k r z (Y * Y))).smul_const (f g)
  show deriv (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0 = _
  rw [hfun]
  exact hd.deriv
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
