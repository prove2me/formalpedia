-- Prove2me | solution 1 for Formalism.L2.Th1.A.jet_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:02.855593+00:00
-- url     : https://prove2.me/submissions/ace4ab4a-8c0a-4f10-b4c2-8771a199aef7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_More_iterate_derivative_subst
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply


section
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace More
section Tools
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (W : WeierstrassCurve R)
end Tools
end More
open More
namespace More
end More
namespace More
end More
namespace More
end More
private theorem constantCoeff_powerSeries_subst_eq_zero {R : Type u} [CommRing R] {a : R⟦X⟧} (ha : HasSubst a)
    (ha0 : constantCoeff a = 0) (g : R⟦X⟧) :
    constantCoeff (g.subst a) = constantCoeff g := by
  obtain ⟨h, hh⟩ := (PowerSeries.X_dvd_iff).mpr
    (show constantCoeff (g - C (constantCoeff g)) = 0 by simp)
  have hg : g = X * h + (constantCoeff g) • (1 : R⟦X⟧) := by
    rw [PowerSeries.smul_eq_C_mul, mul_one, ← hh]; ring
  rw [hg, ← PowerSeries.coe_substAlgHom ha, map_add, map_mul, map_smul, map_one,
    PowerSeries.coe_substAlgHom ha, PowerSeries.subst_X ha]
  simp [ha0, PowerSeries.smul_eq_C_mul]
private theorem factorial_mul_coeff_eq_coeff_zero_iterate_derivative {R : Type u} [CommRing R] (n : ℕ) (g : R⟦X⟧) :
    (n.factorial : R) * coeff n g = coeff 0 ((derivative R)^[n] g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ← ih, PowerSeries.coeff_derivative, Nat.factorial_succ]
    push_cast
    ring
namespace More
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)
end More
namespace More
variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)
end More
end Formalism.L2.Th1.A
end
end

set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
namespace Formalism.L2.Th1.A
theorem _root_.solution : JetZ.{u} := by
  intro K _ _ W f n
  have hE0 : constantCoeff (expSer W) = 0 := by
    first
    | exact (expSpec_of integration_spec composition_inverse_spec invariant_differential_units K W).1
    | exact (formal_exponential_spec K W).1
  have hs : HasSubst (expSer W) := by
    first
    | exact HasSubst.of_constantCoeff_zero' hE0
    | exact HasSubst.of_constantCoeff_zero hE0
  rw [factorial_mul_coeff_eq_coeff_zero_iterate_derivative, More.iterate_derivative_subst, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_powerSeries_subst_eq_zero hs hE0]
end Formalism.L2.Th1.A
