-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.pderiv_subst_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:13.908513+00:00
-- url     : https://prove2.me/submissions/cb7adbcc-abd2-4380-8b72-c55fbec17f88

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {R : Type*} [CommRing R] {σ : Type*}
namespace Formalism.ELL.SubstitutionCoefficientCongruence
theorem _root_.solution (p : Polynomial R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv R i ((p : PowerSeries R).subst a) =
      (derivative R (p : PowerSeries R)).subst a * MvPowerSeries.pderiv R i a := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  suffices H : ∀ P : Polynomial R, MvPowerSeries.pderiv R i (PowerSeries.substAlgHom hs (P : PowerSeries R)) =
      PowerSeries.substAlgHom hs (derivative R (P : PowerSeries R)) * MvPowerSeries.pderiv R i a by
    simpa only [PowerSeries.coe_substAlgHom] using H p
  intro P
  induction P using Polynomial.induction_on'
  next P Q hP hQ =>
    rw [Polynomial.coe_add, map_add, map_add, hP, hQ, map_add, map_add, add_mul]
  next n c =>
    have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries R) = a := by
      rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
    rw [← Polynomial.smul_X_eq_monomial]
    simp only [Polynomial.coe_smul, Polynomial.coe_pow, Polynomial.coe_X, map_smul, map_pow, hX,
      Derivation.map_smul, Derivation.leibniz_pow, PowerSeries.derivative_X, map_nsmul, smul_eq_mul,
      mul_one, map_mul, map_one, nsmul_eq_mul, map_natCast, smul_mul_assoc, mul_assoc]
end Formalism.ELL.SubstitutionCoefficientCongruence
