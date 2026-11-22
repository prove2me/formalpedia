-- Prove2me | solution 1 for Formalism.UG.P.glint_finite_quotient_of_dvr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:36.50781+00:00
-- url     : https://prove2.me/submissions/37c37f1e-710a-4543-99b6-0e1f0f07d1db

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : Finite (IsLocalRing.ResidueField R)) (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key : ∀ k : ℕ, Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Ideal.one_eq_top]
      exact Finite.of_fintype (R ⧸ ⊤)
    | succ k ih =>
      have hle : IsLocalRing.maximalIdeal R ^ (k + 1) ≤ IsLocalRing.maximalIdeal R ^ k :=
        Ideal.pow_le_pow_right (by simp)
      replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.toEquiv
      suffices Finite (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))
          (IsLocalRing.maximalIdeal R ^ k)) from
        .of_ideal_quotient (.map (Ideal.Quotient.mk _) (IsLocalRing.maximalIdeal R ^ k))
      exact @Finite.of_equiv _ _ h
        ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal _)
          (IsDiscreteValuationRing.not_a_field _) k).trans
          (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ k))
  have : I = IsLocalRing.maximalIdeal R ^ m := by
    rw [hm, hmax, Ideal.span_singleton_pow]
  rw [this]
  exact key m
end Formalism.UG.P
