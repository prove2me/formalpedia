-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.torsion_bound_of_totient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:34.612579+00:00
-- url     : https://prove2.me/submissions/78057ed1-afcc-4207-8464-5f6ca19a8ce8

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TorsionBoundAsm := by
  intro hT E _ _ f hf
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  have hord : orderOf ζ = Nat.card (NumberField.Units.torsion E) :=
    orderOf_eq_card_of_forall_mem_zpowers hζ
  set w := Nat.card (NumberField.Units.torsion E) with hw
  have hwpos : 0 < w := Nat.card_pos
  let φ : NumberField.Units.torsion E →* E :=
    ((algebraMap (𝓞 E) E : 𝓞 E →* E).comp (Units.coeHom (𝓞 E))).comp
      (NumberField.Units.torsion E).subtype
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective hab
  have hprim : IsPrimitiveRoot (φ ζ) w := by
    rw [← hord, ← orderOf_injective φ hφ ζ]
    exact IsPrimitiveRoot.orderOf _
  have h1 : Nat.totient w ≤ 2 * f := by
    rw [← hf, ← Polynomial.natDegree_cyclotomic w ℚ, Polynomial.cyclotomic_eq_minpoly_rat hprim hwpos]
    exact minpoly.natDegree_le _
  calc w ≤ 2 * Nat.totient w ^ 2 := hT w
    _ ≤ 2 * (2 * f) ^ 2 := by gcongr
    _ = 8 * f ^ 2 := by ring
end Formalism.HermitianLatticeCounting.P
