-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_torsion_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:49.256163+00:00
-- url     : https://prove2.me/submissions/e507735b-97f2-4850-a42e-6bf68574cd9a

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
set_option backward.isDefEq.respectTransparency false
open NumberField.Units
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (hr : ∀ w : InfinitePlace F, w.IsReal) (x : (𝓞 F)ˣ) (hx : x ∈ torsion F) :
    x = 1 ∨ x = -1 := by
  by_cases hc : 2 < orderOf x
  · exfalso
    rw [← orderOf_units, ← orderOf_submonoid] at hc
    have h0 := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf ((x : 𝓞 F) : F))
    obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
    haveI : Nonempty {w : InfinitePlace F // w.IsReal} := ⟨⟨w0, hr w0⟩⟩
    rw [InfinitePlace.nrRealPlaces] at h0
    exact ((@Fintype.card_eq_zero_iff _ (_)).1 h0).false ⟨w0, hr w0⟩
  · have hc' : orderOf x ≤ 2 := not_lt.mp hc
    interval_cases hi : orderOf x
    · exact absurd ((CommGroup.mem_torsion x).1 hx) (orderOf_eq_zero_iff.mp hi)
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · right
      rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]
end Formalism.HermitianLatticeCounting.P
