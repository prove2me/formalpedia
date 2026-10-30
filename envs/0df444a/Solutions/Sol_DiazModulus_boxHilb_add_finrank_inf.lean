-- Prove2me | solution 1 for DiazModulus.boxHilb_add_finrank_inf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:12:12.46903+00:00
-- url     : https://prove2.me/submissions/0cbda6c3-cc48-4121-8b07-727fbf1c342a

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Rank–nullity for the box Hilbert function

`h_I(T) + dim_K (F_T ∩ I) = dim_K F_T`.

Let `q : S → S ⧸ I` be the quotient map, viewed as a `K`-linear map, and restrict it to the
finite-dimensional space `F_T`. Its range is the image `q(F_T)`, whose dimension is `h_I(T)` by
definition. Its kernel is the preimage of `ker q = I` in `F_T`, which is linearly equivalent to
`F_T ∩ I` (`Submodule.comapSubtypeEquivOfLe`). Rank–nullity
(`LinearMap.finrank_range_add_finrank_ker`) gives the identity. -/

namespace C11_F1
open DiazModulus

/-- The kernel of the quotient map, as a `K`-linear map, is `I` seen as a `K`-subspace. -/
theorem ker_mkₐ_toLinearMap {K S : Type*} [Field K] [CommRing S] [Algebra K S] (I : Ideal S) :
    LinearMap.ker (Ideal.Quotient.mkₐ K I).toLinearMap = Submodule.restrictScalars K I := by
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

end C11_F1

open DiazModulus C11_F1 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (T : B → ℕ) :
    boxHilb F I T + Module.finrank K ↥(F T ⊓ Submodule.restrictScalars K I) = Module.finrank K ↥(F T) := by
  set q := (Ideal.Quotient.mkₐ K I).toLinearMap
  set f := q.domRestrict (F T)
  have hrange : LinearMap.range f = (F T).map q := LinearMap.range_domRestrict _ _
  have hker : LinearMap.ker f =
      Submodule.comap (F T).subtype (F T ⊓ Submodule.restrictScalars K I) := by
    rw [LinearMap.ker_domRestrict, ker_mkₐ_toLinearMap]
    ext x
    simp
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)] at hrn
  exact hrn
