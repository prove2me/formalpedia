-- Prove2me | solution 1 for DiazModulus.boxHilb_anti
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:15:12.019514+00:00
-- url     : https://prove2.me/submissions/599c2267-ab50-4c7e-8ddf-307bce4eaeb2

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # The box Hilbert function is antitone in the ideal

`I ≤ J` implies `h_J(T) ≤ h_I(T)` (DALAG Ex. 8.3, the easy direction).

Since `I ≤ J`, the quotient map `S → S ⧸ J` factors as `S → S ⧸ I → S ⧸ J` through the
`K`-algebra map `Ideal.Quotient.factorₐ`. Hence the image of `F_T` in `S ⧸ J` is the image,
under a linear map, of its image in `S ⧸ I` (`Submodule.map_comp`). That image is
finite-dimensional, being the image of `F_T`, and a linear map does not raise dimension
(`Submodule.finrank_map_le`). -/

namespace C11_F2b
open DiazModulus
end C11_F2b

open DiazModulus C11_F2b in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) {I J : Ideal S} (hIJ : I ≤ J) (T : B → ℕ) :
    boxHilb F J T ≤ boxHilb F I T := by
  unfold boxHilb
  have hcomp : (Ideal.Quotient.mkₐ K J).toLinearMap =
      (Ideal.Quotient.factorₐ K hIJ).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    rfl
  rw [hcomp, Submodule.map_comp]
  exact Submodule.finrank_map_le _ _
