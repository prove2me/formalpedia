-- Prove2me | solution 1 for DiazModulus.card_le_boxHilb_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:12:18.500985+00:00
-- url     : https://prove2.me/submissions/e671449e-c697-43a3-8964-4cff60ac4485

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # Independent families modulo `I` bound the box Hilbert function

If `e : ι → F_T` is linearly independent modulo `I`, then `|ι| ≤ h_I(T)`.

Write `q : S → S ⧸ I` for the quotient map and `W = q(F_T)`, so `h_I(T) = dim_K W`. Each
`q(e_i)` lies in `W`, so the family factors through `W` as `i ↦ ⟨q(e_i), _⟩`; it is still
linearly independent there, since composing with the inclusion `W → S ⧸ I` recovers the given
independent family (`LinearIndependent.of_comp`). `W` is finite-dimensional, being the image of
`F_T`, and an independent family in a finite-dimensional space has at most `dim` members
(`LinearIndependent.fintype_card_le_finrank`). -/

namespace C11_F3
open DiazModulus
end C11_F3

open DiazModulus C11_F3 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) {ι : Type*} [Fintype ι] (I : Ideal S) (T : B → ℕ)
    (e : ι → S) (he : ∀ i, e i ∈ F T)
    (hli : LinearIndependent K (fun i => Ideal.Quotient.mk I (e i))) :
    Fintype.card ι ≤ boxHilb F I T := by
  unfold boxHilb
  set W := (F T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let v : ι → W := fun i => ⟨Ideal.Quotient.mk I (e i), Submodule.mem_map_of_mem (he i)⟩
  have hv : LinearIndependent K v := LinearIndependent.of_comp W.subtype hli
  exact hv.fintype_card_le_finrank
