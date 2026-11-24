-- Prove2me | solution 1 for Formalism.L2.NG.IsLabelOf.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:50.143929+00:00
-- url     : https://prove2.me/submissions/d4f94e62-5bea-4e0d-b809-b9ef5a4239b9

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
import Theorems.Thm_Formalism_L2_NG_IsLabelOf_at_gen
import Theorems.Thm_Formalism_L2_NG_eq_of_rootsBar_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}
namespace Formalism.L2.NG
namespace IsLabelOf
theorem _root_.solution (h : IsLabelOf A κ ζ teich I n P f) (h' : IsLabelOf A κ ζ teich I n P f')
    (ht : Function.Injective teich) {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ I) (hc : NT.TameCoupled A κ σ ζ) : f = f' := by
  have e := (h.at_gen hσ hc).symm.trans (h'.at_gen hσ hc)
  have r := congrArg Polynomial.roots e
  have key : ∀ s : Multiset (Formalism.CyclotomicNorms.Fbar p), ((s.map fun x => X - C (teich x)).prod).roots = s.map teich := by
    intro s
    have : (s.map fun x => X - C (teich x)) = (s.map teich).map fun a => X - C a := by rw [Multiset.map_map]; rfl
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  rw [key, key] at r
  exact eq_of_rootsBar_eq h.1 h'.1 (Multiset.map_injective ht r)
end IsLabelOf
end Formalism.L2.NG
