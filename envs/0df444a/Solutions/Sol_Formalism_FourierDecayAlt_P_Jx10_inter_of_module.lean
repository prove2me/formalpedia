-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx10.inter_of_module
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:01.811187+00:00
-- url     : https://prove2.me/submissions/9975578f-924d-4124-9bc7-c040f98bf13c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx10
namespace Formalism.FourierDecayAlt.P.Jx10
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by
  by_contra ht
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢
        exact hL c _ ha }
  have hI : I ≠ ⊤ := by
    intro hI
    apply ht
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := by
      rw [hI]
      exact Submodule.mem_top
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L := h1
    simpa using h2
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, haP, haL⟩ := h P hP
  exact haP (hIP haL)
end Formalism.FourierDecayAlt.P.Jx10
