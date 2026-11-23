-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.finite_bad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:08.423741+00:00
-- url     : https://prove2.me/submissions/d145560b-5538-4b33-a253-3a12fd95fd68

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) :
    {P : Ideal (𝓞 (maximalRealSubfield E)) | P.IsMaximal ∧ t ∉ locAt E P L}.Finite := by
  obtain ⟨n, hn, hnt⟩ := hL.2 t
  have hn0 : (n : 𝓞 (maximalRealSubfield E)) ≠ 0 := by
    intro h
    have : n = 0 := by exact_mod_cast h
    omega
  have hI : Ideal.span {(n : 𝓞 (maximalRealSubfield E))} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => v.asIdeal)).subset ?_
  rintro P ⟨hP, htP⟩
  have hnP : (n : 𝓞 (maximalRealSubfield E)) ∈ P := by
    by_contra h
    exact htP ⟨n, h, by rw [map_natCast]; exact hnt⟩
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hnP
    exact hn0 hnP
  exact ⟨⟨P, hP.isPrime, hPbot⟩, by
    show P ∣ _
    rw [Ideal.dvd_span_singleton]; exact hnP, rfl⟩
end Formalism.FourierDecayAlt.P.S6x6
