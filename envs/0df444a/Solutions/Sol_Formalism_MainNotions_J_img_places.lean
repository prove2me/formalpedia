-- Prove2me | solution 1 for Formalism.MainNotions.J.img_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:11.958816+00:00
-- url     : https://prove2.me/submissions/e049ce23-4422-4250-a778-9d665556f3ea

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_max
import Theorems.Thm_Formalism_MainNotions_J_liesOver_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (span {(p : ℤ)}).primesOver (𝓞 K) := by
  haveI := pI_max p hp
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hle : (span {(p : ℤ)} : Ideal ℤ) ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ v.asIdeal
      simpa using hv
    exact (pI_max p hp).eq_of_le (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top hle
  · rintro ⟨hPp, hPl⟩
    refine ⟨⟨P, hPp, liesOver_ne_bot K p hp P hPl⟩, ?_, rfl⟩
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPl.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
end Formalism.MainNotions.J
