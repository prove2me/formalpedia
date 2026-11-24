-- Prove2me | solution 1 for Formalism.L2.Col.le_of_atW_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:16.547158+00:00
-- url     : https://prove2.me/submissions/1e03c92f-1242-45aa-abb6-26ff322cc83d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution {A B : Submodule (𝓞 K) V}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), atW w A ≤ atW w B) : A ≤ B := by
  intro x hx
  let I : Ideal (𝓞 K) := B.colon {x}
  by_contra hxB
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : 𝓞 K) ∈ I := by rw [hI]; trivial
    rw [Submodule.mem_colon_singleton] at h1
    exact hxB (by simpa using h1)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 (h ((plEquiv K).symm ⟨m, hm⟩) (Submodule.subset_span hx))
  exact hs (hIm (Submodule.mem_colon_singleton.2 hsx))
end Formalism.L2.Col
