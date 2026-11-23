-- Prove2me | solution 1 for Formalism.L2.Col.atW_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:38.8928+00:00
-- url     : https://prove2.me/submissions/b1d3e954-809f-49ee-845c-9aa1defe1aa6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_atW_mono

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    atW w (A ⊓ B) = atW w A ⊓ atW w B := by
  apply le_antisymm (le_inf (atW_mono w inf_le_left) (atW_mono w inf_le_right))
  rintro x ⟨hA, hB⟩
  obtain ⟨s, hs, hx⟩ := mem_atW_iff.1 hA
  obtain ⟨t, ht, hy⟩ := mem_atW_iff.1 hB
  refine mem_atW_iff.2 ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
  · rw [mul_comm, mul_smul]; exact A.smul_mem t hx
  · rw [mul_smul]; exact B.smul_mem s hy
end Formalism.L2.Col
