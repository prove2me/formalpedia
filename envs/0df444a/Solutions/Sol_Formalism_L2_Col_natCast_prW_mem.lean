-- Prove2me | solution 1 for Formalism.L2.Col.natCast_prW_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:19.161887+00:00
-- url     : https://prove2.me/submissions/fbfe30b3-e731-41b8-a43e-2ef7c1eaaf96

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : ((prW w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have h := Ideal.absNorm_mem (w.asIdeal.under ℤ)
  have h2 := Ideal.mem_comap.1 h
  simpa [prW] using h2
end Formalism.L2.Col
