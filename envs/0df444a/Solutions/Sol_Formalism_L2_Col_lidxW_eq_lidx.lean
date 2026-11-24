-- Prove2me | solution 1 for Formalism.L2.Col.lidxW_eq_lidx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:55.686667+00:00
-- url     : https://prove2.me/submissions/c8255744-40ba-4e5a-be4c-1958713abbca

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_lenW_toNat

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
    lidxW w A B = Formalism.HermitianLatticesTheory.lidx w.asIdeal A B := by
  unfold lidxW Formalism.HermitianLatticesTheory.lidx
  rw [lenW_toNat, lenW_toNat]
end Formalism.L2.Col
