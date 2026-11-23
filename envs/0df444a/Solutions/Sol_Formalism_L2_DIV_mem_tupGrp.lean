-- Prove2me | solution 1 for Formalism.L2.DIV.mem_tupGrp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:25.75101+00:00
-- url     : https://prove2.me/submissions/91d88ddd-fcc0-46d1-b9fe-13473aacafdd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Theorems.Thm_Formalism_L2_DIV_mem_kills


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution {S : Set ℕ} (ξ : Chr F E L) : ξ ∈ tupGrp F E L S ↔
    ((ratId F E).range ≤ ξ.ker ∧ (∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker) ∧ IsOfFinOrder ξ) ∧
      (idF F E).range ≤ ξ.ker ∧ (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ¬ GoodPl E S v → inertAt E v ≤ ξ.ker := by
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mem_kills, CommGroup.mem_torsion]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
end Formalism.L2.DIV
