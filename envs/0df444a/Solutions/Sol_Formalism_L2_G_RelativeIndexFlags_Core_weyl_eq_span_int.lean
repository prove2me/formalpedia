-- Prove2me | solution 1 for Formalism.L2.G.RelativeIndexFlags.Core.weyl_eq_span_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:27.672845+00:00
-- url     : https://prove2.me/submissions/d82e5ccf-62d3-4b26-b898-925bb3ba732c

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
import Theorems.Thm_Formalism_L2_G_RelativeIndexFlags_Core_map_mem_weyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core
namespace Formalism.L2.G.RelativeIndexFlags.Core
theorem _root_.solution (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    weyl O r n hn ν = Submodule.span O ((fun f => MvPolynomial.map (Int.castRingHom O) f) ''
      (weyl ℤ r n hn ν : Set (MvPolynomial (Fin r × Fin n) ℤ))) := by
  apply le_antisymm
  · show Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    exact ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, by
      show MvPolynomial.map (Int.castRingHom O) (applyWord ℤ w (hw ℤ hn ν)) = _
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact map_mem_weyl hn ν f hf
end Formalism.L2.G.RelativeIndexFlags.Core
