-- Prove2me | solution 1 for Formalism.L2.G.RelativeIndexFlags.Core.map_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:38:57.255451+00:00
-- url     : https://prove2.me/submissions/d53635d9-dcd0-4844-9f88-93e4927c2f4b

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core
namespace Formalism.L2.G.RelativeIndexFlags.Core
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (F : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R g F) = rowAct S (g.map φ) (MvPolynomial.map φ F) := by
  have h : (MvPolynomial.map φ).comp (rowAct R (n := n) g).toRingHom =
      (rowAct S (n := n) (g.map φ)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h F
end Formalism.L2.G.RelativeIndexFlags.Core
