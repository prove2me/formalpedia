-- Prove2me | solution 1 for Formalism.L2.G.RelativeIndexFlags.Core.map_mem_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:00:53.421022+00:00
-- url     : https://prove2.me/submissions/11d003eb-11d0-4a6c-852c-2db313634420

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
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
theorem _root_.solution {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    MvPolynomial.map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨w, by rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : MvPolynomial.map (Int.castRingHom O) (c • x) = (c : O) • MvPolynomial.map (Int.castRingHom O) x := by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]; rfl
    rw [e1]; exact Submodule.smul_mem _ _ hx
end Formalism.L2.G.RelativeIndexFlags.Core
