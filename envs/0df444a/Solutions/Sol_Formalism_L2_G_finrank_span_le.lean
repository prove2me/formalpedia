-- Prove2me | solution 1 for Formalism.L2.G.finrank_span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:31.835187+00:00
-- url     : https://prove2.me/submissions/d864e2ff-8620-44c2-b4ad-d7e02913ff4e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TiedFamilies_TieDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G
open Module
namespace Formalism.L2.G
theorem _root_.solution {O Kf W : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M] :
    Module.rank Kf (Submodule.span Kf (M : Set W)) ≤ (Module.finrank O M : Cardinal) := by
  obtain ⟨b, hbM, hspan, hli⟩ := exists_linearIndependent Kf (M : Set W)
  rw [← hspan, rank_span_set hli]

  have hinj : Function.Injective fun r : O => r • (1 : Kf) := by
    simpa [Algebra.smul_def] using IsFractionRing.injective O Kf
  have hliO : LinearIndependent O (fun x : b => (x : W)) := hli.restrict_scalars hinj
  let w : b → M := fun x => ⟨x, hbM x.2⟩
  have hliw : LinearIndependent O w := LinearIndependent.of_comp M.subtype hliO
  have h1 := hliw.cardinal_le_rank
  have h2 : Module.rank O M < Cardinal.aleph0 := Module.rank_lt_aleph0 O M
  rw [Module.finrank, Cardinal.cast_toNat_of_lt_aleph0 h2]
  exact h1
end Formalism.L2.G
