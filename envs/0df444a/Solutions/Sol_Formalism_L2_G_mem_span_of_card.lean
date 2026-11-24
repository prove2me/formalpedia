-- Prove2me | solution 1 for Formalism.L2.G.mem_span_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:11.377156+00:00
-- url     : https://prove2.me/submissions/85f3273e-a9bd-4559-b0b6-48e22ed6260f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TiedFamilies_TieDim
import Theorems.Thm_Formalism_L2_G_finrank_span_le

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
theorem _root_.solution {O Kf W ι : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M]
    [Fintype ι] (c : ι → W) (hli : LinearIndependent Kf c) (hc : ∀ i, c i ∈ Submodule.span Kf (M : Set W))
    (hcard : Fintype.card ι = Module.finrank O M) (F : W) (hF : F ∈ M) : F ∈ Submodule.span Kf (Set.range c) := by
  by_contra hF'
  have hli2 : LinearIndependent Kf (fun o : Option ι => Option.casesOn' o F c) :=
    linearIndependent_option'.mpr ⟨hli, hF'⟩
  let S := Submodule.span Kf (M : Set W)
  have hmem : ∀ o : Option ι, Option.casesOn' o F c ∈ S := by
    intro o
    cases o with
    | none => exact Submodule.subset_span hF
    | some i => exact hc i
  let w : Option ι → S := fun o => ⟨_, hmem o⟩
  have hliw : LinearIndependent Kf w := LinearIndependent.of_comp S.subtype hli2

  have h1 := hliw.cardinal_le_rank.trans (finrank_span_le (Kf := Kf) M)
  rw [Cardinal.mk_fintype, Fintype.card_option] at h1
  norm_cast at h1
  omega
end Formalism.L2.G
