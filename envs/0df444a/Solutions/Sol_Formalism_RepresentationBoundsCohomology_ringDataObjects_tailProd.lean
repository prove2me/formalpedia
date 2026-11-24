-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.tailProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:20.559255+00:00
-- url     : https://prove2.me/submissions/dc0fe224-9b5a-4660-91ae-4fa30754b682

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {M : Type*} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := by
  cases t with
  | zero => simp
  | succ n =>
    rw [List.range_succ_eq_map, List.tail_cons, List.map_map, ← List.prod_toFinset _ List.nodup_range,
      List.toFinset_range]
    have hI : Finset.Ioo 0 (n + 1) = (Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext i
      simp only [Finset.mem_Ioo, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨i - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        omega
    (rw [hI, Finset.prod_map]) <;> rfl
end Formalism.RepresentationBoundsCohomology.ringDataObjects
