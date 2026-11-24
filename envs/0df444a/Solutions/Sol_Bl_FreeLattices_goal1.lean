-- Prove2me | solution 1 for Bl.FreeLattices.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:31.838869+00:00
-- url     : https://prove2.me/submissions/33d67afd-f210-477e-b5b4-23260b8066cf

import Mathlib
import Definitions.Def_Lemmata_B1962s_FreeLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.FreeLattices
private theorem tf (p : Nat) [Fact (Nat.Prime p)] (σ : Type) :
    Module.IsTorsionFree (PadicInt p) (MvPolynomial σ (Padic p)) := by
  refine Module.IsTorsionFree.comap (S := Padic p) (algebraMap (PadicInt p) (Padic p)) ?_ ?_
  · intro r hr
    have h0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap (PadicInt p) (Padic p) r ≠ 0 := by
      simpa using h0
    exact IsRegular.of_ne_zero h1
  · intro r m
    exact algebraMap_smul (Padic p) r m
end Bl.FreeLattices
end

set_option autoImplicit false
open Bl Bl.FreeLattices
namespace Bl.FreeLattices
theorem _root_.solution :
  Bl.FreeLattices.FreeLat := by
  intro p _ σ L W _ _ hL
  have := tf p σ
  have : Module.Finite (PadicInt p) L := Module.Finite.iff_fg.mpr hL
  let b := Module.finBasis (PadicInt p) L
  refine ⟨Module.finrank (PadicInt p) L, fun i => (b i : MvPolynomial σ (Padic p)), ?_, ?_, ?_⟩
  · intro a
    exact (b a).2
  · exact b.linearIndependent.map' L.subtype L.ker_subtype
  · have h := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
end Bl.FreeLattices
