-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lifting_isometry_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:34.920531+00:00
-- url     : https://prove2.me/submissions/362a774d-ef71-4fad-a39b-d54f1cba8d5e

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftIsoW := by
  intro K V _ _ _ _ H r F F' j hj c Wt hNF hL
  obtain ⟨-, -, -, -, -, hk, hk', hs, hs'⟩ := hNF
  constructor
  · intro w hw
    obtain ⟨x, hx, hv⟩ := hs w hw
    obtain ⟨wt, hwt, i, hi, e⟩ := Submodule.mem_sup.1 (hL.2.2 _ hv)
    refine ⟨wt, ⟨hwt, ?_⟩, ?_⟩
    · have : w - wt = x + i := by rw [eq_sub_iff_add_eq] at e; rw [← e]; abel
      rw [this]; exact F.X.add_mem hx hi.1
    · rintro wt' ⟨hwt', hx'⟩
      have hX1 : w - wt ∈ F.X := by
        have : w - wt = x + i := by rw [eq_sub_iff_add_eq] at e; rw [← e]; abel
        rw [this]; exact F.X.add_mem hx hi.1
      have hd : wt' - wt ∈ F.X := by
        have : wt' - wt = (w - wt) - (w - wt') := by abel
        rw [this]; exact F.X.sub_mem hX1 hx'
      have hdW : wt' - wt ∈ Wt := Wt.sub_mem hwt' hwt
      have hI : wt' - wt ∈ II F F' := (hk _ hd).1 (fun y hy => hL.1 _ hdW y hy)
      have : wt' - wt ∈ Wt ⊓ II F F' := ⟨hdW, hI⟩
      rw [hL.2.1] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot K).1 this)
  · intro w hw
    obtain ⟨x, hx, hv⟩ := hs' w hw
    obtain ⟨wt, hwt, i, hi, e⟩ := Submodule.mem_sup.1 (hL.2.2 _ hv)
    have hX1 : w - wt ∈ F'.X := by
      have : w - wt = x + i := by rw [eq_sub_iff_add_eq] at e; rw [← e]; abel
      rw [this]; exact F'.X.add_mem hx hi.2
    refine ⟨wt, ⟨hwt, hX1⟩, ?_⟩
    rintro wt' ⟨hwt', hx'⟩
    have hd : wt' - wt ∈ F'.X := by
      have : wt' - wt = (w - wt) - (w - wt') := by abel
      rw [this]; exact F'.X.sub_mem hX1 hx'
    have hdW : wt' - wt ∈ Wt := Wt.sub_mem hwt' hwt
    have hI : wt' - wt ∈ II F F' := (hk' _ hd).1 (fun y hy => hL.1 _ hdW y hy)
    have : wt' - wt ∈ Wt ⊓ II F F' := ⟨hdW, hI⟩
    rw [hL.2.1] at this
    exact sub_eq_zero.1 ((Submodule.mem_bot K).1 this)
end Formalism.HermitianLatticeCounting.P
