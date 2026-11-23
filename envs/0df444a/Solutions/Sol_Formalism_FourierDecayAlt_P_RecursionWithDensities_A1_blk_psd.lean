-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.blk_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:08.836439+00:00
-- url     : https://prove2.me/submissions/276cb423-19a6-4b9c-b9db-112475634b32

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_ext_inj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
section gen
variable {α : Type}
variable {E : Type} [AddCommGroup E]
end gen
section ta
variable {E : Type} [Field E] [DecidableEq E]
private theorem isPt_of_mem_pt (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n, ∀ h ∈ PT Sg n, IsPt n h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hh
    cases n with
    | zero =>
      simp only [PT, Finset.mem_singleton] at hh
      subst hh
      simp [TA.IsPt, TA.lvl]
    | succ n =>
      simp only [PT, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image] at hh
      obtain ⟨a, h0, hh0, t, ht, he⟩ := hh
      subst he
      have hm := Finset.mem_range.mp a.2
      obtain ⟨hl, hb⟩ := ih a.1 hm h0 hh0
      unfold TA.IsPt
      refine ⟨?_, ?_⟩
      · simp [TA.ext, TA.lvl] at hl ⊢
        omega
      · intro b hbm
        simp only [TA.ext, List.mem_append, List.mem_singleton] at hbm
        rcases hbm with hbm | rfl
        · exact hb b hbm
        · refine ⟨?_, hNZ _ _ t ht⟩
          show 1 ≤ n + 1 - a.1
          omega
end ta
section main
variable {E : Type} [Field E] [DecidableEq E]
end main
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
namespace Formalism.FourierDecayAlt.P
open RecursionWithDensities
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) (hK : AxK D) (i s : ℕ)
    (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) (t : E) (ht : t ≠ 0) :
    PSDOn (PT Sg (i - s)) (fun h h' => D.K i (TA.ext h s t) (TA.ext h' s t)) := by
  obtain ⟨_, hK2⟩ := hK
  have hP : ∀ p ∈ (PT Sg (i - s)).image (fun h => TA.ext h s t), IsPt i p := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hl, hb⟩ := isPt_of_mem_pt Sg hNZ (i - s) h hh
    unfold TA.IsPt
    refine ⟨?_, ?_⟩
    · simp [TA.ext, TA.lvl] at hl ⊢
      omega
    · intro b hbm
      simp only [TA.ext, List.mem_append, List.mem_singleton] at hbm
      rcases hbm with hbm | rfl
      · exact hb b hbm
      · exact ⟨hs, ht⟩
  have hk := hK2 i hi _ hP
  have hinj : Set.InjOn (fun h => TA.ext h s t) (PT Sg (i - s)) := fun x _ y _ e => (ext_inj e).1
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => hk.1 _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy),
    fun a => ?_⟩
  have h := hk.2 (fun p => a p.dropLast)
  simp only [Finset.sum_image hinj] at h
  simpa [TA.ext] using h
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
