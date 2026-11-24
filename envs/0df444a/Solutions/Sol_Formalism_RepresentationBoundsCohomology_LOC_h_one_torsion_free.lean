-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.h_one_torsion_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:43.098031+00:00
-- url     : https://prove2.me/submissions/4c6b75a8-90f1-41c0-869d-5a03521491b5

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_HOneTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
open ReciprocityTheory.Gal
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {O G V : Type u} [CommRing O] [IsDomain O] [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V] (ρ : Representation O G V)
    (hb : ∀ c : O, c ≠ 0 → Function.Bijective fun v : V => c • v) :
    Module.IsTorsionFree O (H1 ρ) := by
  refine ⟨fun r hr => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have key : ∀ x : H1 ρ, r • x = 0 → x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      intro h
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 h
      obtain ⟨m', hm'⟩ := (hb r hr0).2 m
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 ρ _).2 ⟨m', fun g => (hb r hr0).1 ?_⟩
      have h1 : r • z.1 g = ρ g m - m := hm g
      show r • z.1 g = r • (ρ g m' - m')
      have hm'' : r • m' = m := hm'
      rw [h1, smul_sub, ← map_smul, hm'']
  intro x y hxy
  have hxy' : r • x = r • y := hxy
  have : r • (x - y) = 0 := by rw [smul_sub, hxy', sub_self]
  exact sub_eq_zero.1 (key _ this)
end Formalism.RepresentationBoundsCohomology.LOC
