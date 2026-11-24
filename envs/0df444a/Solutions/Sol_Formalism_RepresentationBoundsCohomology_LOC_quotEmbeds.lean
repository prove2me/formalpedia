-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.quotEmbeds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:49.441782+00:00
-- url     : https://prove2.me/submissions/0b1207a7-8ec2-4adc-828f-674f9be901bc

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsPowSmulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatQuotEmbeds.{u} := by
  intro O V _ _ _ _ _ _ _ T hT
  have hfin : Module.Finite O T := Module.Finite.iff_fg.mpr hT.1
  have htfV : Module.IsTorsionFree O V := Module.IsTorsionFree.trans (R := FractionRing O)
  have htf : Module.IsTorsionFree O T := inferInstance
  have hfree : Module.Free O T := inferInstance
  let b := Module.finBasis O T
  let v : Fin (Module.finrank O T) → V := fun i => (b i : V)
  have hliO : LinearIndependent O v :=
    b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  have hTv : ∀ t : T, (t : V) = ∑ i, b.repr t i • v i := by
    intro t
    have h := congrArg T.subtype (b.sum_repr t)
    rw [map_sum] at h
    simpa [v] using h.symm
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hT.2, Submodule.span_le]
    intro t ht
    have h : t = ∑ i, b.repr ⟨t, ht⟩ i • v i := hTv ⟨t, ht⟩
    rw [h]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul (FractionRing O)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B : Module.Basis (Fin (Module.finrank O T)) (FractionRing O) V := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨?_, ?_⟩
  · rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  · let f : V →ₗ[O] (Fin (Module.finrank O T) → KO O) :=
      LinearMap.pi fun i => (toKO O) ∘ₗ ((B.coord i).restrictScalars O)
    have hker : LinearMap.ker f = T := by
      apply le_antisymm
      · intro x hx
        have hx' : ∀ i, B.repr x i ∈ (1 : Submodule O (FractionRing O)) := by
          intro i
          have := congrFun (LinearMap.mem_ker.mp hx) i
          exact (Submodule.Quotient.mk_eq_zero _).mp this
        rw [← B.sum_repr x]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hx' i)
        rw [← ha, algebraMap_smul, hB]
        exact T.smul_mem _ (b i).2
      · intro x hx
        rw [LinearMap.mem_ker]
        funext i
        have hrep : B.repr x i = algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ i) := by
          have h1 : x = ∑ j, algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ j) • B j := by
            have h : x = ∑ i, b.repr ⟨x, hx⟩ i • v i := hTv ⟨x, hx⟩
            simpa [hB] using h
          have h2 := DFunLike.congr_fun (congrArg B.repr h1) i
          rw [B.repr_sum_self] at h2
          exact h2
        change toKO O (B.repr x i) = 0
        rw [hrep]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_one.mpr ⟨_, rfl⟩)
    refine ⟨T.liftQ f hker.ge, ?_⟩
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker, Submodule.mkQ_map_self]
end Formalism.RepresentationBoundsCohomology.LOC
