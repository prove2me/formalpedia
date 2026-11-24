-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.exists_dual_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:05.450122+00:00
-- url     : https://prove2.me/submissions/59a76412-2325-4f30-b897-07dc78b70e29

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_map_frac_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
open Formalism.RepresentationBoundsCohomology.LOC.Lat2
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
  [IsScalarTower O (FractionRing O) V']
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution {b : V →ₗ[O] V' →ₗ[O] FractionRing O} (hb : PerfectRight b) {n : ℕ}
    (e : Basis (Fin n) (FractionRing O) V) :
    ∃ f : Basis (Fin n) (FractionRing O) V',
      (∀ i x, e.repr x i = b x (f i)) ∧ (∀ i w, f.repr w i = b (e i) w) := by
  choose f hf using fun i => (hb (e.coord i)).exists
  have hexp : ∀ w : V', w = ∑ i, b (e i) w • f i := by
    intro w
    refine (hb ((b.flip w).extendScalarsOfIsLocalization (nonZeroDivisors O)
      (FractionRing O))).unique (fun x => rfl) (fun x => ?_)
    rw [LinearMap.extendScalarsOfIsLocalization_apply', LinearMap.flip_apply, map_sum]
    conv_rhs => rw [← e.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_frac_smul, hf, map_frac_smul b, LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul,
      smul_eq_mul, mul_comm]
  have hli : LinearIndependent (FractionRing O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (b (e j)) hc
    rw [map_sum, map_zero] at h
    rw [← h, Finset.sum_eq_single j]
    · rw [map_frac_smul, hf, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro i _ hij
      rw [map_frac_smul, hf, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij,
        smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range f) := by
    intro w _
    rw [hexp w]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨Basis.mk hli hsp, fun i x => ?_, fun i w => ?_⟩
  · rw [Basis.mk_apply, hf, Basis.coord_apply]
  · conv_lhs => rw [hexp w]
    have : ∑ i, b (e i) w • f i = ∑ i, b (e i) w • (Basis.mk hli hsp) i := by
      simp only [Basis.mk_apply]
    rw [this, Basis.repr_sum_self]
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
