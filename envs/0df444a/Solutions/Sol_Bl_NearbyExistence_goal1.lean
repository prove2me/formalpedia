-- Prove2me | solution 1 for Bl.NearbyExistence.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:46.198508+00:00
-- url     : https://prove2.me/submissions/d52f6c76-eb56-4cc6-a43f-5b4c66b4cdf9

import Mathlib
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.NearbyExistence
private lemma exists_near (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) :
    ∃ y : F, Valued.v (x - algebraMap F (v.adicCompletion F) y) < 1 := by
  have hn : {z : v.adicCompletion F | Valued.v (x - z) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_one_iff] at hz ⊢
    rwa [Valuation.map_sub_swap]
  obtain ⟨z, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := F) v x) _ hn
  exact ⟨y, hz⟩
end Bl.NearbyExistence
end

set_option autoImplicit false
open Bl Bl.NearbyExistence
namespace Bl.NearbyExistence
theorem _root_.solution :
  ∀ {F : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F))
  (x :
    Subtype.{1} fun (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} F v) ↦
      Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.{0, 0} F v) x),
  Exists.{1} fun (r : NumberField.RingOfIntegers.{0} F) ↦
    LT.lt.{0}
      (DFunLike.coe.{1, 1, 1} Valued.v.{0, 0}
        (HSub.hSub.{0, 0, 0} (Subtype.val.{1} x)
          (DFunLike.coe.{1, 1, 1}
            (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} F)
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} F v))
            r)))
      1 := by
  intro F _ _ v x
  obtain ⟨y, hy⟩ := exists_near F v x.1
  have hx : Valued.v x.1 ≤ 1 := x.2
  have hyc : Valued.v (algebraMap F (v.adicCompletion F) y) ≤ 1 := by
    have e : algebraMap F (v.adicCompletion F) y = x.1 - (x.1 - algebraMap F (v.adicCompletion F) y) := by
      ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx hy.le)
  have hyv : v.valuation F y ≤ 1 := by
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y
    rwa [e2] at hyc
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyv 1
  refine ⟨a, ?_⟩
  have e1 : x.1 - algebraMap (NumberField.RingOfIntegers F) (v.adicCompletion F) a
      = (x.1 - algebraMap F (v.adicCompletion F) y) +
        algebraMap F (v.adicCompletion F) (y - algebraMap (NumberField.RingOfIntegers F) F a) := by
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers F) F (v.adicCompletion F), map_sub]
    ring
  rw [e1]
  refine Valuation.map_add_lt _ hy ?_
  have e3 : Valued.v (algebraMap F (v.adicCompletion F) (y - algebraMap (NumberField.RingOfIntegers F) F a))
      = v.valuation F (y - algebraMap (NumberField.RingOfIntegers F) F a) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [e3, Valuation.map_sub_swap]
  simpa using ha
end Bl.NearbyExistence
