-- Prove2me | solution 1 for Bl.general_b_fact_left_last.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:33.580238+00:00
-- url     : https://prove2.me/submissions/fade0a10-36e5-48a4-9090-8c7a8ddf4786

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Module.End
namespace Bl.general_b_fact_left_last
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
private lemma pz {T : End K V} {x : V} {k m : ℕ} (hkm : k ≤ m) (hx : (T ^ k) x = 0) :
    (T ^ m) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [show k + d = d + k from Nat.add_comm k d, pow_add, Module.End.mul_apply, hx, map_zero]
end Bl.general_b_fact_left_last
end

set_option autoImplicit false
open Module Module.End
open Bl Bl.general_b_fact_left_last
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Bl.general_b_fact_left_last
theorem _root_.solution {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A * B).maxGenEigenspace (a * b) := by
  rw [mem_maxGenEigenspace] at hA hB ⊢
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  have hNB : Commute (A - a • 1) B := h.sub_left ((Commute.one_left B).smul_left a)
  have hNM : Commute (A - a • 1) (B - b • 1) :=
    hNB.sub_right ((Commute.one_right _).smul_right b)
  have hBM : Commute B (B - b • 1) :=
    (Commute.refl B).sub_right ((Commute.one_right B).smul_right b)
  have key : A * B - (a * b) • (1 : End K V) = (A - a • 1) * B + a • (B - b • 1) := by
    rw [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]; abel
  have hc : Commute ((A - a • 1) * B) (a • (B - b • 1)) := (hNM.mul_left hBM).smul_right a
  refine ⟨k + l, ?_⟩
  rw [key, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, hNB.mul_pow, smul_pow]
  refine (congrArg _ ?_).trans (smul_zero _)
  rcases le_or_gt k m with hkm | hkm
  · have hC : Commute ((A - a • 1) ^ m) (B ^ m * (a ^ (k + l - m) • (B - b • 1) ^ (k + l - m))) :=
      (hNB.pow_pow m m).mul_right ((hNM.pow_pow m (k + l - m)).smul_right _)
    rw [mul_assoc, hC.eq, Module.End.mul_apply, pz hkm hk, map_zero]
  · rw [Module.End.mul_apply, LinearMap.smul_apply, pz (by omega) hl, smul_zero, map_zero]
end Bl.general_b_fact_left_last
