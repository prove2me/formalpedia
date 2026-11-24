-- Prove2me | solution 1 for Formalism.SLP.P.CountO.inf_sup_mulSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:13.310515+00:00
-- url     : https://prove2.me/submissions/08be1986-97df-4cca-b3ae-ea9ec0c0f1ac

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_mem_mulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (N : Submodule R X) {a b : ℕ} (hab : a.Coprime b)
    (hN : N.toAddSubgroup.index = a * b) :
    (N ⊔ mulSub R X a) ⊓ (N ⊔ mulSub R X b) = N := by
  have hkill : ∀ w : X, (a * b) • w ∈ N := fun w => by
    have := AddSubgroup.nsmul_index_mem N.toAddSubgroup w
    rw [hN] at this
    exact this
  refine le_antisymm ?_ (le_inf le_sup_left le_sup_left)
  rintro x ⟨hx1, hx2⟩
  obtain ⟨y1, hy1, z1, hz1, rfl⟩ := Submodule.mem_sup.mp hx1
  obtain ⟨y2, hy2, z2, hz2, h2⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨w1, rfl⟩ := mem_mulSub hz1
  obtain ⟨w2, rfl⟩ := mem_mulSub hz2
  set x := y1 + a • w1 with hxdef
  have hbx : b • x ∈ N := by
    rw [hxdef, smul_add, smul_smul, mul_comm b a]
    exact N.add_mem (N.toAddSubgroup.nsmul_mem hy1 b) (hkill w1)
  have hax : a • x ∈ N := by
    rw [← h2, smul_add, smul_smul]
    exact N.add_mem (N.toAddSubgroup.nsmul_mem hy2 a) (hkill w2)
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have e1 : x = (Nat.gcdA a b) • (a • x) + (Nat.gcdB a b) • (b • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, ← add_smul, mul_comm,
      mul_comm (Nat.gcdB a b), ← h, one_smul]
  rw [e1]
  exact N.add_mem (N.toAddSubgroup.zsmul_mem hax _) (N.toAddSubgroup.zsmul_mem hbx _)
end Formalism.SLP.P.CountO
