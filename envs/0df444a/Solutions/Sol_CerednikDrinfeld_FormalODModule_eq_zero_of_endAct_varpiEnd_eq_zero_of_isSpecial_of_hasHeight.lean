-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isSpecial_of_hasHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/05d5c6b3-469c-5a58-98a9-237328bb8e10

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap

import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isSpecial_of_hasHeight
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace TorsionFreeM

open MvFormalGroup MvFormalGroup.CartierModule

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

theorem isMaximal_pIdeal [IsAlgClosed k] : (pIdeal p (WittVector p k)).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)

theorem charP_quot : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
  CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)

theorem isAlgClosed_of_ringEquiv {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

end TorsionFreeM

end

open TorsionFreeM MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (m : MvFormalGroup.CartierModule p Φ.F) (hm : MvFormalGroup.CartierModule.endAct Φ.varpiEnd m = 0) :
    m = 0 := by
  classical

  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal := isMaximal_pIdeal p k
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := charP_quot p k
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) := isAlgClosed_of_ringEquiv eK
  set J := (Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι with hJ
  let Φ' : SpecialFormalODModule p J := ⟨Φ, hΦ, hΦ4⟩
  have hW := fun n => CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul p J Φ' n

  have hpm : (p : ℕ) • m = 0 := by
    rw [← CerednikDrinfeld.FormalODModule.endAct_varpiEnd_endAct_varpiEnd Φ m, hm, map_zero]

  have hp0 : ((p : ℕ) : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) ≠ 0 := by
    intro h
    have := congrArg (fun w => w.coeff 1) h
    simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
    exact one_ne_zero this
  have hpiece : ∀ (n : ℕ) (x : CartierModule p Φ.F), x ∈ Φ.gradedPiece J n → (p : ℕ) • x = 0 → x = 0 := by
    intro n x hx hpx
    obtain ⟨-, e, he, huniq⟩ := hW n
    obtain ⟨w, hw, -⟩ := huniq x hx
    have h1 : (0 : CartierModule p Φ.F) = ∑ r, (fun _ : Fin 2 => (0 : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)))) r • e r := by
      simp
    have h2 : (0 : CartierModule p Φ.F) =
        ∑ r, (fun r => ((p : ℕ) : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) * w r) r • e r := by
      rw [← hpx, hw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← smul_smul, Nat.cast_smul_eq_nsmul]
    have hw0 := (huniq 0 (zero_mem _)).unique h1 h2
    have : w = 0 := by
      funext r
      have := (congrFun hw0 r).symm
      exact (mul_eq_zero.mp this).resolve_left hp0
    rw [hw, this]; simp

  have hpnil : IsNilpotent ((p : ℕ) : WittVector p k ⧸ pIdeal p (WittVector p k)) :=
    ⟨1, by rw [pow_one]; exact (CharP.cast_eq_zero _ p)⟩
  have hc := CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p J hpnil Φ
  obtain ⟨m0, hm0, m1, hm1, rfl⟩ := AddSubgroup.mem_sup.mp (show m ∈ Φ.gradedPiece J 0 ⊔ Φ.gradedPiece J 1 by
    rw [hc.sup_eq_top]; trivial)
  have hsum : (p : ℕ) • m0 + (p : ℕ) • m1 = 0 := by rw [← smul_add]; exact hpm
  have hp0m : (p : ℕ) • m0 ∈ Φ.gradedPiece J 0 := AddSubgroup.nsmul_mem _ hm0 _
  have hp1m : (p : ℕ) • m1 ∈ Φ.gradedPiece J 1 := AddSubgroup.nsmul_mem _ hm1 _
  have hdisj := hc.disjoint
  have e0 : (p : ℕ) • m0 = 0 := by
    have hneg : (p : ℕ) • m0 = -((p : ℕ) • m1) := eq_neg_of_add_eq_zero_left hsum
    have : (p : ℕ) • m0 ∈ Φ.gradedPiece J 1 := by rw [hneg]; exact AddSubgroup.neg_mem _ hp1m
    exact (AddSubgroup.disjoint_def.mp hdisj) hp0m this
  have e1 : (p : ℕ) • m1 = 0 := by rwa [e0, zero_add] at hsum
  rw [hpiece 0 m0 hm0 e0, hpiece 1 m1 hm1 e1, add_zero]

end S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isSpecial_of_hasHeight
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isSpecial_of_hasHeight (solution)
