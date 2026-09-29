-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1bd8142d-eb40-5d27-b521-475364f2c25f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld

noncomputable section

namespace TorsionFreeReduced

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule

variable {p : ℕ} [Fact p.Prime]

theorem hasHeight_map_field {B : Type} [CommRing B] (X : FormalODModule p B) (hX4 : X.HasHeight 4)
    {K : Type} [Field K] (g : B →+* K) : (X.map g).HasHeight 4 := by
  obtain ⟨-, -, hfib⟩ := hX4
  have hK : Module.finrank K (KerAlgebra ((X.act (p : Zp2 p)).map g)) = p ^ 4 := hfib K g
  show HasKernelOfDegree ((X.map g).act (p : Zp2 p)) (p ^ 4)
  rw [map_act]
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · exact Module.finite_of_finrank_pos (by rw [hK]; exact pow_pos (Nat.Prime.pos Fact.out) 4)
  · exact Module.Projective.of_free
  · rw [CerednikDrinfeld.SpecialFormal.Series.map_map]; exact hfib κ (f.comp g)

section Field

variable {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
  (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)

theorem natCast_ne_zero_witt : ((p : ℕ) : WittVector p K) ≠ 0 := by
  intro h
  have h1 := WittVector.coeff_p_one p K
  rw [h, WittVector.zero_coeff] at h1
  exact zero_ne_one h1

include hY hY4 in

theorem eq_zero_of_mem_piece (n : ℕ) (x : CartierModule p Y.F) (hx : x ∈ Y.gradedPiece j n)
    (hPix : endAct Y.varpiEnd x = 0) : x = 0 := by
  let Φs : SpecialFormalODModule p j := ⟨Y, hY, hY4⟩
  obtain ⟨-, e, -, hbasis⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul p j Φs n
  obtain ⟨w, hw, -⟩ := hbasis x hx
  obtain ⟨w0, -, huniq0⟩ := hbasis 0 (zero_mem _)
  have hpx : (p : ℕ) • x = 0 := by rw [← endAct_varpiEnd_endAct_varpiEnd, hPix, map_zero]
  have h1 : w0 = fun _ => 0 := (huniq0 (fun _ => 0) (by simp)).symm
  have h2 : w0 = fun r => ((p : ℕ) : WittVector p K) * w r := by
    refine (huniq0 _ ?_).symm
    rw [← hpx, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  have hw0 : ∀ r, w r = 0 := by
    intro r
    have := congrFun (h1.symm.trans h2) r
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (natCast_ne_zero_witt (K := K))
    · exact h
  rw [hw]
  exact Finset.sum_eq_zero fun r _ => by rw [hw0 r, zero_smul]

include hY hY4 in
theorem field_case (m : CartierModule p Y.F) (hm : endAct Y.varpiEnd m = 0) : m = 0 := by
  obtain ⟨hc, -, -, hPi, -⟩ :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j Y hY.1
  have hm' : m ∈ Y.gradedPiece j 0 ⊔ Y.gradedPiece j 1 := by
    rw [hc.sup_eq_top]; exact AddSubgroup.mem_top m
  obtain ⟨m₀, hm₀, m₁, hm₁, rfl⟩ := AddSubgroup.mem_sup.1 hm'
  have h01 : endAct Y.varpiEnd m₀ ∈ Y.gradedPiece j 1 := hPi 0 m₀ hm₀
  have h10 : endAct Y.varpiEnd m₁ ∈ Y.gradedPiece j 0 := by
    have := hPi 1 m₁ hm₁
    rwa [show (1 + 1 : ℕ) = 0 + 2 from rfl, gradedPiece_add_two] at this
  have hsum : endAct Y.varpiEnd m₀ + endAct Y.varpiEnd m₁ = 0 := by rw [← map_add]; exact hm
  have hdis := hc.disjoint
  rw [AddSubgroup.disjoint_def] at hdis
  have h0' : endAct Y.varpiEnd m₀ ∈ Y.gradedPiece j 0 := by
    have : endAct Y.varpiEnd m₀ = -endAct Y.varpiEnd m₁ := eq_neg_of_add_eq_zero_left hsum
    rw [this]; exact neg_mem h10
  have hz0 : endAct Y.varpiEnd m₀ = 0 := hdis h0' h01
  have hz1 : endAct Y.varpiEnd m₁ = 0 := by rwa [hz0, zero_add] at hsum
  rw [eq_zero_of_mem_piece j Y hY hY4 0 m₀ hm₀ hz0, eq_zero_of_mem_piece j Y hY hY4 1 m₁ hm₁ hz1, add_zero]

end Field

theorem coeff_eq_zero_of_forall_prime {B : Type} [CommRing B] [IsReduced B] (c : B)
    (h : ∀ (J : Ideal B) [J.IsPrime], algebraMap B J.ResidueField c = 0) : c = 0 :=
  IsReduced.eq_zero c (nilpotent_iff_mem_prime.2 fun J hJ => by
    haveI := hJ
    exact Ideal.algebraMap_residueField_eq_zero.1 (h J))

end TorsionFreeReduced

end

open TorsionFreeReduced MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] [IsReduced B] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (m : MvFormalGroup.CartierModule p X.F) (hm : MvFormalGroup.CartierModule.endAct X.varpiEnd m = 0) :
    m = 0 := by

  refine CartierModule.ext (funext fun l => ?_)
  rw [toPowerSeries_zero]
  ext e
  rw [MvPowerSeries.coeff_zero]
  refine coeff_eq_zero_of_forall_prime _ fun J _ => ?_

  let κ := J.ResidueField
  let K := AlgebraicClosure κ
  let g : B →+* K := (algebraMap κ K).comp (algebraMap B κ)
  have hpK : ((p : ℕ) : K) = 0 := by rw [← map_natCast g, CharP.cast_eq_zero, map_zero]
  haveI : CharP K p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out hpK)

  have hY : (X.map g).IsSpecial (g.comp j) := CerednikDrinfeld.FormalODModule.IsSpecial.map j g X hX
  have hY4 : (X.map g).HasHeight 4 := hasHeight_map_field X hX4 g
  have hbc : baseChange (p := p) g (endAct X.varpiEnd m) =
      endAct (X.map g).varpiEnd (baseChange (p := p) g m) :=
    baseChangeEq_endAct g rfl (fun i => varpiEnd_map_toPowerSeries g X i) m
  have hzero : baseChange (p := p) g m = 0 := by
    refine field_case (g.comp j) (X.map g) hY hY4 _ ?_
    rw [← hbc, hm, map_zero]
    rfl
  have hcoeff : g (MvPowerSeries.coeff e (m.toPowerSeries l)) = 0 := by
    have := congrArg (fun x : CartierModule p (X.map g).F => MvPowerSeries.coeff e (x.toPowerSeries l)) hzero
    simpa only [toPowerSeries_baseChangeEq, MvPowerSeries.coeff_map, toPowerSeries_zero,
      MvPowerSeries.coeff_zero] using this
  have hinj : Function.Injective (algebraMap κ K) := (algebraMap κ K).injective
  exact hinj (by rw [map_zero]; exact hcoeff)

end S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced (solution)
