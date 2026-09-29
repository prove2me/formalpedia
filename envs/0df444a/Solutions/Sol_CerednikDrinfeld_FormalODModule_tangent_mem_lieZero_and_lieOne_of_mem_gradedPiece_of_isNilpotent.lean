-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bb8ec1c1-58cf-5233-889d-dbc82d45b8c4

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent

set_option autoImplicit false

universe u

namespace TangentGraded

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

section Witt

variable (p : ℕ) [Fact p.Prime] {k : Type} [CommRing k] [CharP k p] [PerfectRing k p]

open WittVector

theorem exists_teichmuller_add (a : WittVector p k) :
    ∃ (c : k) (b : WittVector p k), a = teichmuller p c + (p : WittVector p k) * b := by
  have hd0 : (a - teichmuller p (a.coeff 0)).coeff 0 = 0 := by
    have h := add_coeff_zero (teichmuller p (a.coeff 0)) (a - teichmuller p (a.coeff 0))
    rw [add_sub_cancel, teichmuller_coeff_zero] at h
    exact (left_eq_add.mp h)
  have hd1 : a - teichmuller p (a.coeff 0) = verschiebung ((a - teichmuller p (a.coeff 0)).shift 1) := by
    have := eq_iterate_verschiebung (x := a - teichmuller p (a.coeff 0)) (n := 1)
      (by intro i hi; interval_cases i; exact hd0)
    simpa only [Function.iterate_one] using this
  obtain ⟨x, hx⟩ := (frobenius_bijective p k).2 ((a - teichmuller p (a.coeff 0)).shift 1)
  have hV : verschiebung (frobenius x) = x * (p : WittVector p k) := by
    simpa only [Function.iterate_one, pow_one] using iterate_verschiebung_iterate_frobenius x 1
  refine ⟨a.coeff 0, x, ?_⟩
  rw [mul_comm, ← hV, hx, ← hd1, add_sub_cancel]

theorem exists_sum_teichmuller (N : ℕ) (a : WittVector p k) :
    ∃ (c : Fin N → k) (b : WittVector p k),
      a = (∑ i : Fin N, (p : WittVector p k) ^ (i : ℕ) * teichmuller p (c i)) + (p : WittVector p k) ^ N * b := by
  induction N with
  | zero => exact ⟨Fin.elim0, a, by simp⟩
  | succ N ih =>
    obtain ⟨c, b, hab⟩ := ih
    obtain ⟨c', b', hb⟩ := exists_teichmuller_add p b
    refine ⟨Fin.snoc c c', b', ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.coe_castSucc]
    rw [hab, hb]
    ring

end Witt

section Lie

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]

theorem lieAct_apply (X : FormalODModule p B) (a : Zp2 p) (v : X.Lie) :
    X.lieAct a v = (linearPart (X.act a)).mulVec v := rfl

theorem lieAct_add (X : FormalODModule p B) (a b : Zp2 p) (v : X.Lie) :
    X.lieAct (a + b) v = X.lieAct a v + X.lieAct b v := by
  rw [lieAct_apply, lieAct_apply, lieAct_apply, X.act_add]
  show (linearPart (fun i => MvPowerSeries.subst (Sum.elim (X.act a) (X.act b)) (X.F.toPowerSeries i))).mulVec v = _
  rw [linearPart_subst_elim X.F (X.isLawHom_act a).1 (X.isLawHom_act b).1, Matrix.add_mulVec]

theorem lieAct_mul (X : FormalODModule p B) (a b : Zp2 p) (v : X.Lie) :
    X.lieAct (a * b) v = X.lieAct a (X.lieAct b v) := by
  rw [lieAct_apply, lieAct_apply, lieAct_apply, X.act_mul, Matrix.mulVec_mulVec]
  congr 1
  exact linearPart_subst (X.isLawHom_act b).1 (X.act a)

theorem lieAct_natCast (X : FormalODModule p B) (n : ℕ) (v : X.Lie) :
    X.lieAct (n : Zp2 p) v = (n : B) • v := by
  rw [lieAct_apply, X.act_natCast, linearPart_nthSeries, nsmul_eq_mul, mul_one, Matrix.natCast_mulVec]

theorem lieAct_zero (X : FormalODModule p B) (v : X.Lie) : X.lieAct 0 v = 0 := by
  have := lieAct_natCast X 0 v
  rwa [Nat.cast_zero, Nat.cast_zero, zero_smul] at this

theorem lieAct_eq_smul_of_teichmuller (X : FormalODModule p B) (hB : IsNilpotent (p : B))
    (χ : Zp2 p →+* B) (v : X.Lie)
    (h : ∀ c : GaloisField p 2, X.lieAct (WittVector.teichmuller p c) v = χ (WittVector.teichmuller p c) • v)
    (a : Zp2 p) : X.lieAct a v = χ a • v := by
  obtain ⟨N, hN⟩ := hB
  obtain ⟨c, b, rfl⟩ := exists_sum_teichmuller p N a

  let S : AddSubmonoid (Zp2 p) :=
    { carrier := {a | X.lieAct a v = χ a • v}
      add_mem' := fun {a b} ha hb => by
        show X.lieAct (a + b) v = χ (a + b) • v
        rw [lieAct_add, ha, hb, map_add, add_smul]
      zero_mem' := by
        show X.lieAct 0 v = χ 0 • v
        rw [lieAct_zero, map_zero, zero_smul] }
  have hpow : ∀ (k : ℕ) (c : GaloisField p 2),
      (p : Zp2 p) ^ k * WittVector.teichmuller p c ∈ S := by
    intro k c
    show X.lieAct ((p : Zp2 p) ^ k * WittVector.teichmuller p c) v = χ ((p : Zp2 p) ^ k * WittVector.teichmuller p c) • v
    rw [lieAct_mul, h, ← Nat.cast_pow, lieAct_natCast, map_mul, map_natCast, smul_smul]
  have htail : (p : Zp2 p) ^ N * b ∈ S := by
    show X.lieAct ((p : Zp2 p) ^ N * b) v = χ ((p : Zp2 p) ^ N * b) • v
    rw [lieAct_mul, ← Nat.cast_pow, lieAct_natCast, map_mul, map_natCast, Nat.cast_pow, hN, zero_smul,
      zero_mul, zero_smul]
  have hmem : (∑ i : Fin N, (p : Zp2 p) ^ (i : ℕ) * WittVector.teichmuller p (c i)) + (p : Zp2 p) ^ N * b ∈ S :=
    S.add_mem (S.sum_mem fun i _ => hpow i (c i)) htail
  exact hmem

theorem mem_lieZero_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (v : X.Lie) :
    v ∈ X.lieZero j ↔ ∀ a, X.lieAct a v = j a • v := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_lieOne_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (v : X.Lie) :
    v ∈ X.lieOne j ↔ ∀ a, X.lieAct a v = j (WittVector.frobenius a) • v := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem lieAct_teichmuller_tangent (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) (c : GaloisField p 2) :
    X.lieAct (WittVector.teichmuller p c) (tangent f) = (j (WittVector.teichmuller p c) ^ p ^ n) • tangent f := by
  have := congrArg tangent (hf c)
  rw [endAct_apply, tangent_map, tangent_homothety] at this
  exact this

theorem frobenius_teichmuller (c : GaloisField p 2) :
    WittVector.frobenius (WittVector.teichmuller p c) = WittVector.teichmuller p c ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

end Lie

end TangentGraded

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B) :
    (∀ f ∈ X.gradedPiece j 0, MvFormalGroup.CartierModule.tangent f ∈ X.lieZero j) ∧
    (∀ f ∈ X.gradedPiece j 1, MvFormalGroup.CartierModule.tangent f ∈ X.lieOne j) := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · rw [TangentGraded.mem_lieZero_iff]
    exact TangentGraded.lieAct_eq_smul_of_teichmuller X hB j _ (fun c => by
      rw [TangentGraded.lieAct_teichmuller_tangent X j 0 f hf c, pow_zero, pow_one])
  · rw [TangentGraded.mem_lieOne_iff]
    exact TangentGraded.lieAct_eq_smul_of_teichmuller X hB (j.comp (WittVector.frobenius (p := p))) _ (fun c => by
      rw [TangentGraded.lieAct_teichmuller_tangent X j 1 f hf c, pow_one, RingHom.comp_apply,
        TangentGraded.frobenius_teichmuller, map_pow])

end S_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent (solution)
