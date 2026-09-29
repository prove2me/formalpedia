-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/16fe745c-867d-5b20-beb5-4e1fed8eacb4

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld

open MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B))
    (X X' : FormalODModule p B)
    (θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F)
    (hθ : ∀ (c : GaloisField p 2) (f : MvFormalGroup.CartierModule p X.F),
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd (WittVector.teichmuller p c)) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd (WittVector.teichmuller p c)) (θ f)) :
    ∀ (a : Zp2 p) (f : MvFormalGroup.CartierModule p X.F),
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd a) (θ f) := by
  classical
  intro a f

  have ρ_add : ∀ (Y : FormalODModule p B) (a b : Zp2 p) (g : CartierModule p Y.F),
      endAct (Y.actEnd (a + b)) g = endAct (Y.actEnd a) g + endAct (Y.actEnd b) g := by
    intro Y a b g
    rw [← FormalODModule.actRingHom_apply, map_add, map_add]
    rfl
  have ρ_mul : ∀ (Y : FormalODModule p B) (a b : Zp2 p) (g : CartierModule p Y.F),
      endAct (Y.actEnd (a * b)) g = endAct (Y.actEnd a) (endAct (Y.actEnd b) g) := by
    intro Y a b g
    rw [← FormalODModule.actRingHom_apply, map_mul, map_mul, AddMonoid.End.coe_mul, Function.comp_apply]
    rfl
  have ρ_nat : ∀ (Y : FormalODModule p B) (n : ℕ) (g : CartierModule p Y.F),
      endAct (Y.actEnd (n : Zp2 p)) g = n • g := by
    intro Y n g
    rw [← FormalODModule.actRingHom_apply, map_natCast, endAct_natCast]

  let G : Zp2 p → Prop := fun a => ∀ g : CartierModule p X.F,
    θ (endAct (X.actEnd a) g) = endAct (X'.actEnd a) (θ g)
  have G_add : ∀ a b, G a → G b → G (a + b) := by
    intro a b ha hb g
    show θ (endAct (X.actEnd (a + b)) g) = endAct (X'.actEnd (a + b)) (θ g)
    rw [ρ_add, ρ_add, map_add, ha g, hb g]
  have G_mul : ∀ a b, G a → G b → G (a * b) := by
    intro a b ha hb g
    show θ (endAct (X.actEnd (a * b)) g) = endAct (X'.actEnd (a * b)) (θ g)
    rw [ρ_mul, ρ_mul, ha, hb]
  have G_nat : ∀ n : ℕ, G (n : Zp2 p) := by
    intro n g
    show θ (endAct (X.actEnd (n : Zp2 p)) g) = endAct (X'.actEnd (n : Zp2 p)) (θ g)
    rw [ρ_nat, ρ_nat, map_nsmul]
  have G_teich : ∀ c : GaloisField p 2, G (WittVector.teichmuller p c) := fun c g => hθ c g

  have hdecomp : ∀ N : ℕ, ∃ s b : Zp2 p, G s ∧ a = s + (p : Zp2 p) ^ N * b := by
    intro N
    induction N with
    | zero => exact ⟨0, a, by simpa using G_nat 0, by rw [pow_zero, one_mul, zero_add]⟩
    | succ N ih =>
      obtain ⟨s, b, hs, hab⟩ := ih
      have hmem : b - WittVector.teichmuller p (b.coeff 0) ∈ Ideal.span {(p : Zp2 p)} := by
        rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
        have h := map_sub (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2) b
          (WittVector.teichmuller p (b.coeff 0))
        change (b - WittVector.teichmuller p (b.coeff 0)).coeff 0 =
          b.coeff 0 - (WittVector.teichmuller p (b.coeff 0)).coeff 0 at h
        rw [h, WittVector.teichmuller_coeff_zero, sub_self]
      obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp hmem
      refine ⟨s + (p : Zp2 p) ^ N * WittVector.teichmuller p (b.coeff 0), b', ?_, ?_⟩
      · exact G_add _ _ hs (G_mul _ _ (by simpa using G_nat (p ^ N)) (G_teich _))
      · rw [hab, add_assoc, add_right_inj, pow_succ, mul_assoc, ← mul_add]
        congr 1
        rw [mul_comm, hb', add_sub_cancel]

  set D : CartierModule p X'.F := θ (endAct (X.actEnd a) f) - endAct (X'.actEnd a) (θ f) with hD
  have hdiv : ∀ N : ℕ, ∃ d : CartierModule p X'.F, D = (p ^ N : ℕ) • d := by
    intro N
    obtain ⟨s, b, hs, hab⟩ := hdecomp N
    refine ⟨θ (endAct (X.actEnd b) f) - endAct (X'.actEnd b) (θ f), ?_⟩
    rw [hD, hab, ρ_add, ρ_add, map_add, hs f, add_sub_add_left_eq_sub, ρ_mul, ρ_mul, ← Nat.cast_pow,
      ρ_nat, ρ_nat, map_nsmul, smul_sub]

  obtain ⟨e, he⟩ := hB
  obtain ⟨y, hy⟩ : ∃ y : WittVector p B, ((p ^ e : ℕ) : WittVector p B) = WittVector.verschiebung y := by
    refine ⟨((p ^ e : ℕ) : WittVector p B).shift 1, ?_⟩
    have h := WittVector.eq_iterate_verschiebung (x := ((p ^ e : ℕ) : WittVector p B)) (n := 1) (by
      intro i hi
      obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
      have h0 := map_natCast (WittVector.constantCoeff : WittVector p B →+* B) (p ^ e)
      change ((p ^ e : ℕ) : WittVector p B).coeff 0 = ((p ^ e : ℕ) : B) at h0
      rw [h0, Nat.cast_pow, he])
    simpa using h
  have hV : ∀ (N : ℕ) (m : CartierModule p X'.F), ∃ t : CartierModule p X'.F,
      ((p ^ e : ℕ) ^ N : ℕ) • m = (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[N] t := by
    intro N
    induction N with
    | zero => intro m; exact ⟨m, by simp⟩
    | succ N ih =>
      intro m
      obtain ⟨t, ht⟩ := ih (y • frobenius m)
      refine ⟨t, ?_⟩
      rw [pow_succ, ← smul_smul, ← natCast_smul_eq_nsmul' (p ^ e) m, hy, ← verschiebungInt_smul_frobenius,
        ← natCast_smul_eq_nsmul', smul_verschiebungInt, map_natCast, natCast_smul_eq_nsmul', ht,
        ← Function.iterate_succ_apply' (⇑(verschiebungInt (p := p) (Φ := X'.F)))]

  have hDV : ∀ N : ℕ, ∃ t : CartierModule p X'.F, D = (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[N] t := by
    intro N
    obtain ⟨d, hd⟩ := hdiv (e * N)
    obtain ⟨t, ht⟩ := hV N d
    exact ⟨t, by rw [hd, pow_mul, ht]⟩
  have huniq := MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p X'.F
    (fun _ => (0 : CartierModule p X'.F))
  have hzero : ∀ N : ℕ, (∑ m ∈ Finset.range N,
      (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[m] ((fun _ => (0 : CartierModule p X'.F)) m)) = 0 := by
    intro N
    exact Finset.sum_eq_zero (fun m _ => iterate_map_zero _ _)
  have hD0 : D = 0 := by
    apply huniq.unique
    · intro N
      obtain ⟨t, ht⟩ := hDV N
      exact ⟨t, by rw [hzero, zero_add]; exact ht⟩
    · intro N
      exact ⟨0, by rw [hzero, zero_add, iterate_map_zero]⟩
  exact sub_eq_zero.mp hD0

end S_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent (solution)
