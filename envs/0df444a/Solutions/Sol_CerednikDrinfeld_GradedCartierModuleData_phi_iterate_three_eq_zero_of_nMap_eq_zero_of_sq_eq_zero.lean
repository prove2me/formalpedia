-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9a22c38a-8650-5c4c-871f-085d872dbf2a

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero

set_option autoImplicit false

namespace C7Proof

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [hp : Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']

theorem sq_eq_zero_of_mem {φ : B →+* B'} (hI2 : RingHom.ker φ * RingHom.ker φ = ⊥) {a : B}
    (ha : a ∈ RingHom.ker φ) : a * a = 0 := by
  have h : a * a ∈ RingHom.ker φ * RingHom.ker φ := Ideal.mul_mem_mul ha ha
  rw [hI2] at h
  exact (Submodule.mem_bot B).mp h

theorem pow_p_eq_zero {a : B} (ha : a * a = 0) : a ^ p = 0 :=
  pow_eq_zero_of_le hp.out.two_le (by rw [pow_two]; exact ha)

theorem frobenius_teichmuller_eq_zero {a : B} (ha : a * a = 0) :
    WittVector.frobenius (WittVector.teichmuller p a) = 0 := by
  rw [WittVector.frobenius_teichmuller_eq, pow_p_eq_zero ha, WittVector.teichmuller_zero]

theorem natCast_mul_teichmuller_eq_zero {a : B} (hpa : (p : B) * a = 0) (ha : a * a = 0) :
    (p : WittVector p B) * WittVector.teichmuller p a = 0 := by
  set q : WittVector p B := (p : WittVector p B) - WittVector.teichmuller p (p : B) with hq
  have hq0 : q.coeff 0 = 0 := by
    have h1 : (p : WittVector p B).coeff 0 = (p : B) :=
      map_natCast (WittVector.constantCoeff : WittVector p B →+* B) p
    have h2 : q.coeff 0 = (p : WittVector p B).coeff 0 - (WittVector.teichmuller p (p : B)).coeff 0 :=
      map_sub (WittVector.constantCoeff : WittVector p B →+* B) _ _
    rw [h2, h1, WittVector.teichmuller_coeff_zero, sub_self]
  have hqV : WittVector.verschiebung (q.shift 1) = q := by
    rw [WittVector.verschiebung_shift q 0 (fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      exact hq0)]
    ext k
    rw [WittVector.shift_coeff, zero_add]
  have hp' : (p : WittVector p B) = WittVector.teichmuller p (p : B) + q := by
    rw [hq]; abel
  rw [hp', add_mul, ← map_mul, hpa, WittVector.teichmuller_zero, zero_add, ← hqV,
    ← WittVector.verschiebung_mul_frobenius, frobenius_teichmuller_eq_zero ha, mul_zero, map_zero]

section Datum

variable {j : Zp2 p →+* B} {φ : B →+* B'}
variable {D : GradedCartierModuleData p B j} {D' : GradedCartierModuleData p B' (φ.comp j)}

theorem iterate_verschiebung_zero (N : ℕ) : (⇑D.verschiebung)^[N] (0 : D.M) = 0 :=
  iterate_map_zero D.verschiebung N

theorem ker_step {f : D.M →+ D'.M} (hf : IsBaseChangeAlong φ D D' f) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (hγ' : D'.IsHomogeneousVBasis (fun i => f (γ i)))
    (m : D.M) (y' : D'.M) (h : f m = D'.verschiebung y') :
    ∃ (a : Fin 2 → B) (x' : D.M), (∀ i, φ (a i) = 0) ∧ f x' = y' ∧
      m = (∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) + D.verschiebung x' := by
  obtain ⟨⟨c, y⟩, hm, -⟩ := hγ.2 m

  have hfm : f m = (∑ i : Fin 2, WittVector.teichmuller p (φ (c i)) • f (γ i)) +
      D'.verschiebung (f y) := by
    rw [hm, map_add, map_sum, hf.2.2.1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf.1, WittVector.map_teichmuller]

  have hfm' : f m = (∑ i : Fin 2, WittVector.teichmuller p ((fun _ => (0 : B')) i) • f (γ i)) +
      D'.verschiebung y' := by
    rw [h]
    simp only [WittVector.teichmuller_zero, zero_smul, Finset.sum_const_zero, zero_add]
  obtain ⟨cy, hcy, huniq⟩ := hγ'.2 (f m)
  have e1 : ((fun i => φ (c i)), f y) = cy := huniq _ hfm
  have e2 : ((fun _ => (0 : B')), y') = cy := huniq _ hfm'
  have e := e1.trans e2.symm
  refine ⟨c, y, fun i => ?_, ?_, hm⟩
  · exact congrFun (congrArg Prod.fst e) i
  · exact congrArg Prod.snd e

theorem L_teichmuller_smul_eq_zero {L : D.M →+ D.NMod} (hL : D.IsCartierLMap L) {a : B}
    (ha : a * a = 0) (x : D.M) : L (WittVector.teichmuller p a • x) = 0 := by
  rw [hL.map_smul, frobenius_teichmuller_eq_zero ha, zero_smul]

theorem L_ker_shape {L : D.M →+ D.NMod} (hL : D.IsCartierLMap L) {γ : Fin 2 → D.M}
    {a : Fin 2 → B} (ha : ∀ i, a i * a i = 0) (x' : D.M) :
    L ((∑ i : Fin 2, WittVector.teichmuller p (a i) • γ i) + D.verschiebung x') =
      D.nMk (D.varpi x', 0) := by
  rw [map_add, map_sum, hL.map_verschiebung]
  have h0 : ∑ i : Fin 2, L (WittVector.teichmuller p (a i) • γ i) = 0 :=
    Finset.sum_eq_zero fun i _ => L_teichmuller_smul_eq_zero hL (ha i) (γ i)
  rw [h0, zero_add]

theorem nsmul_p_eq_zero_of_ker {f : D.M →+ D'.M} (hf : IsBaseChangeAlong φ D D' f)
    (hI2 : RingHom.ker φ * RingHom.ker φ = ⊥) (hIp : ∀ x ∈ RingHom.ker φ, (p : B) * x = 0)
    (hD : D.IsSpecialCartierModule) {γ : Fin 2 → D.M}
    (hγ : D.IsHomogeneousVBasis γ) (hγ' : D'.IsHomogeneousVBasis (fun i => f (γ i)))
    (x : D.M) (hx : f x = 0) : (p : ℕ) • x = 0 := by

  have key : ∀ N : ℕ, ∀ x : D.M, f x = 0 → ∃ t : D.M, (p : ℕ) • x = (⇑D.verschiebung)^[N] t := by
    intro N
    induction N with
    | zero => exact fun x _ => ⟨(p : ℕ) • x, rfl⟩
    | succ N ih =>
      intro x hx
      obtain ⟨a, x', ha, hx', hxe⟩ :=
        ker_step hf hγ hγ' x 0 (by rw [hx, map_zero])
      obtain ⟨t, ht⟩ := ih x' hx'
      refine ⟨t, ?_⟩
      have hdig : ∀ i, (p : ℕ) • (WittVector.teichmuller p (a i) • γ i) = 0 := fun i => by
        rw [← Nat.cast_smul_eq_nsmul (WittVector p B), smul_smul,
          natCast_mul_teichmuller_eq_zero (hIp _ (ha i)) (sq_eq_zero_of_mem hI2 (ha i)), zero_smul]
      rw [hxe, smul_add, Finset.smul_sum, Finset.sum_eq_zero (fun i _ => hdig i), zero_add,
        ← map_nsmul, ht, Function.iterate_succ_apply']

  obtain ⟨s, hs, huniq⟩ := hD.2 (fun _ => (0 : D.M))
  have h1 : (p : ℕ) • x = s := huniq _ (fun N => by
    obtain ⟨t, ht⟩ := key N x hx
    refine ⟨t, ?_⟩
    rw [ht, Finset.sum_eq_zero (fun m _ => iterate_verschiebung_zero m), zero_add])
  have h2 : (0 : D.M) = s := huniq _ (fun N => ⟨0, by
    rw [Finset.sum_eq_zero (fun m _ => iterate_verschiebung_zero m), iterate_verschiebung_zero,
      zero_add]⟩)
  rw [h1, ← h2]

end Datum

end C7Proof

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData C7Proof in
theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (hI2 : RingHom.ker φ * RingHom.ker φ = ⊥) (hIp : ∀ x ∈ RingHom.ker φ, (p : B) * x = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (z : D.NMod) (hz : D.nMap D' f hf.2.2.1 hf.2.2.2.1 z = 0) :
    D.nMap D' f hf.2.2.1 hf.2.2.2.1 (D.phi L hL.isCartierLMap.map_verschiebung z) = 0 ∧
      D.phi L hL.isCartierLMap.map_verschiebung
        (D.phi L hL.isCartierLMap.map_verschiebung (D.phi L hL.isCartierLMap.map_verschiebung z)) = 0 := by
  obtain ⟨γ, hγ, hγ'⟩ := hf.2.2.2.2.2
  have hLc := hL.isCartierLMap
  set hLV := hL.isCartierLMap.map_verschiebung

  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z

  have hz' : ∃ y' : D'.M, f m = D'.verschiebung y' ∧ f m' = -D'.varpi y' := by
    rw [nMap_nMk, nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hz
    rw [nRelMap_apply, Prod.mk.injEq] at hy
    refine ⟨D'.ofSigma y, hy.1.symm, ?_⟩
    have := congrArg D'.ofSigma hy.2
    rw [ofSigma_toSigma, ofSigma_toSigma] at this
    exact this.symm
  obtain ⟨y', hmy, hm'y⟩ := hz'

  obtain ⟨a, x', ha, hx', hme⟩ := ker_step hf hγ hγ' m y' hmy
  have ha2 : ∀ i, a i * a i = 0 := fun i => sq_eq_zero_of_mem hI2 (ha i)

  set n : D.M := D.varpi x' + m' with hn
  have h1 : D.phi L hLV (D.nMk (m, m')) = D.nMk (n, 0) := by
    rw [phi_nMk, hme, L_ker_shape hLc ha2, ← map_add, Prod.mk_add_mk, add_zero]
  have hfn : f n = 0 := by
    rw [hn, map_add, hf.2.2.2.1, hx', hm'y, add_neg_cancel]
  have hnMk0 : D.nMk (0, 0) = 0 := map_zero _
  refine ⟨?_, ?_⟩
  ·
    rw [h1, nMap_nMk, hfn, map_zero]
    exact map_zero D'.nMk
  ·
    obtain ⟨b, n', hb, hn', hne⟩ := ker_step hf hγ hγ' n 0 (by rw [hfn, map_zero])
    have hb2 : ∀ i, b i * b i = 0 := fun i => sq_eq_zero_of_mem hI2 (hb i)
    have h2 : D.phi L hLV (D.nMk (n, 0)) = D.nMk (D.varpi n', 0) := by
      rw [phi_nMk, hne, L_ker_shape hLc hb2, hnMk0, add_zero]

    obtain ⟨c, n'', hc, hn'', hn'e⟩ := ker_step hf hγ hγ' n' 0 (by rw [hn', map_zero])
    have hc2 : ∀ i, c i * c i = 0 := fun i => sq_eq_zero_of_mem hI2 (hc i)
    have hPi : D.varpi n' = (∑ i : Fin 2, WittVector.teichmuller p (c i) • D.varpi (γ i)) +
        D.verschiebung (D.varpi n'') := by
      rw [hn'e, map_add, map_sum, D.varpi_verschiebung]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => map_smul _ _ _)
    have h3 : D.phi L hLV (D.nMk (D.varpi n', 0)) = 0 := by
      rw [phi_nMk, hPi, L_ker_shape hLc hc2, D.varpi_varpi,
        nsmul_p_eq_zero_of_ker hf hI2 hIp hD hγ hγ' n'' hn'', hnMk0, add_zero]
    rw [h1, h2, h3]

end S_CerednikDrinfeld_GradedCartierModuleData_phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero (solution)
