-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bb640fb9-6e2e-501e-9a3a-dfc0b36ec900

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mGPCompl

section Witt

variable (p : ℕ) [hp : Fact p.Prime]

theorem witt_map_frobenius {R : Type u} {S : Type v} [CommRing R] [CommRing S] (g : R →+* S)
    (x : WittVector p R) :
    WittVector.map g (WittVector.frobenius x) = WittVector.frobenius (WittVector.map g x) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius, MvPolynomial.map_aeval,
    funext (WittVector.map_coeff g _)]
  rw [RingHom.ext_int ((g : R →+* S).comp (algebraMap ℤ R)) (algebraMap ℤ S), MvPolynomial.aeval_eq_eval₂Hom]

theorem ghostComponent_eq_of_coeff_eq {R : Type u} [CommRing R] (n : ℕ) (x y : WittVector p R)
    (h : ∀ i ≤ n, x.coeff i = y.coeff i) :
    WittVector.ghostComponent n x = WittVector.ghostComponent n y := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
    aeval_wittPolynomial]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem eq_of_forall_ghostComponent_eq {R : Type u} [CommRing R] (hpnz : (p : R) ∈ nonZeroDivisors R)
    (x y : WittVector p R) (h : ∀ k, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    x = y := by
  ext k
  exact WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) x y
    (fun i _ => h i) k (Nat.lt_succ_self k)

theorem eq_teichmuller_add_verschiebung_shift {R : Type u} [CommRing R] (w : WittVector p R) :
    w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung (w.shift 1) := by
  have h := WittVector.init_add_tail w 1
  have hi : WittVector.init 1 w = WittVector.teichmuller p (w.coeff 0) := by
    ext n
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p (w.coeff 0) (n + 1) (Nat.succ_pos n)]
  have ht : WittVector.tail 1 w = WittVector.verschiebung (w.shift 1) := by
    ext n
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.verschiebung_coeff_zero]
    | succ n => simp [WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, Nat.add_comm]
  rw [hi, ht] at h
  exact h.symm

theorem frobenius_sub_pow_mem {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (a : WittVector p k) :
    WittVector.frobenius a - a ^ p ∈ Ideal.span {(p : WittVector p k)} := by

  set y := a.shift 1
  obtain ⟨z, hz⟩ : ∃ z : WittVector p k, WittVector.frobenius z = y :=
    ⟨(WittVector.frobeniusEquiv p k).symm y, (WittVector.frobeniusEquiv p k).apply_symm_apply y⟩
  have hV : WittVector.verschiebung y = z * p := by rw [← hz, WittVector.verschiebung_frobenius]
  have ha : a = WittVector.teichmuller p (a.coeff 0) + z * p := by
    rw [← hV]; exact eq_teichmuller_add_verschiebung_shift p a
  have hmem : a - WittVector.teichmuller p (a.coeff 0) ∈ Ideal.span {(p : WittVector p k)} := by
    nth_rw 1 [ha]
    rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hF : WittVector.frobenius a - WittVector.teichmuller p (a.coeff 0) ^ p
      ∈ Ideal.span {(p : WittVector p k)} := by
    have : WittVector.frobenius (WittVector.teichmuller p (a.coeff 0))
        = WittVector.teichmuller p (a.coeff 0) ^ p := by
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
        ← map_pow]
    rw [← this, ← map_sub]
    nth_rw 1 [ha]
    rw [add_sub_cancel_left, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hP : a ^ p - WittVector.teichmuller p (a.coeff 0) ^ p ∈ Ideal.span {(p : WittVector p k)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_pow, map_pow]
    have h0 : Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) a =
        Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) (WittVector.teichmuller p (a.coeff 0)) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
    rw [h0]
  have := Ideal.sub_mem _ hF hP
  rwa [sub_sub_sub_cancel_right] at this

theorem frobenius_teichmuller {k : Type u} [CommRing k] [CharP k p] (c : k) :
    WittVector.frobenius (WittVector.teichmuller p c) = WittVector.teichmuller p c ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← map_pow]

theorem frobenius_iterate_teichmuller {k : Type u} [CommRing k] [CharP k p] (c : k) (n : ℕ) :
    (⇑(WittVector.frobenius (p := p) (R := k)))^[n] (WittVector.teichmuller p c)
      = WittVector.teichmuller p c ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_pow, frobenius_teichmuller, ← pow_mul,
      pow_succ, mul_comm]

theorem frobenius_frobenius_zp2 (a : CerednikDrinfeld.Zp2 p) :
    WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul]
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  rw [← sq, ← hcard, FiniteField.pow_card]

theorem p_mem_nonZeroDivisors_zp2 :
    (p : CerednikDrinfeld.Zp2 p) ∈ nonZeroDivisors (CerednikDrinfeld.Zp2 p) := by
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => CerednikDrinfeld.CartierLift.zp2_natCast_mul_eq_zero (p := p) x hx,
    fun x hx => CerednikDrinfeld.CartierLift.zp2_natCast_mul_eq_zero (p := p) x (by rwa [mul_comm] at hx)⟩

end Witt

section Main

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld

variable (p : ℕ) [hp : Fact p.Prime]

theorem endAct_mul_apply {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (φ ψ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct (φ * ψ) f = endAct φ (endAct ψ f) := by
  rw [map_mul]; rfl

private theorem _root_.P2mGPCompl.exists_generator :
    ∃ ζ : GaloisField p 2, ζ ^ p ≠ ζ ∧ ∀ c : GaloisField p 2, c ≠ 0 → ∃ k : ℕ, ζ ^ k = c := by
  classical
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hpow : ∀ c : GaloisField p 2, c ≠ 0 → ∃ k : ℕ, (g : GaloisField p 2) ^ k = c := by
    intro c hc
    have hmem : Units.mk0 c hc ∈ Submonoid.powers g := (mem_powers_iff_mem_zpowers).mpr (hg _)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    refine ⟨k, ?_⟩
    have := congrArg (fun u : (GaloisField p 2)ˣ => (u : GaloisField p 2)) hk
    simpa [Units.val_pow_eq_pow_val] using this
  refine ⟨(g : GaloisField p 2), fun hfix => ?_, hpow⟩

  have hcardF : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  have hord : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hcardF]
  have hgp : g ^ (p - 1) = 1 := by
    apply Units.ext
    have h1 : (g : GaloisField p 2) ^ (p - 1) * (g : GaloisField p 2) = (g : GaloisField p 2) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hfix]
    have hne : (g : GaloisField p 2) ≠ 0 := g.ne_zero
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_left_eq_self₀.mp h1 |>.resolve_right hne
  have hdvd : orderOf g ∣ p - 1 := orderOf_dvd_of_pow_eq_one hgp
  rw [hord] at hdvd
  have hle := Nat.le_of_dvd (by have := hp.out.two_le; omega) hdvd
  have : p * p ≤ p := by
    have := hp.out.two_le
    rw [pow_two] at hle; omega
  nlinarith [hp.out.two_le]

p2m_export "P2mGPCompl" "exists_generator"
variable {p}

theorem isCompl_gradedPiece {B : Type u} [CommRing B] (j : Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : FormalODModule p B) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) := by
  classical

  have hpnz := p_mem_nonZeroDivisors_zp2 p
  obtain ⟨θ, hθ⟩ := WittVector.exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift p hpnz
    (WittVector.frobenius (p := p) (R := GaloisField p 2)) (frobenius_sub_pow_mem p)
  have hθteich : ∀ c : GaloisField p 2, θ (WittVector.teichmuller p c) =
      WittVector.teichmuller p (WittVector.teichmuller p c) := by
    intro c
    apply eq_of_forall_ghostComponent_eq p hpnz
    intro k
    rw [hθ, WittVector.ghostComponent_teichmuller, frobenius_iterate_teichmuller]

  obtain ⟨ζ, hζp, hζgen⟩ := exists_generator p
  set z : Zp2 p := WittVector.teichmuller p ζ with hz
  set z' : Zp2 p := WittVector.frobenius z with hz'
  have hz'eq : z' = WittVector.teichmuller p (ζ ^ p) := by
    rw [hz', hz, frobenius_teichmuller, map_pow]
  have hσz' : WittVector.frobenius z' = z := by rw [hz', frobenius_frobenius_zp2]

  set s : Zp2 p := z + z' with hs
  set n : Zp2 p := z * z' with hn
  have hs_fix : WittVector.frobenius s = s := by rw [hs, map_add, hσz', ← hz', add_comm]
  have hn_fix : WittVector.frobenius n = n := by rw [hn, map_mul, hσz', ← hz', mul_comm]
  have hquad : z * z - s * z + n = 0 := by rw [hs, hn]; ring

  set α : WittVector p B := WittVector.map j (θ z) with hα
  set β : WittVector p B := WittVector.map j (θ z') with hβ
  have hα' : α = WittVector.teichmuller p (j (WittVector.teichmuller p ζ)) := by
    rw [hα, hz, hθteich, WittVector.map_teichmuller]
  have hβ' : β = WittVector.teichmuller p (j (WittVector.teichmuller p ζ) ^ p) := by
    rw [hβ, hz'eq, hθteich, WittVector.map_teichmuller, ← map_pow, ← map_pow]

  set T : AddMonoid.End (CartierModule p X.F) := endAct (X.actEnd z) with hT
  have hTw : ∀ (w : WittVector p B) (f : CartierModule p X.F), T (w • f) = w • T f :=
    fun w f => endAct_smul_witt _ w f

  have hW2 := CerednikDrinfeld.FormalODModule.endAct_actEnd_eq_map_smul_of_frobenius_eq_of_isNilpotent p j hB X θ hθ
  have hS : ∀ f : CartierModule p X.F, endAct (X.actEnd s) f = (α + β) • f := by
    intro f; rw [hW2 s hs_fix f, hs, map_add, map_add]
  have hN : ∀ f : CartierModule p X.F, endAct (X.actEnd n) f = (α * β) • f := by
    intro f; rw [hW2 n hn_fix f, hn, map_mul, map_mul]

  have hact_mul : ∀ a b : Zp2 p, X.actEnd (a * b) = X.actEnd a * X.actEnd b :=
    fun a b => map_mul X.actRingHom a b
  have hact_add : ∀ a b : Zp2 p, X.actEnd (a + b) = X.actEnd a + X.actEnd b :=
    fun a b => map_add X.actRingHom a b
  have hact_sub : ∀ a b : Zp2 p, X.actEnd (a - b) = X.actEnd a - X.actEnd b :=
    fun a b => map_sub X.actRingHom a b
  have hact_zero : X.actEnd (0 : Zp2 p) = 0 := map_zero X.actRingHom

  have hkey : ∀ f : CartierModule p X.F, T (T f) - (α + β) • T f + (α * β) • f = 0 := by
    intro f
    have h0 : endAct (X.actEnd (z * z - s * z + n)) f = 0 := by
      rw [hquad, hact_zero, map_zero]; rfl
    rw [hact_add, hact_sub, hact_mul, hact_mul, map_add, map_sub, map_mul, map_mul] at h0
    change endAct (X.actEnd z) (endAct (X.actEnd z) f) - endAct (X.actEnd s) (endAct (X.actEnd z) f)
      + endAct (X.actEnd n) f = 0 at h0
    rwa [hS, hN] at h0
  have hfac : ∀ f : CartierModule p X.F, T (T f - β • f) - α • (T f - β • f) = 0 := by
    intro f
    rw [map_sub, hTw, smul_sub, ← mul_smul]
    have := hkey f
    rw [add_smul] at this

    calc T (T f) - β • T f - (α • T f - (α * β) • f)
        = T (T f) - (α • T f + β • T f) + (α * β) • f := by abel
      _ = 0 := this
  have hfac' : ∀ f : CartierModule p X.F, T (T f - α • f) - β • (T f - α • f) = 0 := by
    intro f
    rw [map_sub, hTw, smul_sub, ← mul_smul, mul_comm β α]
    have := hkey f
    rw [add_smul] at this
    calc T (T f) - α • T f - (β • T f - (α * β) • f)
        = T (T f) - (α • T f + β • T f) + (α * β) • f := by abel
      _ = 0 := this

  have hu : IsUnit (z - z') := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have h0 : (z - z').coeff 0 = ζ - ζ ^ p := by
      have := WittVector.add_coeff_zero (z - z') z'
      rw [sub_add_cancel] at this
      have e1 : z.coeff 0 = ζ := by rw [hz, WittVector.teichmuller_coeff_zero]
      have e2 : z'.coeff 0 = ζ ^ p := by rw [hz'eq, WittVector.teichmuller_coeff_zero]
      rw [e1, e2] at this
      exact eq_sub_of_add_eq this.symm
    rw [h0]
    exact sub_ne_zero.mpr (Ne.symm hζp)
  obtain ⟨uinv, huinv⟩ : ∃ v : Zp2 p, (z - z') * v = 1 := hu.exists_right_inv
  set γ : WittVector p B := WittVector.map j (θ uinv) with hγ
  have hαβγ : (α - β) * γ = 1 := by
    rw [hα, hβ, hγ, ← map_sub, ← map_mul, ← map_sub, ← map_mul, huinv, map_one, map_one]
  have hγαβ : γ * (α - β) = 1 := by rw [mul_comm]; exact hαβγ

  have hsplit : ∀ f : CartierModule p X.F, γ • (T f - β • f) + (-γ) • (T f - α • f) = f := by
    intro f
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub]
    have : T f - β • f - (T f - α • f) = (α - β) • f := by rw [sub_smul]; abel
    rw [this, ← mul_smul, hγαβ, one_smul]
  have hker0 : ∀ f : CartierModule p X.F, T (γ • (T f - β • f)) = α • (γ • (T f - β • f)) := by
    intro f
    rw [hTw, ← sub_eq_zero, smul_comm α γ, ← smul_sub, hfac f, smul_zero]
  have hker1 : ∀ f : CartierModule p X.F, T ((-γ) • (T f - α • f)) = β • ((-γ) • (T f - α • f)) := by
    intro f
    rw [hTw, ← sub_eq_zero, smul_comm β (-γ), ← smul_sub, hfac' f, smul_zero]

  have hz_c : ∀ c : GaloisField p 2, c ≠ 0 → ∃ k : ℕ, WittVector.teichmuller p c = z ^ k := by
    intro c hc
    obtain ⟨k, rfl⟩ := hζgen c hc
    exact ⟨k, by rw [hz, map_pow]⟩
  have hTpow : ∀ (k : ℕ) (f : CartierModule p X.F) (w : WittVector p B), T f = w • f →
      endAct (X.actEnd (z ^ k)) f = (w ^ k) • f := by
    intro k f w hf
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul, show X.actEnd 1 = 1 from map_one X.actRingHom, map_one]; rfl
    | succ k ih =>
      rw [pow_succ, hact_mul, map_mul, pow_succ, mul_comm (w ^ k) w, mul_smul]
      change endAct (X.actEnd (z ^ k)) (T f) = w • (w ^ k • f)
      rw [hf, endAct_smul_witt, ih]
  have hmem : ∀ (m : ℕ) (f : CartierModule p X.F),
      T f = WittVector.teichmuller p (j (WittVector.teichmuller p ζ) ^ p ^ m) • f → f ∈ X.gradedPiece j m := by
    intro m f hf c
    by_cases hc : c = 0
    · rw [hc, WittVector.teichmuller_zero, hact_zero, map_zero, map_zero,
        zero_pow (pow_ne_zero _ hp.out.ne_zero), homothety_zero_left]
      rfl
    · obtain ⟨k, hk⟩ := hz_c c hc
      rw [hk, hTpow k f _ hf, ← map_pow (WittVector.teichmuller p), teichmuller_smul, map_pow j, hz,
        ← pow_mul, ← pow_mul, mul_comm]
  have hof : ∀ (m : ℕ) (f : CartierModule p X.F), f ∈ X.gradedPiece j m →
      T f = WittVector.teichmuller p (j (WittVector.teichmuller p ζ) ^ p ^ m) • f := by
    intro m f hf
    rw [teichmuller_smul]
    exact hf ζ

  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [AddSubgroup.disjoint_def]
    intro f h0 h1
    have e0 := hof 0 f h0
    have e1 := hof 1 f h1
    rw [pow_zero, pow_one, ← hα'] at e0
    rw [pow_one, ← hβ'] at e1
    have : (α - β) • f = 0 := by rw [sub_smul, ← e0, ← e1, sub_self]
    have := congrArg (fun x => γ • x) this
    simpa [← mul_smul, hγαβ] using this
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    rw [← hsplit f]
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (hmem 0 _ ?_)) (AddSubgroup.mem_sup_right (hmem 1 _ ?_))
    · rw [pow_zero, pow_one, ← hα']; exact hker0 f
    · rw [pow_one, ← hβ']; exact hker1 f

end Main

end P2mGPCompl

end

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) :=
  P2mGPCompl.isCompl_gradedPiece j hB X

end S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent (solution)
