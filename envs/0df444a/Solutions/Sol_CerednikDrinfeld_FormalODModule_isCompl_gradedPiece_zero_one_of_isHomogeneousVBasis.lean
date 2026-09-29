-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/11b13114-b7df-5e8d-9c57-5086424a74d5

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

import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Theorems.Thm_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mGradedVB

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

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

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_pow_ne : ∃ ζ : GaloisField p 2, ζ ^ p ≠ ζ := by
  classical
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  refine ⟨(g : GaloisField p 2), fun hfix => ?_⟩
  have hcardF : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  have hord : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hcardF]
  have hgp : g ^ (p - 1) = 1 := by
    apply Units.ext
    have h1 : (g : GaloisField p 2) ^ (p - 1) * (g : GaloisField p 2) = (g : GaloisField p 2) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hfix]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (mul_left_eq_self₀.mp h1).resolve_right g.ne_zero
  have hdvd : orderOf g ∣ p - 1 := orderOf_dvd_of_pow_eq_one hgp
  rw [hord] at hdvd
  have hle := Nat.le_of_dvd (by have := hp.out.two_le; omega) hdvd
  have : p * p ≤ p := by
    have := hp.out.two_le
    rw [pow_two] at hle; omega
  nlinarith [hp.out.two_le]

theorem isUnit_teichmuller_sub {ζ : GaloisField p 2} (h : ζ ^ p ≠ ζ) :
    IsUnit (WittVector.teichmuller p ζ - WittVector.frobenius (WittVector.teichmuller p ζ) : Zp2 p) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  have hz' : WittVector.frobenius (WittVector.teichmuller p ζ) = WittVector.teichmuller p (ζ ^ p) := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have := WittVector.add_coeff_zero
    (WittVector.teichmuller p ζ - WittVector.frobenius (WittVector.teichmuller p ζ) : Zp2 p)
    (WittVector.frobenius (WittVector.teichmuller p ζ))
  rw [sub_add_cancel, hz', WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at this
  rw [hz', eq_sub_of_add_eq this.symm]
  exact sub_ne_zero.mpr (Ne.symm h)

@[reducible] noncomputable def algebraPadicInt {B : Type u} [CommRing B] (j : Zp2 p →+* B) :
    Algebra (PadicInt p) B :=
  (j.comp ((WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp
    (WittVector.equiv p).symm.toRingHom)).toAlgebra

section main

variable {B : Type u} [CommRing B] (j : Zp2 p →+* B) (X : FormalODModule p B)

local notation "VV" => (verschiebungInt : CartierModule p X.F →+ CartierModule p X.F)

theorem eq_zero_of_forall_exists_iterate (x : CartierModule p X.F)
    (hx : ∀ N : ℕ, ∃ t : CartierModule p X.F, x = (⇑VV)^[N] t) : x = 0 := by
  have h := existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p X.F (fun _ => 0)
  refine h.unique ?_ ?_
  · intro N
    obtain ⟨t, ht⟩ := hx N
    exact ⟨t, by simpa [Function.iterate_fixed (map_zero _)] using ht⟩
  · intro N
    exact ⟨0, by simp [Function.iterate_fixed (map_zero _)]⟩

theorem iterate_V_sub (N : ℕ) (a b : CartierModule p X.F) :
    (⇑VV)^[N] (a - b) = (⇑VV)^[N] a - (⇑VV)^[N] b := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_sub]

theorem iterate_V_add (N : ℕ) (a b : CartierModule p X.F) :
    (⇑VV)^[N] (a + b) = (⇑VV)^[N] a + (⇑VV)^[N] b := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add]

theorem iterate_V_mem (N n : ℕ) (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    (⇑VV)^[N] f ∈ X.gradedPiece j (n + N) := by
  induction N with
  | zero => simpa using hf
  | succ N ih =>
    rw [Function.iterate_succ_apply', ← add_assoc]
    exact FormalODModule.verschiebungInt_mem_gradedPiece_succ X j _ _ ih

theorem mem_gradedPiece_of_forall (n : ℕ) (E : CartierModule p X.F)
    (hE : ∀ N : ℕ, ∃ S t, S ∈ X.gradedPiece j n ∧ E = S + (⇑VV)^[N] t) : E ∈ X.gradedPiece j n := by
  intro c
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_exists_iterate X _ fun N => ?_
  obtain ⟨S, t, hS, rfl⟩ := hE N
  refine ⟨endAct (X.actEnd (WittVector.teichmuller p c)) t -
    homothety ((j (WittVector.teichmuller p c) ^ p ^ n) ^ p ^ N) t, ?_⟩
  rw [map_add, map_add, hS c, iterate_V_sub]
  have h1 : ∀ (M : ℕ) (g : CartierModule p X.F),
      endAct (X.actEnd (WittVector.teichmuller p c)) ((⇑VV)^[M] g) = (⇑VV)^[M] (endAct (X.actEnd (WittVector.teichmuller p c)) g) := by
    intro M g
    induction M generalizing g with
    | zero => rfl
    | succ M ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', endAct_verschiebungInt, ih]
  have h2 : ∀ (M : ℕ) (a : B) (g : CartierModule p X.F),
      homothety a ((⇑VV)^[M] g) = (⇑VV)^[M] (homothety (a ^ p ^ M) g) := by
    intro M a g
    induction M generalizing a g with
    | zero => simp
    | succ M ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', homothety_verschiebungInt, ih, ← pow_mul,
        ← pow_succ']
  rw [h1, h2]
  abel

theorem eq_zero_of_mem_mem (f : CartierModule p X.F) (h0 : f ∈ X.gradedPiece j 0) (h1 : f ∈ X.gradedPiece j 1) :
    f = 0 := by
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
  obtain ⟨ζ, hζ⟩ := exists_pow_ne (p := p)
  set z : Zp2 p := WittVector.teichmuller p ζ with hz
  have hz' : WittVector.frobenius z = WittVector.teichmuller p (ζ ^ p) := by
    rw [hz, frobenius_teichmuller, map_pow]
  obtain ⟨uinv, huinv⟩ := (isUnit_teichmuller_sub (p := p) hζ).exists_right_inv

  have e0 := h0 ζ
  have e1 := h1 ζ
  rw [pow_zero, pow_one, ← teichmuller_smul] at e0
  rw [pow_one, ← teichmuller_smul] at e1
  have hα : WittVector.teichmuller p (j z) = WittVector.map j (θ z) := by
    rw [hz, hθteich, WittVector.map_teichmuller]
  have hβ : WittVector.teichmuller p (j z ^ p) = WittVector.map j (θ (WittVector.frobenius z)) := by
    rw [hz', hθteich, WittVector.map_teichmuller, ← map_pow j, hz, ← map_pow (WittVector.teichmuller p)]
  have hdiff : (WittVector.map j (θ (z - WittVector.frobenius z))) • f = 0 := by
    rw [map_sub, map_sub, sub_smul, ← hα, ← hβ, ← e0, ← e1, sub_self]
  have key := congrArg (fun x => WittVector.map j (θ uinv) • x) hdiff
  simp only [smul_zero] at key
  rw [← mul_smul, ← map_mul, ← map_mul, mul_comm uinv, hz, huinv, map_one, map_one, one_smul] at key
  exact key

theorem sum_iterate_mem (n : ℕ) (N : ℕ) (x : ℕ → CartierModule p X.F)
    (hx : ∀ m, (⇑VV)^[m] (x m) ∈ X.gradedPiece j n) :
    (∑ m ∈ Finset.range N, (⇑VV)^[m] (x m)) ∈ X.gradedPiece j n :=
  AddSubgroup.sum_mem _ fun m _ => hx m

theorem iterate_V_sum (N : ℕ) (s : Finset ℕ) (x : ℕ → CartierModule p X.F) :
    (⇑VV)^[N] (∑ m ∈ s, x m) = ∑ m ∈ s, (⇑VV)^[N] (x m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Function.iterate_fixed (map_zero _)]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterate_V_add, ih]

theorem iterate_V_homothety_mem (m : ℕ) (i : Fin 2) (b : B) (g : CartierModule p X.F)
    (hg : g ∈ X.gradedPiece j i) : (⇑VV)^[m] (homothety b g) ∈ X.gradedPiece j ((i : ℕ) + m) := by
  apply iterate_V_mem
  rw [← teichmuller_smul]
  exact FormalODModule.smul_mem_gradedPiece X j i _ g hg

end main

end P2mGradedVB

end

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule P2mGradedVB in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) := by
  classical
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [AddSubgroup.disjoint_def]
    intro f h0 h1
    exact eq_zero_of_mem_mem j X f h0 h1
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    letI : Algebra (PadicInt p) B := algebraPadicInt j

    have hexp' : ∀ N : ℕ, ∃ ch : (Fin N → Fin 2 → B) × CartierModule p X.F,
        (f = (∑ m : Fin N, (⇑verschiebungInt)^[(m : ℕ)] (∑ i : Fin 2, homothety (ch.1 m i) (γ i))) +
          (⇑verschiebungInt)^[N] ch.2) ∧
        ∀ (c' : Fin N → Fin 2 → B) (t' : CartierModule p X.F),
          f = (∑ m : Fin N, (⇑verschiebungInt)^[(m : ℕ)] (∑ i : Fin 2, homothety (c' m i) (γ i))) +
            (⇑verschiebungInt)^[N] t' → c' = ch.1 := by
      intro N
      have h := MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
        p X.F γ hγ.2 f N
      obtain ⟨ch, hch, huniq⟩ := h
      exact ⟨ch, hch, fun c' t' h' => congrArg Prod.fst (huniq (c', t') h')⟩
    choose ch hch huniq using hexp'

    have hcompat : ∀ (N : ℕ) (m : Fin N), (ch (N + 1)).1 m.castSucc = (ch N).1 m := by
      intro N m
      have hcand : f = (∑ m : Fin N, (⇑verschiebungInt)^[(m : ℕ)]
            (∑ i : Fin 2, homothety ((ch (N + 1)).1 m.castSucc i) (γ i))) +
          (⇑verschiebungInt)^[N] ((∑ i : Fin 2, homothety ((ch (N + 1)).1 (Fin.last N) i) (γ i)) +
            verschiebungInt (ch (N + 1)).2) := by
        conv_lhs => rw [hch (N + 1)]
        rw [Fin.sum_univ_castSucc, iterate_V_add, add_assoc]
        simp only [Fin.coe_castSucc, Fin.val_last]
        rw [Function.iterate_succ_apply]
      have := huniq N (fun m => (ch (N + 1)).1 m.castSucc) _ hcand
      exact congrFun this m

    obtain ⟨d, hd⟩ : ∃ d : ℕ → Fin 2 → B, ∀ m, d m = (ch (m + 1)).1 (Fin.last m) := ⟨_, fun _ => rfl⟩
    have hdig : ∀ (N : ℕ) (m : Fin N), (ch N).1 m = d m := by
      intro N
      induction N with
      | zero => intro m; exact m.elim0
      | succ N ih =>
        intro m
        refine Fin.lastCases ?_ (fun m' => ?_) m
        · rw [hd, Fin.val_last]
        · rw [Fin.coe_castSucc, hcompat N m', ih m']

    obtain ⟨e, he⟩ : ∃ e : ℕ → CartierModule p X.F, ∀ m,
        e m = if m % 2 = 0 then homothety (d m 0) (γ 0) else homothety (d m 1) (γ 1) := ⟨_, fun _ => rfl⟩
    obtain ⟨o, ho⟩ : ∃ o : ℕ → CartierModule p X.F, ∀ m,
        o m = if m % 2 = 0 then homothety (d m 1) (γ 1) else homothety (d m 0) (γ 0) := ⟨_, fun _ => rfl⟩
    have heo : ∀ m, (∑ i : Fin 2, homothety (d m i) (γ i)) = e m + o m := by
      intro m
      rw [Fin.sum_univ_two, he, ho]
      split_ifs <;> abel
    have he0 : ∀ m, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[m] (e m) ∈ X.gradedPiece j 0 := by
      intro m
      rw [he]
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [if_pos (by omega), ← FormalODModule.gradedPiece_add_two_mul X j 0 k]
        have := iterate_V_homothety_mem j X m 0 (d m 0) (γ 0) (hγ.1 0)
        rw [Fin.val_zero] at this
        convert this using 2; omega
      · rw [if_neg (by omega), ← FormalODModule.gradedPiece_add_two_mul X j 0 (k + 1)]
        have := iterate_V_homothety_mem j X m 1 (d m 1) (γ 1) (hγ.1 1)
        rw [Fin.val_one] at this
        convert this using 2; omega
    have ho1 : ∀ m, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[m] (o m) ∈ X.gradedPiece j 1 := by
      intro m
      rw [ho]
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [if_pos (by omega), ← FormalODModule.gradedPiece_add_two_mul X j 1 k]
        have := iterate_V_homothety_mem j X m 1 (d m 1) (γ 1) (hγ.1 1)
        rw [Fin.val_one] at this
        convert this using 2; omega
      · rw [if_neg (by omega), ← FormalODModule.gradedPiece_add_two_mul X j 1 k]
        have := iterate_V_homothety_mem j X m 0 (d m 0) (γ 0) (hγ.1 0)
        rw [Fin.val_zero] at this
        convert this using 2; omega

    obtain ⟨E, hE, -⟩ := MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p X.F e
    obtain ⟨O, hO, -⟩ := MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p X.F o
    have hEmem : E ∈ X.gradedPiece j 0 := mem_gradedPiece_of_forall j X 0 E fun N => by
      obtain ⟨t, ht⟩ := hE N
      exact ⟨_, t, sum_iterate_mem j X 0 N e he0, ht⟩
    have hOmem : O ∈ X.gradedPiece j 1 := mem_gradedPiece_of_forall j X 1 O fun N => by
      obtain ⟨t, ht⟩ := hO N
      exact ⟨_, t, sum_iterate_mem j X 1 N o ho1, ht⟩

    have hfEO : f - (E + O) = 0 := by
      refine eq_zero_of_forall_exists_iterate X _ fun N => ?_
      obtain ⟨a, ha⟩ := hE N
      obtain ⟨b, hb⟩ := hO N
      refine ⟨(ch N).2 - (a + b), ?_⟩
      have hterm : ∀ m : Fin N, (∑ i : Fin 2, homothety ((ch N).1 m i) (γ i)) = e m + o m := fun m => by
        rw [← heo]; exact Finset.sum_congr rfl fun i _ => by rw [hdig]
      have hsum : (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
            (∑ i : Fin 2, homothety ((ch N).1 m i) (γ i))) =
          ∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[m] (e m + o m) := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun m _ => by rw [hterm]
      have hf : f = (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[m] (e m + o m)) + (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[N] (ch N).2 := by
        rw [← hsum]; exact hch N
      rw [hf, ha, hb, iterate_V_sub, iterate_V_add]
      simp only [iterate_V_add, Finset.sum_add_distrib]
      abel
    rw [sub_eq_zero] at hfEO
    rw [hfEO]
    exact AddSubgroup.add_mem_sup hEmem hOmem

end S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis (solution)
