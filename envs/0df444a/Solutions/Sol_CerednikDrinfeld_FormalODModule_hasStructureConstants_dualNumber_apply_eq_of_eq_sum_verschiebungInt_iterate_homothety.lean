-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/90bdfc72-efd2-5fa8-8476-f92f5f5a7ca4

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
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety

set_option autoImplicit false

noncomputable section

universe u

namespace P2mOSCarry

p2m_open "WittVector P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.WittVector"

theorem add_pow_of_mul_self_eq_zero {A : Type*} [CommRing A] (a e : A) (he : e * e = 0) (N : ℕ) :
    (a + e) ^ N = a ^ N + (N : A) * a ^ (N - 1) * e := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, Nat.cast_succ, Nat.add_sub_cancel]
    have h2 : (N : A) * a ^ (N - 1) * e * e = 0 := by rw [mul_assoc, he, mul_zero]
    rw [h2, add_zero, ← pow_succ]
    rcases N with _ | N
    · simp
    · rw [Nat.add_sub_cancel, Nat.cast_succ]
      ring

theorem pow_eq_zero_of_mul_self_eq_zero {A : Type*} [CommRing A] (e : A) (he : e * e = 0) {m : ℕ}
    (hm : 2 ≤ m) : e ^ m = 0 :=
  pow_eq_zero_of_le hm (by rw [pow_two]; exact he)

variable (p : ℕ) [hp : Fact p.Prime]

theorem coeff_univ (n : ℕ) :
    ((teichmuller p (TrivSqZeroExt.inl Polynomial.X : DualNumber (Polynomial ℤ)) +
        teichmuller p (DualNumber.eps : DualNumber (Polynomial ℤ))).coeff 0 =
        TrivSqZeroExt.inl Polynomial.X + DualNumber.eps) ∧
    (1 ≤ n → (teichmuller p (TrivSqZeroExt.inl Polynomial.X : DualNumber (Polynomial ℤ)) +
        teichmuller p (DualNumber.eps : DualNumber (Polynomial ℤ))).coeff n =
      -((TrivSqZeroExt.inl Polynomial.X : DualNumber (Polynomial ℤ)) ^ (p ^ n - 1) * DualNumber.eps)) := by
  set X' : DualNumber (Polynomial ℤ) := TrivSqZeroExt.inl Polynomial.X with hX'
  set E : DualNumber (Polynomial ℤ) := DualNumber.eps with hE
  set Z : WittVector p (DualNumber (Polynomial ℤ)) := teichmuller p X' + teichmuller p E with hZ
  have hE2 : E * E = 0 := DualNumber.eps_mul_eps
  have hp2 : 2 ≤ p := hp.out.two_le

  have hghost : ∀ m, ghostComponent m Z = X' ^ p ^ m + E ^ p ^ m := fun m => by
    rw [hZ, map_add, ghostComponent_teichmuller, ghostComponent_teichmuller]
  have hghost' : ∀ m, ghostComponent m Z =
      ∑ i ∈ Finset.range (m + 1), (p : DualNumber (Polynomial ℤ)) ^ i * Z.coeff i ^ p ^ (m - i) :=
    fun m => by rw [ghostComponent_apply, aeval_wittPolynomial]

  have htf : ∀ (k : ℕ) (u : DualNumber (Polynomial ℤ)), ((p : DualNumber (Polynomial ℤ)) ^ k) * u = 0 → u = 0 := by
    intro k u h
    rw [← Nat.cast_pow] at h
    have hm : ((p ^ k : ℕ) : Polynomial ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero k hp.out.ne_zero)
    have h1 : ((p ^ k : ℕ) : Polynomial ℤ) * u.fst = 0 := by
      have := congrArg TrivSqZeroExt.fst h
      rwa [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.fst_zero] at this
    have h2 : ((p ^ k : ℕ) : Polynomial ℤ) * u.snd = 0 := by
      have := congrArg TrivSqZeroExt.snd h
      rwa [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast, smul_zero, add_zero,
        smul_eq_mul] at this
    exact TrivSqZeroExt.ext ((mul_eq_zero.mp h1).resolve_left hm) ((mul_eq_zero.mp h2).resolve_left hm)

  have h0 : Z.coeff 0 = X' + E := by
    have h := (hghost' 0).symm.trans (hghost 0)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul, Nat.sub_zero,
      Nat.sub_self, pow_one] at h
    exact h
  have hpn : ∀ m : ℕ, 1 ≤ m → 2 ≤ p ^ m := fun m hm => le_trans hp2 (Nat.le_self_pow (by omega) p)

  have key : ∀ n, 1 ≤ n → Z.coeff n = -(X' ^ (p ^ n - 1) * E) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hsum := (hghost' n).symm.trans (hghost n)
      have hmid : ∀ i ∈ Finset.range n, i ≠ 0 →
          (p : DualNumber (Polynomial ℤ)) ^ i * Z.coeff i ^ p ^ (n - i) = 0 := by
        intro i hi hi0
        have hi' := Finset.mem_range.mp hi
        have h1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        have hE0 : E ^ p ^ (n - i) = 0 := pow_eq_zero_of_mul_self_eq_zero E hE2 (hpn (n - i) (by omega))
        rw [ih i hi' h1, neg_mul_eq_neg_mul, mul_pow, hE0, mul_zero, mul_zero]
      have hsplit : ∑ i ∈ Finset.range (n + 1), (p : DualNumber (Polynomial ℤ)) ^ i * Z.coeff i ^ p ^ (n - i) =
          Z.coeff 0 ^ p ^ n + (p : DualNumber (Polynomial ℤ)) ^ n * Z.coeff n := by
        rw [Finset.sum_range_succ, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) hmid,
          pow_zero, one_mul, Nat.sub_zero, Nat.sub_self, pow_zero, pow_one]
      have hEn : E ^ p ^ n = 0 := pow_eq_zero_of_mul_self_eq_zero E hE2 (hpn n hn)
      have hbin : Z.coeff 0 ^ p ^ n = X' ^ p ^ n + ((p : DualNumber (Polynomial ℤ)) ^ n) * X' ^ (p ^ n - 1) * E := by
        rw [h0, add_pow_of_mul_self_eq_zero X' E hE2, Nat.cast_pow]
      rw [hsplit, hbin, hEn, add_zero] at hsum
      have h3 : (p : DualNumber (Polynomial ℤ)) ^ n * (X' ^ (p ^ n - 1) * E + Z.coeff n) = 0 := by
        linear_combination hsum
      exact eq_neg_of_add_eq_zero_right (htf n _ h3)
  exact ⟨h0, key n⟩

end P2mOSCarry

namespace WittVector p2m_export "WittVector" "ghostComponent verschiebung_coeff_zero coeff map eq_iterate_verschiebung lift add_coeff_zero map_teichmuller frobenius shift verschiebung_coeff_succ ext verschiebung_frobenius zero_coeff verschiebung_mul_frobenius verschiebung map_verschiebung truncate teichmuller_coeff_zero ghostComponent_apply map_coeff ghostComponent_teichmuller teichmuller" end WittVector
p2m_open_scoped "WittVector" in

theorem WittVector.coeff_teichmuller_add_teichmuller_of_mul_self_eq_zero
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (x e : B) (he : e * e = 0) :
    (WittVector.teichmuller p x + WittVector.teichmuller p e).coeff 0 = x + e ∧
    ∀ n : ℕ, 1 ≤ n →
      (WittVector.teichmuller p x + WittVector.teichmuller p e).coeff n = -(x ^ (p ^ n - 1) * e) := by
  let f : Polynomial ℤ →ₐ[ℤ] B := Polynomial.aeval x
  let φ : DualNumber (Polynomial ℤ) →ₐ[ℤ] B :=
    DualNumber.lift ⟨(f, e), ⟨he, fun a => Commute.all _ _⟩⟩
  have hφX : φ (TrivSqZeroExt.inl Polynomial.X) = x := by
    show DualNumber.lift _ (TrivSqZeroExt.inl Polynomial.X : DualNumber (Polynomial ℤ)) = x
    rw [DualNumber.lift_apply_inl]
    exact Polynomial.aeval_X x
  have hφE : φ DualNumber.eps = e := DualNumber.lift_apply_eps _
  have hmap : WittVector.map φ.toRingHom
      (WittVector.teichmuller p (TrivSqZeroExt.inl Polynomial.X : DualNumber (Polynomial ℤ)) +
        WittVector.teichmuller p (DualNumber.eps : DualNumber (Polynomial ℤ))) =
      WittVector.teichmuller p x + WittVector.teichmuller p e := by
    rw [map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]
    show WittVector.teichmuller p (φ _) + WittVector.teichmuller p (φ _) = _
    rw [hφX, hφE]
  refine ⟨?_, fun n hn => ?_⟩
  · rw [← hmap, WittVector.map_coeff, (P2mOSCarry.coeff_univ p 0).1, map_add]
    show φ _ + φ _ = _
    rw [hφX, hφE]
  · rw [← hmap, WittVector.map_coeff, (P2mOSCarry.coeff_univ p n).2 hn, map_neg, map_mul, map_pow]
    show -(φ _ ^ _ * φ _) = _
    rw [hφX, hφE]

namespace P2mW3

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

theorem hasSubst_frob_mul (u : WittVector p R) :
    HasSubst (fun n => subst (WittLaw.frobPolyFam p R) (WittLaw.mulFam p u n)) := by
  simpa only [substAlgHom_apply] using HasSubst.comp (WittLaw.hasSubst_mulFam u) (WittLaw.hasSubst_frobPolyFam (p := p) (R := R))

theorem mulFam_verschiebung (u : WittVector p R) (m : ℕ) :
    WittLaw.mulFam p (WittVector.verschiebung u) m =
      subst (fun n => subst (WittLaw.frobPolyFam p R) (WittLaw.mulFam p u n)) (WittLaw.verFam R m) := by
  have hV := hasSubst_frob_mul (p := p) (R := R) u
  have key : WittLaw.cVec p (τ := ℕ) (WittVector.verschiebung u) * WittLaw.xTaut p R =
      WittVector.verschiebung (WittLaw.cVec p u * WittVector.frobenius (WittLaw.xTaut p R)) := by
    rw [WittVector.verschiebung_mul_frobenius]
    congr 1
    exact WittVector.map_verschiebung _ _
  rw [WittLaw.mulFam_apply, show WittLaw.mulPoly p (WittVector.verschiebung u) m =
    (WittLaw.cVec p (τ := ℕ) (WittVector.verschiebung u) * WittLaw.xTaut p R).coeff m from rfl, key]
  cases m with
  | zero =>
    rw [WittVector.verschiebung_coeff_zero, MvPolynomial.coe_zero, WittLaw.verFam_zero,
      ← coe_substAlgHom hV, map_zero]
  | succ k =>
    rw [WittVector.verschiebung_coeff_succ, WittLaw.verFam_succ, subst_X hV, ← WittLaw.mk_frobPoly,
      ← WittLaw.aeval_mulPoly, WittLaw.coe_aeval]
    rfl

theorem verschiebung_smul_eq [Φ.IsComm] (u : WittVector p R) (f : MvFormalGroup.CartierModule p Φ) :
    WittVector.verschiebung u • f = verschiebungInt (u • frobenius f) := by
  have hV := hasSubst_frob_mul (p := p) (R := R) u
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_smul_witt, toPowerSeries_verschiebungInt, toPowerSeries_smul_witt, toPowerSeries_frobenius]
  beta_reduce
  have hVM : HasSubst (fun s => subst (WittLaw.mulFam p u) (WittLaw.verFam R s)) := by
    simpa only [substAlgHom_apply] using HasSubst.comp WittLaw.hasSubst_verFam (WittLaw.hasSubst_mulFam (p := p) u)
  rw [subst_comp_subst_apply (WittLaw.hasSubst_verFam) (WittLaw.hasSubst_mulFam u),
    subst_comp_subst_apply hVM WittLaw.hasSubst_frobPolyFam]
  congr 1
  funext m
  rw [mulFam_verschiebung u m]
  cases m with
  | zero =>
    rw [WittLaw.verFam_zero, ← coe_substAlgHom hV, map_zero,
      ← coe_substAlgHom (WittLaw.hasSubst_mulFam u), map_zero,
      ← coe_substAlgHom WittLaw.hasSubst_frobPolyFam, map_zero]
  | succ k =>
    rw [WittLaw.verFam_succ, subst_X hV, subst_X (WittLaw.hasSubst_mulFam u)]

theorem smul_eq_homothety_add_verschiebungInt [Φ.IsComm] (w : WittVector p R) (f : MvFormalGroup.CartierModule p Φ) :
    w • f = homothety (w.coeff 0) f +
      verschiebungInt (((w - WittVector.teichmuller p (w.coeff 0)).shift 1) • frobenius f) := by
  set z := w - WittVector.teichmuller p (w.coeff 0) with hz
  have hz0 : z.coeff 0 = 0 := by
    have h := WittVector.add_coeff_zero z (WittVector.teichmuller p (w.coeff 0))
    rw [show z + WittVector.teichmuller p (w.coeff 0) = w from sub_add_cancel _ _,
      WittVector.teichmuller_coeff_zero] at h
    linear_combination (-1 : R) * h
  have hzV : z = WittVector.verschiebung (z.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := z) (n := 1) (fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; exact hz0)
    simpa using this
  have hw : w = WittVector.teichmuller p (w.coeff 0) + z := by rw [hz]; abel
  conv_lhs => rw [hw]
  rw [add_smul, teichmuller_smul, hzV, verschiebung_smul_eq, ← hzV]

theorem homothety_add_homothety [Φ.IsComm] (x y : R) (f : MvFormalGroup.CartierModule p Φ) :
    homothety x f + homothety y f = homothety (x + y) f +
      verschiebungInt ((((WittVector.teichmuller p x + WittVector.teichmuller p y) -
        WittVector.teichmuller p (x + y)).shift 1) • frobenius f) := by
  have h := smul_eq_homothety_add_verschiebungInt (WittVector.teichmuller p x + WittVector.teichmuller p y) f
  rw [WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h
  calc homothety x f + homothety y f
      = (WittVector.teichmuller p x + WittVector.teichmuller p y) • f := by
        rw [add_smul, teichmuller_smul, teichmuller_smul]
    _ = _ := h

theorem homothety_add_homothety_of_frobenius [Φ.IsComm] (x y : R) (f : MvFormalGroup.CartierModule p Φ)
    {g : MvFormalGroup.CartierModule p Φ} (hf : frobenius f = verschiebungInt g) :
    ∃ r, homothety x f + homothety y f = homothety (x + y) f + verschiebungInt (verschiebungInt r) := by
  refine ⟨WittVector.frobenius (((WittVector.teichmuller p x + WittVector.teichmuller p y) -
        WittVector.teichmuller p (x + y)).shift 1) • g, ?_⟩
  rw [homothety_add_homothety, hf, smul_verschiebungInt]

theorem teichmuller_add_teichmuller_neg (e : R) (he : e * e = 0) :
    WittVector.teichmuller p e + WittVector.teichmuller p (-e) = 0 := by
  have hne : (-e) * (-e) = 0 := by rw [neg_mul_neg, he]
  have hc := WittVector.coeff_teichmuller_add_teichmuller_of_mul_self_eq_zero p e (-e) hne
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hc.1, WittVector.zero_coeff, add_neg_cancel]
  · rw [hc.2 n hn, WittVector.zero_coeff, mul_neg, neg_neg, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_pow n p hp.out.pos)]
    exact P2mOSCarry.pow_eq_zero_of_mul_self_eq_zero e he
      (le_trans hp.out.two_le (Nat.le_self_pow (by omega) p))

theorem homothety_neg_eps [Φ.IsComm] (e : R) (he : e * e = 0) (f : MvFormalGroup.CartierModule p Φ) :
    homothety (-e) f = -homothety e f := by
  rw [eq_neg_iff_add_eq_zero, add_comm]
  calc homothety e f + homothety (-e) f
      = (WittVector.teichmuller p e + WittVector.teichmuller p (-e)) • f := by
        rw [add_smul, teichmuller_smul, teichmuller_smul]
    _ = 0 := by rw [teichmuller_add_teichmuller_neg e he, zero_smul]

end P2mW3

namespace P2mW3

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

def E₂ {q : ℕ} {k : Type u} [Field k] (a : ℕ → Fin 2 → k) (s v : Fin 2 → k) (i : Fin 2) (m : Fin 2) (l : Fin 2) :
    DualNumber k :=
  if (m : ℕ) = 0 then
    (if l = CerednikDrinfeld.FormalODModule.piIndex 0 i then
      algebraMap k (DualNumber k) (a 0 i) + ((s i - s (CerednikDrinfeld.FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps
     else 0)
  else
    (if l = i then
      algebraMap k (DualNumber k) (a 1 i) +
        (v i * a 0 (CerednikDrinfeld.FormalODModule.piIndex 0 i) - a 0 i ^ q * v (CerednikDrinfeld.FormalODModule.piIndex 0 i)
          - a 1 i * s i) • DualNumber.eps
     else 0)

def E₃ {q : ℕ} {k : Type u} [Field k] (a : ℕ → Fin 2 → k) (s v : Fin 2 → k) (i₀ : Fin 2) (m : Fin 3) (l : Fin 2) :
    DualNumber k :=
  if (m : ℕ) = 0 then 0
  else if (m : ℕ) = 1 then
    (if l = i₀ then
      algebraMap k (DualNumber k) (a 1 i₀) +
        (v i₀ * a 0 (CerednikDrinfeld.FormalODModule.piIndex 0 i₀) - a 0 i₀ ^ q * v (CerednikDrinfeld.FormalODModule.piIndex 0 i₀)
          - a 1 i₀ * s i₀) • DualNumber.eps
     else 0)
  else
    (if l = CerednikDrinfeld.FormalODModule.piIndex 0 i₀ then
      algebraMap k (DualNumber k) (a 2 i₀) -
        (a 1 i₀ ^ q * v i₀ + a 2 i₀ * s (CerednikDrinfeld.FormalODModule.piIndex 0 i₀)) • DualNumber.eps
     else 0)

section KitBridge
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
theorem homothety_add_homothety_ex [Φ.IsComm] (x y : R) (f : MvFormalGroup.CartierModule p Φ) :
    ∃ r, homothety x f + homothety y f = homothety (x + y) f + verschiebungInt r :=
  ⟨_, homothety_add_homothety x y f⟩
end KitBridge

section ModV

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

def ModV (n : ℕ) (x y : MvFormalGroup.CartierModule p Φ) : Prop :=
  ∃ r, x = y + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] r

theorem ModV.rfl' (n : ℕ) (x : MvFormalGroup.CartierModule p Φ) : ModV n x x :=
  ⟨0, by rw [iterate_map_zero, add_zero]⟩

theorem ModV.trans {n : ℕ} {x y z : MvFormalGroup.CartierModule p Φ} (h₁ : ModV n x y) (h₂ : ModV n y z) :
    ModV n x z := by
  obtain ⟨r₁, h₁⟩ := h₁; obtain ⟨r₂, h₂⟩ := h₂
  exact ⟨r₂ + r₁, by rw [h₁, h₂, iterate_map_add, add_assoc]⟩

theorem ModV.add {n : ℕ} {x y x' y' : MvFormalGroup.CartierModule p Φ} (h : ModV n x y) (h' : ModV n x' y') :
    ModV n (x + x') (y + y') := by
  obtain ⟨r, h⟩ := h; obtain ⟨r', h'⟩ := h'
  exact ⟨r + r', by rw [h, h', iterate_map_add]; abel⟩

theorem ModV.of_eq {n : ℕ} {x y : MvFormalGroup.CartierModule p Φ} (h : x = y) : ModV n x y := h ▸ ModV.rfl' n x

theorem ModV.iterate_zero (n : ℕ) (r : MvFormalGroup.CartierModule p Φ) :
    ModV n ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] r) 0 := ⟨r, by rw [zero_add]⟩

theorem ModV.mono {n m : ℕ} (hmn : m ≤ n) {x y : MvFormalGroup.CartierModule p Φ} (h : ModV n x y) : ModV m x y := by
  obtain ⟨r, h⟩ := h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact ⟨(⇑(verschiebungInt (p := p) (Φ := Φ)))^[j] r, by rw [h, ← Function.iterate_add_apply]⟩

theorem ModV.verschiebungInt {n : ℕ} {x y : MvFormalGroup.CartierModule p Φ} (h : ModV n x y) :
    ModV (n + 1) (CartierModule.verschiebungInt x) (CartierModule.verschiebungInt y) := by
  obtain ⟨r, h⟩ := h
  exact ⟨r, by rw [h, map_add, Function.iterate_succ_apply']⟩

theorem ModV.iterate {n : ℕ} (j : ℕ) {x y : MvFormalGroup.CartierModule p Φ} (h : ModV n x y) :
    ModV (n + j) ((⇑(CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[j] x)
      ((⇑(CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[j] y) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← add_assoc]
    exact ih.verschiebungInt

theorem homothety_iterate (c : R) (n : ℕ) (r : MvFormalGroup.CartierModule p Φ) :
    homothety c ((⇑(CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n] r) =
      (⇑(CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n] (homothety (c ^ p ^ n) r) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', homothety_verschiebungInt, ih, ← pow_mul,
      ← pow_succ']

theorem ModV.homothety {n : ℕ} (c : R) {x y : MvFormalGroup.CartierModule p Φ} (h : ModV n x y) :
    ModV n (CartierModule.homothety c x) (CartierModule.homothety c y) := by
  obtain ⟨r, h⟩ := h
  exact ⟨CartierModule.homothety (c ^ p ^ n) r, by rw [h, map_add, homothety_iterate]⟩

theorem ModV.merge (x y : R) (f : MvFormalGroup.CartierModule p Φ) :
    ModV 1 (CartierModule.homothety x f + CartierModule.homothety y f) (CartierModule.homothety (x + y) f) := by
  obtain ⟨r, h⟩ := homothety_add_homothety_ex (p := p) x y f
  exact ⟨r, by rw [h, Function.iterate_one]⟩

theorem ModV.merge₂ (x y : R) (f : MvFormalGroup.CartierModule p Φ) {g : MvFormalGroup.CartierModule p Φ}
    (hf : frobenius f = CartierModule.verschiebungInt g) :
    ModV 2 (CartierModule.homothety x f + CartierModule.homothety y f) (CartierModule.homothety (x + y) f) := by
  obtain ⟨r, h⟩ := homothety_add_homothety_of_frobenius (p := p) x y f hf
  refine ⟨r, ?_⟩
  rw [h]
  rfl

end ModV

section Eps

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

theorem eps_smul_mul_eps_smul (a b : k) : (a • DualNumber.eps : DualNumber k) * (b • DualNumber.eps) = 0 := by
  rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]

set_option synthInstance.checkSynthOrder false in
scoped instance charP_dualNumber' : CharP (DualNumber k) q :=
  charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

theorem one_add_eps_smul_pow (s : k) {n : ℕ} (hn : 1 ≤ n) :
    ((1 : DualNumber k) + s • DualNumber.eps) ^ (q ^ n) = 1 := by
  have h2 : (s • DualNumber.eps : DualNumber k) * (s • DualNumber.eps) = 0 := eps_smul_mul_eps_smul s s

  have key : ∀ N : ℕ, ((1 : DualNumber k) + s • DualNumber.eps) ^ N = 1 + (N : DualNumber k) * (s • DualNumber.eps) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ, ih, Nat.cast_succ]
      linear_combination (N : DualNumber k) * h2
  rw [key, Nat.cast_pow, CharP.cast_eq_zero (DualNumber k) q, zero_pow (by omega), zero_mul, add_zero]

theorem eps_smul_pow (c : k) {n : ℕ} (hn : 2 ≤ n) : (c • DualNumber.eps : DualNumber k) ^ n = 0 :=
  pow_eq_zero_of_le hn (by rw [pow_two]; exact eps_smul_mul_eps_smul c c)

theorem algebraMap_mul_eps_smul (a c : k) :
    algebraMap k (DualNumber k) a * (c • DualNumber.eps) = (a * c) • DualNumber.eps := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]

end Eps

section Combine

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

local notation "Kε" => DualNumber k

theorem piIndex_zero_piIndex_zero (i : Fin 2) :
    FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := by
  fin_cases i <;> rfl

theorem piIndex_zero_ne (i : Fin 2) : FormalODModule.piIndex 0 i ≠ i := by
  fin_cases i <;> decide

theorem ne_piIndex_zero (i : Fin 2) : i ≠ FormalODModule.piIndex 0 i := fun h => piIndex_zero_ne i h.symm

theorem sum_homothety_ite {d : ℕ} {Φ : MvFormalGroup d Kε} [Φ.IsComm] (j : Fin 2) (c : Kε)
    (f : Fin 2 → MvFormalGroup.CartierModule q Φ) :
    (∑ l : Fin 2, homothety (if l = j then c else 0) (f l)) = homothety c (f j) := by
  have h : ∀ l : Fin 2, homothety (if l = j then c else 0) (f l) = if l = j then homothety c (f l) else 0 := by
    intro l
    split_ifs with hl
    · rfl
    · exact homothety_zero_left _
  simp_rw [h]
  rw [Finset.sum_ite_eq']
  simp

theorem iter_two {d : ℕ} {Φ : MvFormalGroup d Kε} [Φ.IsComm] (x : MvFormalGroup.CartierModule q Φ) :
    (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2] x = verschiebungInt (verschiebungInt x) := rfl

theorem iter_three {d : ℕ} {Φ : MvFormalGroup d Kε} [Φ.IsComm] (x : MvFormalGroup.CartierModule q Φ) :
    (⇑(verschiebungInt (p := q) (Φ := Φ)))^[3] x = verschiebungInt (verschiebungInt (verschiebungInt x)) := rfl

theorem expand₂ {Φ : MvFormalGroup 2 Kε} [Φ.IsComm]
    (Pi : MvFormalGroup.CartierModule q Φ →+ MvFormalGroup.CartierModule q Φ)
    (e γ' : Fin 2 → MvFormalGroup.CartierModule q Φ)
    (a : ℕ → Fin 2 → k) (s v w : Fin 2 → k) (i : Fin 2)
    (halpha : ∃ r, Pi (γ' i) =
      homothety ((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) (e (FormalODModule.piIndex 0 i)) +
      verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i)) (e i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i)) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2]
        (homothety (algebraMap k Kε (a 2 i)) (e (FormalODModule.piIndex 0 i)) +
          homothety ((w i * a 0 i) • DualNumber.eps) (e (FormalODModule.piIndex 0 i))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[3] r)
    (hinv : ∀ j, ∃ r, e j = homothety (1 - s j • DualNumber.eps) (γ' j) +
      verschiebungInt (p := q) (homothety (-(v j • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 j))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2] (homothety (-(w j • DualNumber.eps)) (γ' j)) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[3] r) :
    ∃ r, Pi (γ' i) =
      (∑ m : Fin 2, (⇑(verschiebungInt (p := q) (Φ := Φ)))^[(m : ℕ)]
        (∑ l : Fin 2, homothety (E₂ (q := q) a s v i m l) (γ' l))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2] r := by
  have hii : FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := piIndex_zero_piIndex_zero i

  have hε2 : ∀ a b : k, (a • DualNumber.eps : Kε) * (b • DualNumber.eps) = 0 := eps_smul_mul_eps_smul
  have hpow1 : ∀ c : k, ((1 : Kε) + c • DualNumber.eps) ^ q = 1 := fun c => by
    have := one_add_eps_smul_pow (q := q) c (n := 1) le_rfl
    rwa [pow_one] at this

  obtain ⟨rα, hα⟩ := halpha
  have hA : ModV (p := q) 2 (Pi (γ' i))
      (homothety ((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) (e (FormalODModule.piIndex 0 i)) +
       verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i)) (e i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i))) := by
    refine ⟨(homothety (algebraMap k Kε (a 2 i)) (e (FormalODModule.piIndex 0 i)) + homothety ((w i * a 0 i) • DualNumber.eps) (e (FormalODModule.piIndex 0 i))) +
      verschiebungInt (p := q) rα, ?_⟩
    rw [hα]
    simp only [iter_two, iter_three, map_add]
    abel

  have hBi' : ModV (p := q) 2 (e (FormalODModule.piIndex 0 i))
      (homothety (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps) (γ' (FormalODModule.piIndex 0 i)) +
        verschiebungInt (p := q) (homothety (-(v (FormalODModule.piIndex 0 i) • DualNumber.eps)) (γ' i))) := by
    obtain ⟨r, hr⟩ := hinv (FormalODModule.piIndex 0 i)
    refine ⟨homothety (-(w (FormalODModule.piIndex 0 i) • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 i)) + verschiebungInt (p := q) r, ?_⟩
    rw [hii] at hr
    rw [hr]
    simp only [iter_two, iter_three, map_add]
    abel
  have hBi : ModV (p := q) 1 (e i) (homothety (1 - s i • DualNumber.eps) (γ' i)) := by
    obtain ⟨r, hr⟩ := hinv i
    refine ⟨homothety (-(v i • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 i)) +
      verschiebungInt (p := q) (homothety (-(w i • DualNumber.eps)) (γ' i)) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2] r, ?_⟩
    rw [hr]
    simp only [iter_two, iter_three, Function.iterate_one, map_add]
    abel

  have hC : ModV (p := q) 2 (homothety ((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) (e (FormalODModule.piIndex 0 i)))
      (homothety (((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 i)) +
        verschiebungInt (p := q) (homothety ((((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) ^ q) *
          (-(v (FormalODModule.piIndex 0 i) • DualNumber.eps))) (γ' i))) := by
    have h := hBi'.homothety ((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i))
    refine h.trans (ModV.of_eq ?_)
    rw [map_add, ← homothety_mul, homothety_verschiebungInt, ← homothety_mul]

  have hD : ModV (p := q) 2
      (verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i)) (e i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i)))
      (verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps)) (γ' i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) (γ' i))) := by
    have h := (hBi.homothety (algebraMap k Kε (a 1 i))).add (hBi.homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps))
    rw [← homothety_mul, ← homothety_mul] at h
    exact h.verschiebungInt

  have hE := hA.trans (hC.add hD)
  have hmerge : ModV (p := q) 2
      (verschiebungInt (p := q) (homothety ((((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) ^ q) *
          (-(v (FormalODModule.piIndex 0 i) • DualNumber.eps))) (γ' i)) +
       verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps)) (γ' i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) (γ' i)))
      (verschiebungInt (p := q) (homothety
        ((((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) ^ q) * (-(v (FormalODModule.piIndex 0 i) • DualNumber.eps)) +
         (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps) +
          (v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps))) (γ' i))) := by
    rw [← map_add]
    refine ModV.verschiebungInt ?_
    refine ((ModV.rfl' 1 _).add (ModV.merge _ _ _)).trans (ModV.merge _ _ _)
  have hfinal := hE.trans (by
    rw [add_assoc]
    exact (ModV.rfl' 2 _).add hmerge)

  have hE0 : ∀ l : Fin 2, E₂ (q := q) a s v i 0 l =
      if l = (FormalODModule.piIndex 0 i) then algebraMap k Kε (a 0 i) + ((s i - s (FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps else 0 := by
    intro l
    unfold E₂
    rw [if_pos (show ((0 : Fin 2) : ℕ) = 0 from rfl)]
  have hE1 : ∀ l : Fin 2, E₂ (q := q) a s v i 1 l =
      if l = i then algebraMap k Kε (a 1 i) + (v i * a 0 (FormalODModule.piIndex 0 i) - a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) • DualNumber.eps
        else 0 := by
    intro l
    unfold E₂
    rw [if_neg (show ((1 : Fin 2) : ℕ) ≠ 0 from one_ne_zero)]
  have hc0 : ((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps) =
      algebraMap k Kε (a 0 i) + ((s i - s (FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps := by
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
    · simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
      ring
  have hc1 : (((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) ^ q) * (-(v (FormalODModule.piIndex 0 i) • DualNumber.eps)) +
      (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps) +
        (v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) =
      algebraMap k Kε (a 1 i) + (v i * a 0 (FormalODModule.piIndex 0 i) - a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) • DualNumber.eps := by
    rw [mul_pow, hpow1, one_mul, ← map_pow]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
    · simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
      ring

  obtain ⟨r, hr⟩ := hfinal
  refine ⟨r, ?_⟩
  rw [hr, hc0, hc1, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Function.iterate_zero, Function.iterate_one, id_eq]
  simp_rw [hE0, hE1]
  rw [sum_homothety_ite (FormalODModule.piIndex 0 i) _ γ', sum_homothety_ite i _ γ']

theorem expand₃ {Φ : MvFormalGroup 2 Kε} [Φ.IsComm]
    (Pi : MvFormalGroup.CartierModule q Φ →+ MvFormalGroup.CartierModule q Φ)
    (e γ' : Fin 2 → MvFormalGroup.CartierModule q Φ)
    (a : ℕ → Fin 2 → k) (s v w : Fin 2 → k) (i : Fin 2) (h0 : a 0 i = 0)
    (hFz : ∃ z, frobenius (γ' i) = verschiebungInt (p := q) z)
    (halpha : ∃ r, Pi (γ' i) =
      homothety ((1 + s i • DualNumber.eps) * algebraMap k Kε (a 0 i)) (e (FormalODModule.piIndex 0 i)) +
      verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i)) (e i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i)) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2]
        (homothety (algebraMap k Kε (a 2 i)) (e (FormalODModule.piIndex 0 i)) +
          homothety ((w i * a 0 i) • DualNumber.eps) (e (FormalODModule.piIndex 0 i))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[3] r)
    (hinv : ∀ j, ∃ r, e j = homothety (1 - s j • DualNumber.eps) (γ' j) +
      verschiebungInt (p := q) (homothety (-(v j • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 j))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2] (homothety (-(w j • DualNumber.eps)) (γ' j)) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[3] r) :
    ∃ r, Pi (γ' i) =
      (∑ m : Fin 3, (⇑(verschiebungInt (p := q) (Φ := Φ)))^[(m : ℕ)]
        (∑ l : Fin 2, homothety (E₃ (q := q) a s v i m l) (γ' l))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[3] r := by
  have hii : FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := piIndex_zero_piIndex_zero i
  have hε2 : ∀ a b : k, (a • DualNumber.eps : Kε) * (b • DualNumber.eps) = 0 := eps_smul_mul_eps_smul
  have hpow1 : ∀ c : k, ((1 : Kε) + c • DualNumber.eps) ^ q = 1 := fun c => by
    have := one_add_eps_smul_pow (q := q) c (n := 1) le_rfl
    rwa [pow_one] at this
  have hq0 : q ≠ 0 := hq.out.ne_zero
  obtain ⟨z, hz⟩ := hFz

  obtain ⟨rα, hα⟩ := halpha
  rw [h0, map_zero, mul_zero, mul_zero, zero_smul, homothety_zero_left, zero_add, add_zero] at hα
  have hA : ModV (p := q) 3 (Pi (γ' i))
      (verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i)) (e i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i)) +
       (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2]
        (homothety (algebraMap k Kε (a 2 i)) (e (FormalODModule.piIndex 0 i)))) := ⟨rα, hα⟩

  have hBi : ModV (p := q) 2 (e i)
      (homothety (1 - s i • DualNumber.eps) (γ' i) +
        verschiebungInt (p := q) (homothety (-(v i • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 i)))) := by
    obtain ⟨r, hr⟩ := hinv i
    refine ⟨homothety (-(w i • DualNumber.eps)) (γ' i) + verschiebungInt (p := q) r, ?_⟩
    rw [hr]
    simp only [iter_two, iter_three, map_add]
    abel
  have hBi' : ModV (p := q) 1 (e (FormalODModule.piIndex 0 i))
      (homothety (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps) (γ' (FormalODModule.piIndex 0 i))) := by
    obtain ⟨r, hr⟩ := hinv (FormalODModule.piIndex 0 i)
    rw [hii] at hr
    refine ⟨homothety (-(v (FormalODModule.piIndex 0 i) • DualNumber.eps)) (γ' i) +
      verschiebungInt (p := q) (homothety (-(w (FormalODModule.piIndex 0 i) • DualNumber.eps))
        (γ' (FormalODModule.piIndex 0 i))) +
      (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2] r, ?_⟩
    rw [hr]
    simp only [iter_two, iter_three, Function.iterate_one, map_add]
    abel

  have hC1 : ModV (p := q) 2 (homothety (algebraMap k Kε (a 1 i)) (e i))
      (homothety (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps)) (γ' i) +
        verschiebungInt (p := q) (homothety ((algebraMap k Kε (a 1 i)) ^ q * (-(v i • DualNumber.eps)))
          (γ' (FormalODModule.piIndex 0 i)))) := by
    refine (hBi.homothety (algebraMap k Kε (a 1 i))).trans (ModV.of_eq ?_)
    rw [map_add, ← homothety_mul, homothety_verschiebungInt, ← homothety_mul]
  have hC2 : ModV (p := q) 2 (homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i))
      (homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) (γ' i)) := by
    refine (hBi.homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps)).trans (ModV.of_eq ?_)
    rw [map_add, ← homothety_mul, homothety_verschiebungInt, ← homothety_mul,
      eps_smul_pow _ hq.out.two_le, zero_mul, homothety_zero_left, map_zero, add_zero]
  have hC : ModV (p := q) 2
      (homothety (algebraMap k Kε (a 1 i)) (e i) +
        homothety ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps) (e i))
      (homothety (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps) +
          (v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) (γ' i) +
        verschiebungInt (p := q) (homothety ((algebraMap k Kε (a 1 i)) ^ q * (-(v i • DualNumber.eps)))
          (γ' (FormalODModule.piIndex 0 i)))) := by
    refine (hC1.add hC2).trans ?_
    have hm := ModV.merge₂ (p := q) (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps))
      ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) (γ' i) hz
    obtain ⟨r, hr⟩ := hm
    refine ⟨r, ?_⟩
    rw [add_right_comm, hr]
    abel

  have hD : ModV (p := q) 1 (homothety (algebraMap k Kε (a 2 i)) (e (FormalODModule.piIndex 0 i)))
      (homothety (algebraMap k Kε (a 2 i) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps))
        (γ' (FormalODModule.piIndex 0 i))) := by
    refine (hBi'.homothety (algebraMap k Kε (a 2 i))).trans (ModV.of_eq ?_)
    rw [← homothety_mul]

  have hE : ModV (p := q) 3 (Pi (γ' i))
      (verschiebungInt (p := q) (homothety (algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps) +
          (v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps)) (γ' i)) +
       (⇑(verschiebungInt (p := q) (Φ := Φ)))^[2]
        (homothety ((algebraMap k Kε (a 1 i)) ^ q * (-(v i • DualNumber.eps))) (γ' (FormalODModule.piIndex 0 i)) +
         homothety (algebraMap k Kε (a 2 i) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps))
          (γ' (FormalODModule.piIndex 0 i)))) := by
    have h1 := hC.verschiebungInt
    have h2 := hD.iterate 2
    refine hA.trans ((h1.add h2).trans (ModV.of_eq ?_))
    simp only [iter_two, map_add]
    abel
  have hmerge : ModV (p := q) 3
      ((⇑(verschiebungInt (p := q) (Φ := Φ)))^[2]
        (homothety ((algebraMap k Kε (a 1 i)) ^ q * (-(v i • DualNumber.eps))) (γ' (FormalODModule.piIndex 0 i)) +
         homothety (algebraMap k Kε (a 2 i) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps))
          (γ' (FormalODModule.piIndex 0 i))))
      ((⇑(verschiebungInt (p := q) (Φ := Φ)))^[2]
        (homothety ((algebraMap k Kε (a 1 i)) ^ q * (-(v i • DualNumber.eps)) +
          algebraMap k Kε (a 2 i) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps))
          (γ' (FormalODModule.piIndex 0 i)))) :=
    (ModV.merge _ _ _).iterate 2
  have hfinal := hE.trans ((ModV.rfl' 3 _).add hmerge)

  have hE30 : ∀ l : Fin 2, E₃ (q := q) a s v i 0 l = 0 := by
    intro l; unfold E₃; rw [if_pos (show ((0 : Fin 3) : ℕ) = 0 from rfl)]
  have hE31 : ∀ l : Fin 2, E₃ (q := q) a s v i 1 l =
      if l = i then algebraMap k Kε (a 1 i) + (v i * a 0 (FormalODModule.piIndex 0 i) -
        a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) • DualNumber.eps else 0 := by
    intro l; unfold E₃
    rw [if_neg (show ((1 : Fin 3) : ℕ) ≠ 0 from one_ne_zero), if_pos (show ((1 : Fin 3) : ℕ) = 1 from rfl)]
  have hE32 : ∀ l : Fin 2, E₃ (q := q) a s v i 2 l =
      if l = FormalODModule.piIndex 0 i then algebraMap k Kε (a 2 i) -
        (a 1 i ^ q * v i + a 2 i * s (FormalODModule.piIndex 0 i)) • DualNumber.eps else 0 := by
    intro l; unfold E₃
    rw [if_neg (show ((2 : Fin 3) : ℕ) ≠ 0 by decide), if_neg (show ((2 : Fin 3) : ℕ) ≠ 1 by decide)]
  have hc1 : algebraMap k Kε (a 1 i) * (1 - s i • DualNumber.eps) +
      (v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps * (1 - s i • DualNumber.eps) =
      algebraMap k Kε (a 1 i) + (v i * a 0 (FormalODModule.piIndex 0 i) -
        a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) • DualNumber.eps := by
    rw [h0, zero_pow hq0, zero_mul, sub_zero]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
    · simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
      ring
  have hc2 : (algebraMap k Kε (a 1 i)) ^ q * (-(v i • DualNumber.eps)) +
      algebraMap k Kε (a 2 i) * (1 - s (FormalODModule.piIndex 0 i) • DualNumber.eps) =
      algebraMap k Kε (a 2 i) - (a 1 i ^ q * v i + a 2 i * s (FormalODModule.piIndex 0 i)) • DualNumber.eps := by
    rw [← map_pow]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
    · simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, Algebra.algebraMap_eq_smul_one]
      ring
  obtain ⟨r, hr⟩ := hfinal
  refine ⟨r, ?_⟩
  rw [hr, hc1, hc2, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Function.iterate_zero, Function.iterate_one, id_eq]
  simp_rw [hE30, hE31, hE32]
  rw [sum_homothety_ite i _ γ', sum_homothety_ite (FormalODModule.piIndex 0 i) _ γ']
  simp only [homothety_zero_left, Finset.sum_const_zero, zero_add]

end Combine

end P2mW3
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3"

noncomputable section

namespace P2mW3
namespace U
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

section DualNumberFacts

variable {k : Type u} [Field k] {q : ℕ} [hq : Fact q.Prime] [CharP k q]

set_option synthInstance.checkSynthOrder false in
scoped instance charP_dualNumber : CharP (DualNumber k) q :=
  charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

theorem eps_pow_prime : (DualNumber.eps : DualNumber k) ^ q = 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hq.out.two_le
  rw [hm, pow_add, pow_two, DualNumber.eps_mul_eps, zero_mul]

theorem smul_eps_pow_prime (c : k) : (c • (DualNumber.eps : DualNumber k)) ^ q = 0 := by
  rw [smul_pow, eps_pow_prime, smul_zero]

theorem one_add_smul_eps_pow_prime (c : k) : (1 + c • (DualNumber.eps : DualNumber k)) ^ q = 1 := by
  rw [add_pow_char, one_pow, smul_eps_pow_prime, add_zero]

theorem smul_eps_mul_algebraMap (c a : k) :
    (c • (DualNumber.eps : DualNumber k)) * algebraMap k (DualNumber k) a = (c * a) • DualNumber.eps := by
  rw [mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

end DualNumberFacts
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3"

section Alpha

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

local notation "Kε" => DualNumber k
local notation "ιε" => algebraMap k (DualNumber k)

theorem alpha
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (s v w : Fin 2 → k) (g : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 + s i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i)) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] (g i))
    (i : Fin 2) :
    ∃ r : MvFormalGroup.CartierModule q (X₀.map ιε).F,
      endAct (X₀.map ιε).varpiEnd (γ' i) =
        homothety (Φ := (X₀.map ιε).F) ((1 + s i • DualNumber.eps) * ιε (a 0 i))
          (baseChange ιε (γ (FormalODModule.piIndex 0 i)) : CartierModule q (X₀.map ιε).F) +
        verschiebungInt (p := q)
          (homothety (Φ := (X₀.map ιε).F) (ιε (a 1 i)) (baseChange ιε (γ i) : CartierModule q (X₀.map ιε).F) +
            homothety (Φ := (X₀.map ιε).F) ((v i * a 0 (FormalODModule.piIndex 0 i)) • DualNumber.eps)
              (baseChange ιε (γ i) : CartierModule q (X₀.map ιε).F)) +
        (⇑(verschiebungInt (p := q) (Φ := (X₀.map ιε).F)))^[2]
          (homothety (Φ := (X₀.map ιε).F) (ιε (a 2 i)) (baseChange ιε (γ (FormalODModule.piIndex 0 i)) : CartierModule q (X₀.map ιε).F) +
            homothety (Φ := (X₀.map ιε).F) ((w i * a 0 i) • DualNumber.eps)
              (baseChange ιε (γ (FormalODModule.piIndex 0 i)) : CartierModule q (X₀.map ιε).F)) +
        (⇑(verschiebungInt (p := q) (Φ := (X₀.map ιε).F)))^[3] r := by
  haveI : (X₀.map ιε).F.IsComm := (X₀.map ιε).isComm
  have hae := ha.map ιε
  have hπ1 : ∀ j : Fin 2, FormalODModule.piIndex 1 j = j := by intro j; fin_cases j <;> rfl
  have hπ2 : ∀ j : Fin 2, FormalODModule.piIndex 2 j = FormalODModule.piIndex 0 j := by intro j; fin_cases j <;> rfl
  have hπ00 : FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := by fin_cases i <;> rfl

  obtain ⟨h3, H3⟩ := hae i 3
  obtain ⟨h1, H1⟩ := hae (FormalODModule.piIndex 0 i) 1
  simp only [Fin.sum_univ_three, Fin.sum_univ_one, Fin.val_zero, Fin.val_one, Fin.val_two,
    Function.iterate_zero, Function.iterate_one, Function.iterate_succ, Function.comp_apply, id_eq,
    hπ1, hπ2, hπ00] at H3 H1
  refine ⟨h3 + endAct (X₀.map ιε).varpiEnd (g i), ?_⟩
  rw [hshape i]

  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, map_add,
    endAct_homothety, endAct_verschiebungInt]

  rw [H3, H1]
  have hq0 : q ≠ 0 := hq.out.ne_zero
  simp only [map_add, homothety_verschiebungInt, ← homothety_mul, one_add_smul_eps_pow_prime, smul_eps_pow_prime,
    one_pow, one_mul, zero_mul, zero_pow hq0, homothety_one, homothety_zero_left, map_zero, add_zero, zero_add,
    smul_eps_mul_algebraMap]
  abel

end Alpha
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3"

end P2mW3.U
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3"
end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U"

namespace P2mW3
namespace G1
open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

section B1

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

theorem smul_eps_mul_smul_eps (a b : k) :
    (a • (DualNumber.eps : DualNumber k)) * (b • (DualNumber.eps : DualNumber k)) = 0 := by
  rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]

theorem smul_eps_mul_one_add (c s : k) :
    (c • (DualNumber.eps : DualNumber k)) * (1 + s • (DualNumber.eps : DualNumber k)) = c • DualNumber.eps := by
  rw [mul_add, mul_one, smul_eps_mul_smul_eps, add_zero]

theorem one_sub_mul_one_add (s : k) :
    (1 - s • (DualNumber.eps : DualNumber k)) * (1 + s • (DualNumber.eps : DualNumber k)) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, smul_eps_mul_smul_eps]
  abel

set_option synthInstance.checkSynthOrder false in
scoped instance charP_dualNumber : CharP (DualNumber k) q :=
  charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

theorem smul_eps_pow_char (v : k) : (v • (DualNumber.eps : DualNumber k)) ^ q = 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hq.out.two_le
  rw [hm, pow_add, pow_two, smul_eps_mul_smul_eps, zero_mul]

theorem one_add_smul_eps_pow_char (s : k) : (1 + s • (DualNumber.eps : DualNumber k)) ^ q = 1 := by
  rw [add_pow_char, one_pow, smul_eps_pow_char, add_zero]

theorem one_sub_smul_eps_pow_char (s : k) : (1 - s • (DualNumber.eps : DualNumber k)) ^ q = 1 := by
  rw [sub_eq_add_neg, ← neg_smul, one_add_smul_eps_pow_char]

variable {d : ℕ} (Ψ : MvFormalGroup d (DualNumber k)) [Ψ.IsComm]

theorem homothety_V_of_pow (c : DualNumber k) (hc : c ^ q = 1) (x : CartierModule q Ψ) :
    homothety c (verschiebungInt x) = verschiebungInt x := by
  rw [homothety_verschiebungInt, hc, homothety_one]

theorem homothety_V2_of_pow (c : DualNumber k) (hc : c ^ q = 1) (x : CartierModule q Ψ) :
    homothety c ((⇑(verschiebungInt (p := q) (Φ := Ψ)))^[2] x) = (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[2] x := by
  show homothety c (verschiebungInt (verschiebungInt x)) = verschiebungInt (verschiebungInt x)
  rw [homothety_V_of_pow Ψ c hc]

theorem homothety_V3_of_pow (c : DualNumber k) (hc : c ^ q = 1) (x : CartierModule q Ψ) :
    homothety c ((⇑(verschiebungInt (p := q) (Φ := Ψ)))^[3] x) = (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[3] x := by
  show homothety c (verschiebungInt (verschiebungInt (verschiebungInt x))) =
    verschiebungInt (verschiebungInt (verschiebungInt x))
  rw [homothety_V_of_pow Ψ c hc]

theorem homothety_V_of_pow_zero (c : DualNumber k) (hc : c ^ q = 0) (x : CartierModule q Ψ) :
    homothety c (verschiebungInt x) = 0 := by
  rw [homothety_verschiebungInt, hc, homothety_zero_left, map_zero]

theorem homothety_V2_of_pow_zero (c : DualNumber k) (hc : c ^ q = 0) (x : CartierModule q Ψ) :
    homothety c ((⇑(verschiebungInt (p := q) (Φ := Ψ)))^[2] x) = 0 := by
  show homothety c (verschiebungInt (verschiebungInt x)) = 0
  rw [homothety_V_of_pow_zero Ψ c hc]

theorem homothety_V3_of_pow_zero (c : DualNumber k) (hc : c ^ q = 0) (x : CartierModule q Ψ) :
    homothety c ((⇑(verschiebungInt (p := q) (Φ := Ψ)))^[3] x) = 0 := by
  show homothety c (verschiebungInt (verschiebungInt (verschiebungInt x))) = 0
  rw [homothety_V_of_pow_zero Ψ c hc]

theorem iterate3_neg (x : CartierModule q Ψ) :
    (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[3] (-x) = -((⇑(verschiebungInt (p := q) (Φ := Ψ)))^[3] x) := by
  show verschiebungInt (verschiebungInt (verschiebungInt (-x))) = -verschiebungInt (verschiebungInt (verschiebungInt x))
  rw [map_neg, map_neg, map_neg]

theorem iterate2_neg (x : CartierModule q Ψ) :
    (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[2] (-x) = -((⇑(verschiebungInt (p := q) (Φ := Ψ)))^[2] x) := by
  show verschiebungInt (verschiebungInt (-x)) = -verschiebungInt (verschiebungInt x)
  rw [map_neg, map_neg]

end B1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U"

section Invert

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

theorem invert (X₀ : FormalODModule q k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (s v w : Fin 2 → k) (g : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 + s i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i)) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] (g i))
    (hK6 : ∀ (c : k) (f : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F),
      MvFormalGroup.CartierModule.homothety (c • DualNumber.eps) f +
        MvFormalGroup.CartierModule.homothety (-(c • DualNumber.eps)) f = 0)
    (i : Fin 2) :
    ∃ r : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F,
      (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
          MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) =
        MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 - s i • DualNumber.eps) (γ' i) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (-(v i • DualNumber.eps))
            (γ' (FormalODModule.piIndex 0 i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (-(w i • DualNumber.eps)) (γ' i)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] r := by

  have hεe : ∀ (c : k) (j : Fin 2),
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (c • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ j)) =
        MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (c • DualNumber.eps) (γ' j) := by
    intro c j
    have h1 := congrArg (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (c • DualNumber.eps)) (hshape j)
    rw [map_add, map_add, map_add, ← homothety_mul, smul_eps_mul_one_add,
      homothety_V_of_pow_zero _ _ (smul_eps_pow_char c), homothety_V2_of_pow_zero _ _ (smul_eps_pow_char c),
      homothety_V3_of_pow_zero _ _ (smul_eps_pow_char c), add_zero, add_zero, add_zero] at h1
    exact h1.symm

  have h2 := congrArg (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 - s i • DualNumber.eps)) (hshape i)
  rw [map_add, map_add, map_add, ← homothety_mul, one_sub_mul_one_add, homothety_one,
    homothety_V_of_pow _ _ (one_sub_smul_eps_pow_char (s i)), homothety_V2_of_pow _ _ (one_sub_smul_eps_pow_char (s i)),
    homothety_V3_of_pow _ _ (one_sub_smul_eps_pow_char (s i))] at h2

  have hv : MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (-(v i • DualNumber.eps)) (γ' (FormalODModule.piIndex 0 i))
      = -MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i))) := by
    rw [hεe, eq_neg_iff_add_eq_zero, add_comm]; exact hK6 _ _
  have hw : MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (-(w i • DualNumber.eps)) (γ' i)
      = -MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i)) := by
    rw [hεe, eq_neg_iff_add_eq_zero, add_comm]; exact hK6 _ _
  refine ⟨-(g i), ?_⟩
  rw [hv, hw, map_neg, iterate2_neg, iterate3_neg, h2]
  abel

end Invert
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U"

end P2mW3.G1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U"

noncomputable section

namespace P2mW3
namespace S
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

set_option synthInstance.checkSynthOrder false in
scoped instance charP_dualNumber_fstep {k : Type u} [Field k] {q : ℕ} [CharP k q] : CharP (DualNumber k) q :=
  charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

section

variable {q : ℕ} [Fact q.Prime] {R : Type u} [CommRing R] [CharP R q] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

theorem frobenius_verschiebungInt_mem_range (x : CartierModule q Φ) :
    ∃ z, frobenius (verschiebungInt x) = verschiebungInt (p := q) (Φ := Φ) z := by
  refine ⟨frobenius x, ?_⟩
  rw [frobenius_verschiebungInt, verschiebungInt_apply_eq_verschiebung, verschiebung_frobenius]

theorem frobenius_verschiebungInt_iterate_mem_range (n : ℕ) (hn : 1 ≤ n) (x : CartierModule q Φ) :
    ∃ z, frobenius ((⇑(verschiebungInt (p := q) (Φ := Φ)))^[n] x) = verschiebungInt (p := q) (Φ := Φ) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact frobenius_verschiebungInt_mem_range _

theorem add_mem_range {a b : CartierModule q Φ}
    (ha : ∃ z, a = verschiebungInt (p := q) (Φ := Φ) z) (hb : ∃ z, b = verschiebungInt (p := q) (Φ := Φ) z) :
    ∃ z, a + b = verschiebungInt (p := q) (Φ := Φ) z := by
  obtain ⟨za, rfl⟩ := ha; obtain ⟨zb, rfl⟩ := hb
  exact ⟨za + zb, (map_add _ _ _).symm⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1"

theorem frob_gamma'_mem_range_V
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (s v w : Fin 2 → k) (g : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 + s i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i)) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] (g i))
    (i₀ : Fin 2)
    (hFV : ∃ y : MvFormalGroup.CartierModule q X₀.F,
      MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) :
    ∃ z, MvFormalGroup.CartierModule.frobenius (γ' i₀) =
      MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F) z := by
  obtain ⟨y, hy⟩ := hFV
  rw [hshape i₀, map_add, map_add, map_add]
  refine add_mem_range (add_mem_range (add_mem_range ?_ ?_) ?_) ?_
  ·
    refine ⟨homothety ((((1 : DualNumber k) + s i₀ • DualNumber.eps) ^ q) ^ q)
      (baseChange (algebraMap k (DualNumber k)) y), ?_⟩
    rw [frobenius_homothety]
    show homothety _ (frobenius (baseChangeEq (algebraMap k (DualNumber k)) rfl (γ i₀))) = _
    rw [← baseChangeEq_frobenius, hy, baseChangeEq_verschiebungInt, homothety_verschiebungInt]
    rfl
  · exact frobenius_verschiebungInt_mem_range _
  · exact frobenius_verschiebungInt_iterate_mem_range 2 (by norm_num) _
  · exact frobenius_verschiebungInt_iterate_mem_range 3 (by norm_num) _

end P2mW3.S
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.S"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1"

namespace P2mW3
namespace G2
open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

section Shell

variable {q : ℕ} [hq : Fact q.Prime] {B : Type u} [CommRing B] [CharP B q] {d : ℕ} (Ψ : MvFormalGroup d B) [Ψ.IsComm]

theorem sum_single_eq_sum_sum (f : Fin 2 → CartierModule q Ψ) (N : ℕ) (c : Fin N → B) (j : Fin N → Fin 2) :
    (∑ m : Fin N, (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[(m : ℕ)] (homothety (c m) (f (j m))))
      = ∑ m : Fin N, (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[(m : ℕ)]
          (∑ l : Fin 2, homothety (if l = j m then c m else 0) (f l)) := by
  classical
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [Finset.sum_eq_single_of_mem (j m) (Finset.mem_univ _)]
  · rw [if_pos rfl]
  · intro l _ hl
    rw [if_neg hl, homothety_zero_left]

theorem digits_unique (f : Fin d → CartierModule q Ψ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : CartierModule q Ψ) (N : ℕ) (c c' : Fin N → Fin d → B) (r r' : CartierModule q Ψ)
    (h : g = (∑ m : Fin N, (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[(m : ℕ)] (∑ i : Fin d, homothety (c m i) (f i))) +
      (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[N] r)
    (h' : g = (∑ m : Fin N, (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[(m : ℕ)] (∑ i : Fin d, homothety (c' m i) (f i))) +
      (⇑(verschiebungInt (p := q) (Φ := Ψ)))^[N] r') :
    c = c' := by
  have hu := MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP q Ψ f hf g N
  have := hu.unique (y₁ := (c, r)) (y₂ := (c', r')) h h'
  exact congrArg Prod.fst this

end Shell
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.S"

section ShellW3

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q]

set_option synthInstance.checkSynthOrder false in
scoped instance charP_dualNumber' : CharP (DualNumber k) q :=
  charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

theorem shell (X₀ : FormalODModule q k) (j₀ : Zp2 q →+* k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F)
    (a : ℕ → Fin 2 → k)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (s v : Fin 2 → k)
    (a' : ℕ → Fin 2 → DualNumber k) (ha' : (X₀.map (algebraMap k (DualNumber k))).HasStructureConstants γ' a')
    (hexp₂ : ∀ i : Fin 2, ∃ r : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F,
      MvFormalGroup.CartierModule.endAct (X₀.map (algebraMap k (DualNumber k))).varpiEnd (γ' i) =
        (∑ m : Fin 2, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (E₂ (q := q) a s v i m l) (γ' l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2] r)
    (hexp₃ : ∀ i₀ : Fin 2, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      ∃ r : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F,
      MvFormalGroup.CartierModule.endAct (X₀.map (algebraMap k (DualNumber k))).varpiEnd (γ' i₀) =
        (∑ m : Fin 3, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (E₃ (q := q) a s v i₀ m l) (γ' l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] r) :
    (∀ i, a' 0 i = algebraMap k (DualNumber k) (a 0 i) +
        ((s i - s (FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps) ∧
    (∀ i, a' 1 i = algebraMap k (DualNumber k) (a 1 i) +
        (v i * a 0 (FormalODModule.piIndex 0 i) - a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) •
          DualNumber.eps) ∧
    (∀ i₀, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      a' 2 i₀ = algebraMap k (DualNumber k) (a 2 i₀) -
        (a 1 i₀ ^ q * v i₀ + a 2 i₀ * s (FormalODModule.piIndex 0 i₀)) • DualNumber.eps) := by
  classical

  have hdig₂ : ∀ i, (fun (m : Fin 2) (l : Fin 2) => if l = FormalODModule.piIndex (m : ℕ) i then a' m i else 0) = E₂ (q := q) a s v i := by
    intro i
    obtain ⟨h, hh⟩ := ha' i 2
    obtain ⟨r, hr⟩ := hexp₂ i
    rw [sum_single_eq_sum_sum (X₀.map (algebraMap k (DualNumber k))).F γ' 2 (fun m => a' m i) (fun m => FormalODModule.piIndex (m : ℕ) i)] at hh
    exact digits_unique (X₀.map (algebraMap k (DualNumber k))).F γ' hγ'.2 _ 2 _ _ h r hh hr
  have hdig₃ : ∀ i₀, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      (fun (m : Fin 3) (l : Fin 2) => if l = FormalODModule.piIndex (m : ℕ) i₀ then a' m i₀ else 0) = E₃ (q := q) a s v i₀ := by
    intro i₀ h0 hF
    obtain ⟨h, hh⟩ := ha' i₀ 3
    obtain ⟨r, hr⟩ := hexp₃ i₀ h0 hF
    rw [sum_single_eq_sum_sum (X₀.map (algebraMap k (DualNumber k))).F γ' 3 (fun m => a' m i₀) (fun m => FormalODModule.piIndex (m : ℕ) i₀)] at hh
    exact digits_unique (X₀.map (algebraMap k (DualNumber k))).F γ' hγ'.2 _ 3 _ _ h r hh hr
  have hpi1 : ∀ i : Fin 2, FormalODModule.piIndex 1 i = i := by
    intro i; apply Fin.ext; fin_cases i <;> rfl
  have hpi2 : ∀ i : Fin 2, FormalODModule.piIndex 2 i = FormalODModule.piIndex 0 i := by
    intro i; apply Fin.ext; fin_cases i <;> rfl
  refine ⟨fun i => ?_, fun i => ?_, fun i₀ h0 hF => ?_⟩
  · have := congr_fun (congr_fun (hdig₂ i) 0) (FormalODModule.piIndex 0 i)
    simpa [E₂] using this
  · have := congr_fun (congr_fun (hdig₂ i) 1) i
    simpa [E₂, hpi1] using this
  · have := congr_fun (congr_fun (hdig₃ i₀ h0 hF) 2) (FormalODModule.piIndex 0 i₀)
    have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    simpa [E₃, hpi2, h2] using this

end ShellW3
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.S"

end P2mW3.G2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.S P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G2"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.U P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.G1 P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety.P2mW3.S"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (j₀ : Zp2 q →+* k) (X₀ : FormalODModule q k)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hγ' : (X₀.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γ')
    (s v w : Fin 2 → k) (g : Fin 2 → MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)
    (hshape : ∀ i, γ' i =
      MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (1 + s i • DualNumber.eps)
          (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (v i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ (FormalODModule.piIndex 0 i)) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2]
          (MvFormalGroup.CartierModule.homothety (Φ := (X₀.map (algebraMap k (DualNumber k))).F) (w i • DualNumber.eps)
            (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ i) :
              MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] (g i))
    (a' : ℕ → Fin 2 → DualNumber k) (ha' : (X₀.map (algebraMap k (DualNumber k))).HasStructureConstants γ' a') :
    (∀ i, a' 0 i = algebraMap k (DualNumber k) (a 0 i) +
        ((s i - s (FormalODModule.piIndex 0 i)) * a 0 i) • DualNumber.eps) ∧
    (∀ i, a' 1 i = algebraMap k (DualNumber k) (a 1 i) +
        (v i * a 0 (FormalODModule.piIndex 0 i) - a 0 i ^ q * v (FormalODModule.piIndex 0 i) - a 1 i * s i) •
          DualNumber.eps) ∧
    (∀ i₀, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      a' 2 i₀ = algebraMap k (DualNumber k) (a 2 i₀) -
        (a 1 i₀ ^ q * v i₀ + a 2 i₀ * s (FormalODModule.piIndex 0 i₀)) • DualNumber.eps) := by
  have hK6 : ∀ (c : k) (f : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F),
      MvFormalGroup.CartierModule.homothety (c • DualNumber.eps) f +
        MvFormalGroup.CartierModule.homothety (-(c • DualNumber.eps)) f = 0 := by
    intro c f
    rw [P2mW3.homothety_neg_eps (c • DualNumber.eps) (P2mW3.eps_smul_mul_eps_smul c c) f, add_neg_cancel]
  have hinv := fun j => P2mW3.G1.invert X₀ γ γ' s v w g hshape hK6 j
  have hexp₂ : ∀ i : Fin 2, ∃ r : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F,
      MvFormalGroup.CartierModule.endAct (X₀.map (algebraMap k (DualNumber k))).varpiEnd (γ' i) =
        (∑ m : Fin 2, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (P2mW3.E₂ (q := q) a s v i m l) (γ' l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[2] r :=
    fun i => P2mW3.expand₂ (MvFormalGroup.CartierModule.endAct (X₀.map (algebraMap k (DualNumber k))).varpiEnd) (fun j => (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ j) : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) γ' a s v w i (P2mW3.U.alpha j₀ X₀ γ hγ a ha γ' hγ' s v w g hshape i) hinv
  have hexp₃ : ∀ i₀ : Fin 2, a 0 i₀ = 0 →
      (∃ y : MvFormalGroup.CartierModule q X₀.F,
        MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y) →
      ∃ r : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F,
      MvFormalGroup.CartierModule.endAct (X₀.map (algebraMap k (DualNumber k))).varpiEnd (γ' i₀) =
        (∑ m : Fin 3, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[(m : ℕ)]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (P2mW3.E₃ (q := q) a s v i₀ m l) (γ' l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := (X₀.map (algebraMap k (DualNumber k))).F)))^[3] r :=
    fun i₀ h0 hF => P2mW3.expand₃ (MvFormalGroup.CartierModule.endAct (X₀.map (algebraMap k (DualNumber k))).varpiEnd) (fun j => (MvFormalGroup.CartierModule.baseChange (algebraMap k (DualNumber k)) (γ j) : MvFormalGroup.CartierModule q (X₀.map (algebraMap k (DualNumber k))).F)) γ' a s v w i₀ h0
      (P2mW3.S.frob_gamma'_mem_range_V j₀ X₀ γ hγ a ha γ' hγ' s v w g hshape i₀ hF)
      (P2mW3.U.alpha j₀ X₀ γ hγ a ha γ' hγ' s v w g hshape i₀) hinv
  exact P2mW3.G2.shell X₀ j₀ γ a γ' hγ' s v a' ha' hexp₂ hexp₃

end
end
end S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hasStructureConstants_dualNumber_apply_eq_of_eq_sum_verschiebungInt_iterate_homothety (solution)
