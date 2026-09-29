-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6d328107-7849-593b-8fbc-8e57d3a01328

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis

set_option autoImplicit false

universe u

namespace SpecialOfVBasisAux

open WittVector

section Zp2Facts

variable (p : ℕ) [hp : Fact p.Prime]

local notation "k2" => GaloisField p 2
local notation "Z2" => WittVector p (GaloisField p 2)

theorem p_mem_nonZeroDivisors : ((p : Z2)) ∈ nonZeroDivisors Z2 :=
  mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero p k2)

theorem frobenius_sub_pow_mem (a : Z2) : WittVector.frobenius a - a ^ p ∈ Ideal.span {(p : Z2)} := by

  set z : Z2 := WittVector.frobenius a - a ^ p with hz
  have hz0 : z.coeff 0 = 0 := by
    have h : WittVector.constantCoeff z = WittVector.constantCoeff (WittVector.frobenius a) - WittVector.constantCoeff (a ^ p) := by
      rw [hz, map_sub]
    rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, map_pow, WittVector.constantCoeff_apply,
      WittVector.coeff_frobenius_charP, sub_self] at h
    exact h
  have hzV : WittVector.verschiebung (z.shift 1) = z := by
    rw [WittVector.verschiebung_shift z 0 (fun i hi => by interval_cases i; exact hz0)]
    ext n; rw [WittVector.shift_coeff, zero_add]
  obtain ⟨y, hy⟩ := (WittVector.frobenius_bijective p k2).2 (z.shift 1)
  rw [Ideal.mem_span_singleton']
  refine ⟨y, ?_⟩
  rw [← hzV, ← hy, WittVector.verschiebung_frobenius]

theorem eq_of_forall_ghostComponent_eq (x y : WittVector p Z2)
    (h : ∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) : x = y := by
  let K := FractionRing Z2
  let ι : Z2 →+* K := algebraMap Z2 K
  have hι : Function.Injective ι := IsFractionRing.injective Z2 K
  haveI : Invertible (p : K) := invertibleOfNonzero (by
    intro h0
    apply WittVector.p_nonzero p k2
    apply hι
    rw [map_natCast, map_zero]; exact h0)
  apply WittVector.map_injective ι hι
  apply (WittVector.ghostEquiv p K).injective
  funext n
  show WittVector.ghostMap (WittVector.map ι x) n = WittVector.ghostMap (WittVector.map ι y) n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply]
  have nat : ∀ w : WittVector p Z2, WittVector.ghostComponent n (WittVector.map ι w) = ι (WittVector.ghostComponent n w) := by
    intro w
    rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial, aeval_wittPolynomial,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, map_natCast, WittVector.map_coeff]
  rw [nat, nat, h n]

theorem theta_teichmuller (θ : Z2 →+* WittVector p Z2)
    (hθ : ∀ (a : Z2) (n : ℕ), WittVector.ghostComponent n (θ a) = (⇑(WittVector.frobenius (p := p) (R := k2)))^[n] a)
    (c : k2) : θ (WittVector.teichmuller p c) = WittVector.teichmuller p (WittVector.teichmuller p c) := by
  apply eq_of_forall_ghostComponent_eq
  intro n
  rw [hθ, WittVector.ghostComponent_teichmuller]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, ← (WittVector.teichmuller p).map_pow, ← (WittVector.teichmuller p).map_pow, ← pow_mul, pow_succ, mul_comm]

private theorem _root_.SpecialOfVBasisAux.exists_generator : ∃ ζ : k2, ζ ≠ 0 ∧ ζ ^ p ≠ ζ ∧ ∀ c : k2, c ≠ 0 → ∃ m : ℕ, c = ζ ^ m := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (k2)ˣ)
  refine ⟨g, g.ne_zero, ?_, ?_⟩
  · intro h

    have hord : orderOf g = Nat.card (k2)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    letI : Fintype k2 := Fintype.ofFinite _
    have hcard : Nat.card (k2)ˣ = p ^ 2 - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, GaloisField.card p 2 two_ne_zero]
    have hgp : (g : k2) ^ (p - 1) = 1 := by
      have h' : (g : k2) ^ (p - 1) * g = g := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, h]
      exact mul_left_eq_self₀.1 h' |>.resolve_right g.ne_zero
    have hdvd : orderOf g ∣ p - 1 := by
      apply orderOf_dvd_of_pow_eq_one
      ext; rw [Units.val_pow_eq_pow_val, hgp, Units.val_one]
    have hle : orderOf g ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.out.one_lt) hdvd
    rw [hord, hcard] at hle
    have h2 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    exact absurd hle (not_le.2 (Nat.sub_lt_sub_right hp.out.one_le h2))
  · intro c hc
    have hmem : Units.mk0 c hc ∈ Submonoid.powers g :=
      (IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite g)).2 (hg _)
    obtain ⟨m, hm⟩ := hmem
    have hm' : g ^ m = Units.mk0 c hc := hm
    exact ⟨m, by rw [← Units.val_pow_eq_pow_val, hm', Units.val_mk0]⟩

p2m_export "SpecialOfVBasisAux" "exists_generator"
end Zp2Facts

section Expansion

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_teichmuller_add_mul (a : WittVector p (GaloisField p 2)) :
    ∃ (c : GaloisField p 2) (y : WittVector p (GaloisField p 2)), a = teichmuller p c + (p : WittVector p (GaloisField p 2)) * y := by

  set z := a - teichmuller p (a.coeff 0) with hz
  have hz0 : z.coeff 0 = 0 := by
    have h : constantCoeff z = constantCoeff a - constantCoeff (teichmuller p (a.coeff 0)) := by rw [hz, map_sub]
    rw [constantCoeff_apply, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, sub_self] at h
    exact h
  have hzV : verschiebung (z.shift 1) = z := by
    rw [verschiebung_shift z 0 (fun i hi => by interval_cases i; exact hz0)]
    ext n; rw [shift_coeff, zero_add]
  obtain ⟨y, hy⟩ := (frobenius_bijective p (GaloisField p 2)).2 (z.shift 1)
  refine ⟨a.coeff 0, y, ?_⟩
  rw [mul_comm, ← verschiebung_frobenius, hy, hzV, hz, add_sub_cancel]

end Expansion

end SpecialOfVBasisAux

open WittVector MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld SpecialOfVBasisAux in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    X.IsSpecial j := by
  classical
  obtain ⟨hmem, hdet⟩ := hγ

  let t : Fin 2 → (Fin 2 → B) := fun i => tangent (γ i)
  let Λ : Zp2 p →+* Matrix (Fin 2) (Fin 2) B := (MvFormalGroup.linearPartHom X.F).comp X.actRingHom
  have hΛ : ∀ (a : Zp2 p) (v : Fin 2 → B), X.lieAct a v = (Λ a).mulVec v := by
    intro a v
    show (linearPart (X.act a)).mulVecLin v = _
    rw [Matrix.mulVecLin_apply]
    show _ = (linearPart (X.actEnd a).toPowerSeries).mulVec v
    rw [FormalODModule.actEnd_toPowerSeries]

  have hnat : ∀ (a : Zp2 p) (f : CartierModule p X.F), (Λ a).mulVec (tangent f) = tangent (endAct (X.actEnd a) f) := by
    intro a f
    rw [endAct_apply, tangent_map]
    rfl

  have hE : ∀ (i : Fin 2) (c : GaloisField p 2),
      (Λ (teichmuller p c)).mulVec (t i) = (j (teichmuller p c) ^ p ^ (i : ℕ)) • t i := by
    intro i c
    show (Λ (teichmuller p c)).mulVec (tangent (γ i)) = _
    rw [hnat, (FormalODModule.mem_gradedPiece_iff X j i (γ i)).1 (hmem i) c, tangent_homothety]

  have hbasis : LinearIndependent B t ∧ Submodule.span B (Set.range t) = ⊤ := by
    rw [Module.Basis.is_basis_iff_det (Pi.basisFun B (Fin 2)), Pi.basisFun_det_apply]
    exact hdet
  have hpair : ∀ s₀ s₁ : B, s₀ • t 0 + s₁ • t 1 = 0 → s₀ = 0 ∧ s₁ = 0 := by
    have : LinearIndependent B ![t 0, t 1] := by
      convert hbasis.1 using 1
      funext i; fin_cases i <;> rfl
    exact LinearIndependent.pair_iff.1 this

  obtain ⟨ζ, hζ0, hζp, hgen⟩ := exists_generator p
  have hunit : IsUnit (j (teichmuller p ζ) - j (teichmuller p ζ) ^ p) := by
    have h1 : IsUnit (teichmuller p ζ - teichmuller p (ζ ^ p)) := by
      apply isUnit_of_coeff_zero_ne_zero
      rw [← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply,
        teichmuller_coeff_zero, teichmuller_coeff_zero, sub_ne_zero]
      exact fun h => hζp h.symm
    have := h1.map j
    rwa [map_sub, (teichmuller p).map_pow, map_pow] at this

  have hfrob_t : ∀ c : GaloisField p 2, WittVector.frobenius (teichmuller p c) = teichmuller p c ^ p := by
    intro c; rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, (teichmuller p).map_pow]

  have key : ∀ (e : Zp2 p →+* B) (v : Fin 2 → B),
      (∀ c : GaloisField p 2, (Λ (teichmuller p c)).mulVec v = e (teichmuller p c) • v) →
      ∀ a : Zp2 p, (Λ a).mulVec v = e a • v := by
    intro e v hv
    let D : Zp2 p → (Fin 2 → B) := fun a => (Λ a).mulVec v - e a • v
    have hDadd : ∀ a b, D (a + b) = D a + D b := by
      intro a b; simp only [D, map_add, Matrix.add_mulVec, add_smul]; abel
    have hDmul : ∀ a b, D (a * b) = (Λ a).mulVec (D b) + e b • D a := by
      intro a b
      simp only [D, map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul, mul_comm (e b) (e a)]
      abel
    have hD0 : ∀ c : GaloisField p 2, D (teichmuller p c) = 0 := fun c => by
      simp only [D, hv c, sub_self]
    have hnatmul : ∀ w : Fin 2 → B, (Λ (p : Zp2 p)).mulVec w = (p : B) • w := by
      intro w
      rw [map_natCast, ← Nat.smul_one_eq_cast, Matrix.smul_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]
    have hDnat : D (p : Zp2 p) = 0 := by
      show (Λ (p : Zp2 p)).mulVec v - e (p : Zp2 p) • v = 0
      rw [hnatmul, map_natCast, sub_self]
    have hDp : ∀ y, D (y * (p : Zp2 p)) = (p : B) • D y := by
      intro y
      rw [hDmul, hDnat, Matrix.mulVec_zero, zero_add, map_natCast]

    have hdiv : ∀ (N : ℕ) (a : Zp2 p), ∃ w : Fin 2 → B, D a = (p : B) ^ N • w := by
      intro N
      induction N with
      | zero => intro a; exact ⟨D a, by rw [pow_zero, one_smul]⟩
      | succ N ih =>
        intro a
        obtain ⟨c, y, rfl⟩ := exists_teichmuller_add_mul p a
        obtain ⟨w, hw⟩ := ih y
        refine ⟨w, ?_⟩
        rw [hDadd, hD0, zero_add, mul_comm, hDp, hw, smul_smul, ← pow_succ']

    intro a
    have hDa : D a = 0 := by
      funext k
      apply hsep.haus
      intro N
      obtain ⟨w, hw⟩ := hdiv N a
      rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, hw]
      exact Ideal.mem_span_singleton.2 ⟨w k, by simp [Pi.smul_apply, smul_eq_mul]⟩
    exact sub_eq_zero.1 hDa

  have h0 : ∀ a : Zp2 p, (Λ a).mulVec (t 0) = j a • t 0 :=
    key j (t 0) (fun c => by rw [hE 0 c]; simp)
  have h1 : ∀ a : Zp2 p, (Λ a).mulVec (t 1) = j (WittVector.frobenius a) • t 1 := by
    have := key (j.comp (WittVector.frobenius (p := p) (R := GaloisField p 2))) (t 1) (fun c => by
      rw [hE 1 c, RingHom.comp_apply, hfrob_t, map_pow]; simp)
    intro a; rw [this a, RingHom.comp_apply]

  have hdecomp : ∀ v : Fin 2 → B, ∃ s : Fin 2 → B, v = s 0 • t 0 + s 1 • t 1 := by
    intro v
    have hv : v ∈ Submodule.span B (Set.range t) := by rw [hbasis.2]; trivial
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hv
    exact ⟨s, by rw [← hs, Fin.sum_univ_two]⟩
  have hL0 : X.lieZero j = Submodule.span B {t 0} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨s, rfl⟩ := hdecomp v
      have hvζ := (Submodule.mem_iInf _).1 hv (teichmuller p ζ)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΛ,
        Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hE 0, hE 1, sub_eq_zero] at hvζ
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, smul_add, smul_smul] at hvζ

      have hcoef := sub_eq_zero.2 hvζ
      rw [add_sub_add_comm, ← sub_smul, ← sub_smul] at hcoef
      have h2 := (hpair _ _ hcoef).2
      have h3 : s 1 * -(j (teichmuller p ζ) - j (teichmuller p ζ) ^ p) = 0 := by rw [← h2]; ring
      have hs1 : s 1 = 0 := (hunit.neg.mul_left_eq_zero).1 h3
      rw [hs1, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, FormalODModule.lieZero, Submodule.mem_iInf]
      intro a
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΛ, h0, sub_self]
  have hL1 : X.lieOne j = Submodule.span B {t 1} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨s, rfl⟩ := hdecomp v
      have hvζ := (Submodule.mem_iInf _).1 hv (teichmuller p ζ)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΛ,
        Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hE 0, hE 1, hfrob_t, map_pow, sub_eq_zero] at hvζ
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, smul_add, smul_smul] at hvζ
      have hcoef := sub_eq_zero.2 hvζ
      rw [add_sub_add_comm, ← sub_smul, ← sub_smul] at hcoef
      have h2 := (hpair _ _ hcoef).1
      have h3 : s 0 * (j (teichmuller p ζ) - j (teichmuller p ζ) ^ p) = 0 := by rw [← h2]; ring
      have hs0 : s 0 = 0 := (hunit.mul_left_eq_zero).1 h3
      rw [hs0, zero_smul, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, FormalODModule.lieOne, Submodule.mem_iInf]
      intro a
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΛ, h1, sub_self]

  have hline : ∀ i : Fin 2, Nonempty (B ≃ₗ[B] ↥(Submodule.span B {t i})) := by
    intro i
    have hinj : ∀ b : B, b • t i = 0 → b = 0 := by
      intro b hb
      fin_cases i
      · exact (hpair b 0 (by rw [zero_smul, add_zero]; exact hb)).1
      · exact (hpair 0 b (by rw [zero_smul, zero_add]; exact hb)).2
    let f : B →ₗ[B] ↥(Submodule.span B {t i}) :=
      (LinearMap.toSpanSingleton B (Fin 2 → B) (t i)).codRestrict _ (fun b =>
        Submodule.mem_span_singleton.2 ⟨b, rfl⟩)
    refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro b b' h
      have : (b - b') • t i = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact congrArg Subtype.val h
      exact sub_eq_zero.1 (hinj _ this)
    · rintro ⟨v, hv⟩
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv
      exact ⟨b, rfl⟩
  have hcompl : IsCompl (Submodule.span B {t 0}) (Submodule.span B {t 1}) := by
    rw [isCompl_iff]
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv0 hv1
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv0
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hv1
      have : a • t 0 + (-b) • t 1 = 0 := by rw [neg_smul, hb, add_neg_cancel]
      rw [(hpair _ _ this).1, zero_smul]
    · rw [codisjoint_iff, eq_top_iff, ← hbasis.2, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hL0, hL1]; exact hcompl
  · rw [hL0]; obtain ⟨e⟩ := hline 0; exact Module.Invertible.congr e
  · rw [hL1]; obtain ⟨e⟩ := hline 1; exact Module.Invertible.congr e

end S_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis (solution)
