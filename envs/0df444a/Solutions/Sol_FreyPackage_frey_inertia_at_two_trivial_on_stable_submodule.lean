-- Prove2me | solution 1 for FreyPackage.frey_inertia_at_two_trivial_on_stable_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c41668df-c00e-575b-871c-bda64ae90f5f

import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_FreyPackage_freyCurve_discriminant
import Theorems.Thm_FreyPackage_frey_wild_inertia_at_two_trivial
import Theorems.Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace LinearMap p2m_export "LinearMap" "surjective_of_injective toAddMonoidHom inverse ker_eq_bot inr mk ext inl restrict conjugate" end LinearMap
p2m_open_scoped "LinearMap" in

theorem LinearMap.eq_id_on_line_of_conj_eq_sq {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (h2 : Module.finrank F V = 2)
    (N : Submodule F V) (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (T M M' : V →ₗ[F] V) (hT : Function.Injective T)
    (hMM' : ∀ x, M (M' x) = x)
    (hTN : ∀ x ∈ N, T x ∈ N) (hMN : ∀ x ∈ N, M x ∈ N) (hM'N : ∀ x ∈ N, M' x ∈ N)
    (hrel : ∀ x, M (T (M' x)) = T (T x)) :
    (∀ x ∈ N, T x = x) ∧ (∀ x, T x - x ∈ N) := by

  have hN1 : Module.finrank F N = 1 := by
    have hlt : Module.finrank F N < 2 := h2 ▸ Submodule.finrank_lt htop
    have hpos : 1 ≤ Module.finrank F N := Submodule.one_le_finrank_iff.mpr hbot
    omega

  have key : ∀ c : F, c = c * c → c = 0 ∨ c = 1 := by
    intro c hc
    have : c * (1 - c) = 0 := by rw [mul_sub, mul_one, ← hc, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm

  have line_arg : ∀ {W : Type _} [AddCommGroup W] [Module F W], Module.finrank F W = 1 →
      ∀ (t m m' : W →ₗ[F] W), Function.Injective t → (∀ w, m (m' w) = w) →
        (∀ w, m (t (m' w)) = t (t w)) → ∀ w, t w = w := by
    intro W _ _ hW t m m' ht hmm' hrel'
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by
      by_contra h
      push Not at h
      haveI : Subsingleton W := ⟨fun a b => by rw [h a, h b]⟩
      have : Module.finrank F W = 0 := Module.finrank_zero_of_subsingleton
      omega
    have hgen : ∀ w : W, ∃ c : F, c • w₀ = w := fun w =>
      (finrank_eq_one_iff_of_nonzero' w₀ hw₀).mp hW w
    obtain ⟨c, hc⟩ := hgen (t w₀)
    obtain ⟨a, ha⟩ := hgen (m w₀)
    obtain ⟨a', ha'⟩ := hgen (m' w₀)

    have haa' : a' * a = 1 := by
      have h1 : (a' * a) • w₀ = w₀ := by
        rw [mul_smul, ha, ← map_smul, ha', hmm']
      by_contra hne
      apply hw₀
      have : (a' * a - 1) • w₀ = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h

    have hcc : c • w₀ = (c * c) • w₀ := by
      have lhs : m (t (m' w₀)) = (a' * c * a) • w₀ := by
        rw [← ha', map_smul, ← hc, map_smul, map_smul, ← ha, smul_smul, smul_smul]
      have rhs : t (t w₀) = (c * c) • w₀ := by
        rw [← hc, map_smul, ← hc, smul_smul]
      have := hrel' w₀
      rw [lhs, rhs] at this
      rwa [show a' * c * a = c by rw [mul_right_comm, haa', one_mul]] at this
    have hc' : c = c * c := by
      have : (c - c * c) • w₀ = 0 := by rw [sub_smul, hcc, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw₀
    have hc1 : c = 1 := by
      rcases key c hc' with h | h
      · exfalso
        apply hw₀
        apply ht
        rw [← hc, h, zero_smul, LinearMap.map_zero]
      · exact h
    intro w
    obtain ⟨d, rfl⟩ := hgen w
    rw [map_smul, ← hc, hc1, one_smul]
  constructor
  ·
    let t : N →ₗ[F] N := T.restrict (p := N) (q := N) hTN
    let m : N →ₗ[F] N := M.restrict (p := N) (q := N) hMN
    let m' : N →ₗ[F] N := M'.restrict (p := N) (q := N) hM'N
    have ht : Function.Injective t := fun a b hab => by
      apply Subtype.ext
      apply hT
      simpa [t] using congrArg Subtype.val hab
    have hmm' : ∀ w, m (m' w) = w := fun w => Subtype.ext (by simp [m, m', hMM'])
    have hrel' : ∀ w, m (t (m' w)) = t (t w) := fun w => Subtype.ext (by simp [m, m', t, hrel])
    intro x hx
    have := line_arg hN1 t m m' ht hmm' hrel' ⟨x, hx⟩
    simpa [t] using congrArg Subtype.val this
  ·
    have hQ1 : Module.finrank F (V ⧸ N) = 1 := by
      have := Submodule.finrank_quotient_add_finrank N
      omega
    have hTN' : N ≤ N.comap T := fun x hx => hTN x hx
    have hMN' : N ≤ N.comap M := fun x hx => hMN x hx
    have hM'N' : N ≤ N.comap M' := fun x hx => hM'N x hx
    let t : V ⧸ N →ₗ[F] V ⧸ N := N.mapQ N T hTN'
    let m : V ⧸ N →ₗ[F] V ⧸ N := N.mapQ N M hMN'
    let m' : V ⧸ N →ₗ[F] V ⧸ N := N.mapQ N M' hM'N'

    have hTonto : ∀ y ∈ N, ∃ x ∈ N, T x = y := by
      let t₀ : N →ₗ[F] N := T.restrict (p := N) (q := N) hTN
      have ht₀ : Function.Injective t₀ := fun a b hab => by
        apply Subtype.ext
        apply hT
        simpa [t₀] using congrArg Subtype.val hab
      have hsurj : Function.Surjective t₀ := LinearMap.surjective_of_injective ht₀
      intro y hy
      obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy⟩
      exact ⟨x, hx, by simpa [t₀] using congrArg Subtype.val hxy⟩
    have ht : Function.Injective t := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      induction z using Submodule.Quotient.induction_on with
      | H x =>
        have hx : T x ∈ N := by
          simpa [t, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] using hz
        obtain ⟨x', hx'N, hx'⟩ := hTonto (T x) hx
        have : x = x' := hT hx'.symm
        rw [Submodule.Quotient.mk_eq_zero, this]
        exact hx'N
    have hmm' : ∀ w, m (m' w) = w := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H x => simp [m, m', Submodule.mapQ_apply, hMM']
    have hrel' : ∀ w, m (t (m' w)) = t (t w) := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H x => simp [m, m', t, Submodule.mapQ_apply, hrel]
    intro x
    have := line_arg hQ1 t m m' ht hmm' hrel' (Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    simpa [t, Submodule.mapQ_apply] using this

theorem solution (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ x ∈ N, σ • x = x) ∧ (∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by
  classical
  intro A hA τ hτ
  haveI : Fact P.p.Prime := ⟨P.pp⟩

  haveI hE : P.freyCurve.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, P.freyCurve_discriminant, isUnit_iff_ne_zero]
    have h : ((P.a : ℚ) * P.b * P.c) ≠ 0 := by exact_mod_cast P.habc0
    exact div_ne_zero (pow_ne_zero _ h) (by norm_num)

  set V := Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p with hV
  have hp : ((P.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast P.hp0
  have hcard : Nat.card V = P.p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ) P.freyCurve hp
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ P.hp0)
  have h2 : Module.finrank (ZMod P.p) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod P.p) (V := V)
    rw [hcard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective P.pp.two_le h).symm

  obtain ⟨φ, hφ⟩ :=
    ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime Nat.prime_two A hA
  obtain ⟨hωI, hωwild⟩ := hφ τ hτ
  have hω : ∀ x : V, (φ * τ * φ⁻¹ * (τ ^ 2)⁻¹) • x = x :=
    P.frey_wild_inertia_at_two_trivial A hA _ hωI hωwild

  have hrel : ∀ x : V, φ • (τ • (φ⁻¹ • x)) = τ • (τ • x) := by
    intro x
    have h1 : (φ * τ * φ⁻¹) • x = ((φ * τ * φ⁻¹ * (τ ^ 2)⁻¹) * τ ^ 2) • x := by
      rw [inv_mul_cancel_right]
    rw [mul_smul _ (τ ^ 2), hω, pow_two, mul_smul, mul_smul, mul_smul] at h1
    exact h1

  let L : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) → V →ₗ[ZMod P.p] V := fun g =>
    (DistribSMul.toAddMonoidHom V g).toZModLinearMap P.p
  have hL : ∀ g (x : V), L g x = g • x := fun g x => rfl
  have hT : Function.Injective (L τ) := fun a b hab => by
    have : τ • a = τ • b := by simpa [hL] using hab
    simpa using congrArg (fun y => τ⁻¹ • y) this
  obtain ⟨hfix, hmove⟩ := LinearMap.eq_id_on_line_of_conj_eq_sq h2 N hbot htop (L τ) (L φ) (L φ⁻¹)
    hT (fun x => by simp [hL])
    (fun x hx => hN τ x hx) (fun x hx => hN φ x hx) (fun x hx => hN φ⁻¹ x hx)
    (fun x => by simpa [hL] using hrel x)
  exact ⟨fun x hx => by simpa [hL] using hfix x hx, fun x => by simpa [hL] using hmove x⟩

end S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule
end P2MW
export P2MW.S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule (solution)
