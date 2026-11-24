-- Prove2me | solution 1 for Formalism.HC.Der.frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:40.048867+00:00
-- url     : https://prove2.me/submissions/7877801d-565f-4857-9ea6-ebc75082112b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_two_dvd_QS
import Theorems.Thm_Formalism_HC_Der_tower_dvd_QSq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_cyc_isGalois
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_HC_Der_exists_over
import Theorems.Thm_Formalism_HC_Der_frob_iff_inertia
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
import Theorems.Thm_Formalism_HC_Der_tauN_frob
import Theorems.Thm_Formalism_HC_Der_tauN_inertia_iff
import Theorems.Thm_Formalism_HC_Der_tauN_root
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
private theorem jac_lemma {p d : ℕ} (hp : p % 2 = 1) (hd : d % 4 = 3) :
    jacobiSym (-(d : ℤ)) p = jacobiSym (p : ℤ) d := by
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hp)]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h (Nat.odd_iff.mpr (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd h]
    ring
private theorem art_snd_lemma (u : (ZMod H.condN)ˣ) :
    (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hz := Cond.z_spec H.condN
  have hx : IsPrimitiveRoot (Cond.z H.condN ^ (H.QS * H.q)) H.d :=
    hz.pow (Nat.pos_of_ne_zero (NeZero.ne H.condN)) rfl
  have hg2 : Cond.gs H.d hx.pow_eq_one ^ 2 = -(H.d : Cond.Cyc H.condN) := Cond.gs_sq hd4 hx
  have hy2 : (emb H H.sqd) ^ 2 = -(H.d : Cond.Cyc H.condN) := by
    rw [← map_pow, H.sqd_sq, map_neg, map_natCast]
  have hy0 : emb H H.sqd ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hy2
    have h0 : (H.d : Cond.Cyc H.condN) = 0 := by linear_combination hy2
    exact H.hyp.2.1.ne_zero (by exact_mod_cast h0)
  have hτx : (tauN H.condN u) (Cond.z H.condN ^ (H.QS * H.q)) =
      (Cond.z H.condN ^ (H.QS * H.q)) ^ (u : ZMod H.condN).val :=
    tauN_root H.condN u _ (by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow])
  have hcopv : Nat.Coprime (u : ZMod H.condN).val H.d :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left H.d (H.QS * H.q)) (ZMod.val_coe_unit_coprime u)
  have hτg : (tauN H.condN u) (Cond.gs H.d hx.pow_eq_one) =
      ((jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d : ℤ) : Cond.Cyc H.condN) *
        Cond.gs H.d hx.pow_eq_one :=
    Formalism.HC.D7.gs_act hx.pow_eq_one
      ((tauN H.condN u : Cond.Cyc H.condN ≃ₐ[ℚ] Cond.Cyc H.condN) : Cond.Cyc H.condN →+* Cond.Cyc H.condN)
      _ hτx hcopv
  have hτy : (tauN H.condN u) (emb H H.sqd) =
      ((jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d : ℤ) : Cond.Cyc H.condN) * emb H H.sqd := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy2.trans hg2.symm) with h | h
    · rw [h]
      exact hτg
    · rw [h, map_neg, hτg, mul_neg]
  have hσ := H.gal_sqd (H.gal.symm (H.art u))
  rw [MulEquiv.apply_symm_apply] at hσ
  have h2 := emb_art H u H.sqd
  rw [hσ, map_mul, map_intCast, hτy] at h2
  have h3 := mul_right_cancel₀ hy0 h2
  exact_mod_cast h3
end Formalism.HC.Der
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
  intro p _ hpN P _ _
  have hp : p.Prime := Fact.out
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hcop : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hfact : ordCompl[p] H.condN = H.condN := by
    rw [Nat.factorization_eq_zero_of_not_dvd hpN, pow_zero, Nat.div_one]
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, hI, hF⟩ := exists_over (emb H) p P
  have hval : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN) = p →
      (u : ZMod H.condN).val ≡ p [MOD ordCompl[p] H.condN] := by
    intro u hu
    rw [hfact, hu, ZMod.val_natCast]
    exact Nat.mod_modEq p _
  have hfu : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN) = p → ∀ σ : H.E ≃ₐ[ℚ] H.E,
      H.gal σ = H.art u → IsArithFrobAt ℤ σ P := fun u hu σ hσ =>
    hF σ (tauN H.condN u) ((gal_eq_art_iff H σ u).mp hσ) (tauN_frob H.condN p Q u (hval u hu))
  have hinert : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
    intro σ
    constructor
    · intro h
      obtain ⟨τ, hτ1, hτ2⟩ := (hI σ).mp h
      obtain ⟨w, rfl⟩ := (tauN H.condN).surjective τ
      have h1 := (tauN_inertia_iff H.condN p Q w).mp hτ2
      rw [hfact] at h1
      have hw1 : w = 1 := by
        apply Units.ext
        rw [Units.val_one, ← ZMod.natCast_zmod_val (w : ZMod H.condN), ← Nat.cast_one,
          ZMod.natCast_eq_natCast_iff]
        exact h1
      subst hw1
      apply AlgEquiv.ext
      intro x
      apply (emb H).toRingHom.injective
      show emb H (σ x) = emb H x
      rw [hτ1 x, map_one, AlgEquiv.one_apply]
    · rintro rfl x
      simp
  have hiff : ∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
      (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u) := by
    intro σ u hu
    constructor
    · intro hσ
      have hσ' := hfu u hu (H.gal.symm (H.art u)) (H.gal.apply_symm_apply _)
      have h1 := (hinert _).mp ((frob_iff_inertia P _ σ hσ').mp hσ)
      rw [mul_inv_eq_one] at h1
      rw [h1, MulEquiv.apply_symm_apply]
    · exact hfu u hu σ
  have hu0 : ((ZMod.unitOfCoprime p hcop : (ZMod H.condN)ˣ) : ZMod H.condN) = p :=
    ZMod.coe_unitOfCoprime _ _
  refine ⟨⟨H.gal.symm (H.art (ZMod.unitOfCoprime p hcop)),
    hfu _ hu0 _ (H.gal.apply_symm_apply _)⟩, hiff, fun σ hσ => ?_, hinert⟩
  have hg := (hiff σ _ hu0).mp hσ
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN ((two_dvd_QS H).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    unfold HostRaw.psAt
    rw [dif_pos hcop]
  · rw [hg, art_snd_lemma H, hu0, ZMod.val_natCast, jac_lemma hpodd hd4,
      jacobiSym.mod_left ((p % H.condN : ℕ) : ℤ), jacobiSym.mod_left (p : ℤ)]
    congr 1
    push_cast
    exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)
  · have h2 : 2 ^ (φ.e + 2) ∣ H.condN := (tower_dvd_QSq H).trans (QSq_dvd H)
    have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    refine ⟨ZMod.unitOfCoprime p hc2, ZMod.coe_unitOfCoprime _ _, ?_⟩
    rw [hg]
    apply H.art_h
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq p H.condN).of_dvd h2).symm
end Formalism.HC.Der
