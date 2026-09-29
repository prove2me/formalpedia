-- Prove2me | solution 1 for FreyPackage.eigenformResidualAttachmentAt_of_realizationSupplyFieldAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0efc5711-610d-51da-955f-3e58abf55c22

import Mathlib.Algebra.Algebra.ZMod
import Definitions.Def_FreyPackage_EigenformRealizationSupplyField
import Definitions.Def_FreyPackage_EigenformResidualAttachment
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_Module_End_trace_eq_of_mul_self_sub_smul_add_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt

set_option autoImplicit false

open Module LinearMap CongruenceSubgroup
p2m_open "ModularCurve P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.ModularCurve"

noncomputable section

noncomputable local instance instDecEqQbarSupplyFieldGlue :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

section Dictionary

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace MonoidHom p2m_export "MonoidHom" "comp mul_apply map_neg mem_ker ker" end MonoidHom
namespace MonoidHom
p2m_open_scoped "MonoidHom" in

private abbrev _root_.MonoidHom.toEndRep {G : Type*} [Monoid G] (ρ : G →* (V ≃ₗ[k] V)) :
    Representation k G V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ

end MonoidHom
p2m_export "" "MonoidHom.toEndRep"
p2m_open_scoped "MonoidHom" in
@[scoped simp] lemma MonoidHom.toEndRep_apply {G : Type*} [Monoid G] (ρ : G →* (V ≃ₗ[k] V)) (g : G) :
    ρ.toEndRep g = (ρ g).toLinearMap := rfl

p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"
end Dictionary
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

namespace FreyPackage
p2m_export "FreyPackage" "EigenformRealizationSupplyFieldAt p a b pp EigenformResidualAttachmentAt"
p2m_open "FreyPackage"

theorem ker_le_toEndRep_ker {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V)) :
    ρ.ker ≤ ρ.toEndRep.ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  rw [MonoidHom.toEndRep_apply, hσ]
  rfl

end FreyPackage
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

namespace ModularCurve
p2m_export "ModularCurve" "IsResidualRealization CyclotomicDeterminant HeckeAlg heckeGen FrobeniusQuadratic JZero UnramifiedOutsideConcrete FrobeniusQuadraticConcrete heckeModuleBar"
p2m_open "ModularCurve"

section ResidualInterface

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {p : ℕ} {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable {k : Type*} [Field k] {φ : HeckeAlg →+* k}
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {π : J → V} {ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V)}

omit [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] in

theorem PTorsion.add {x y : J} (hx : p • x = 0) (hy : p • y = 0) : p • (x + y) = 0 := by
  rw [smul_add, hx, hy, add_zero]

omit [Module HeckeAlg J] in

theorem PTorsion.galois_smul (σ : L ≃ₐ[K] L) {x : J} (hx : p • x = 0) : p • (σ • x) = 0 := by
  have key : ∀ m : ℕ, σ • (m • x) = m • (σ • x) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]
  rw [← key p, hx, smul_zero]

omit [DistribMulAction (L ≃ₐ[K] L) J] in

theorem PTorsion.hecke_smul (t : HeckeAlg) {x : J} (hx : p • x = 0) : p • (t • x) = 0 := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg p (t • x), smul_comm,
    Nat.cast_smul_eq_nsmul HeckeAlg p x, hx, smul_zero]

omit [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] in

theorem PTorsion.nsmul (m : ℕ) {x : J} (hx : p • x = 0) : p • (m • x) = 0 := by
  rw [smul_comm, hx, smul_zero]

omit [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] in

theorem PTorsion.sub {x y : J} (hx : p • x = 0) (hy : p • y = 0) : p • (x - y) = 0 := by
  rw [smul_sub, hx, hy, sub_zero]

omit [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] in

theorem PTorsion.isPPowTorsion {x : J} (hx : p • x = 0) : ∃ n : ℕ, p ^ n • x = 0 :=
  ⟨1, by rw [pow_one]; exact hx⟩

namespace IsResidualRealization
p2m_export "ModularCurve.IsResidualRealization" "map_hecke map_galois map_zero map_add spanning finite finrank_eq"
p2m_open "ModularCurve.IsResidualRealization"

variable (h : IsResidualRealization p J k φ V π ρ)
include h

private lemma _root_.ModularCurve.IsResidualRealization.map_neg (x : J) (hx : p • x = 0) : π (-x) = -π x := by
  have hnx : p • (-x) = 0 := by rw [smul_neg, hx, neg_zero]
  have h0 : π (x + -x) = π x + π (-x) := h.map_add x (-x) hx hnx
  rw [add_neg_cancel, h.map_zero] at h0
  exact (neg_eq_of_add_eq_zero_right h0.symm).symm

p2m_export "ModularCurve.IsResidualRealization" "map_neg"

private lemma _root_.ModularCurve.IsResidualRealization.map_sub (x y : J) (hx : p • x = 0) (hy : p • y = 0) : π (x - y) = π x - π y := by
  have hny : p • (-y) = 0 := by rw [smul_neg, hy, neg_zero]
  rw [sub_eq_add_neg, h.map_add x (-y) hx hny, h.map_neg y hy, ← sub_eq_add_neg]

p2m_export "ModularCurve.IsResidualRealization" "map_sub"

private lemma _root_.ModularCurve.IsResidualRealization.map_nsmul (m : ℕ) (x : J) (hx : p • x = 0) : π (m • x) = (m : k) • π x := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x, h.map_hecke _ x hx, map_natCast]

p2m_export "ModularCurve.IsResidualRealization" "map_nsmul"

private lemma _root_.ModularCurve.IsResidualRealization.linearMap_eq_zero (T : V →ₗ[k] V)
    (hT : ∀ x : J, p • x = 0 → T (π x) = 0) : T = 0 := by
  rw [← LinearMap.ker_eq_top, ← top_le_iff, ← h.spanning, Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  exact hT x hx

p2m_export "ModularCurve.IsResidualRealization" "linearMap_eq_zero"

lemma linearMap_ext {T₁ T₂ : V →ₗ[k] V}
    (hT : ∀ x : J, p • x = 0 → T₁ (π x) = T₂ (π x)) : T₁ = T₂ := by
  have key := h.linearMap_eq_zero (T₁ - T₂) fun x hx => by
    rw [LinearMap.sub_apply, hT x hx, sub_self]
  rwa [sub_eq_zero] at key

end IsResidualRealization
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

end ResidualInterface
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

section Descent

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {N p : ℕ} {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable {k : Type*} [Field k] {φ : HeckeAlg →+* k}
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {π : J → V} {ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V)}

namespace IsResidualRealization p2m_export "ModularCurve.IsResidualRealization" "map_hecke map_galois map_zero map_add spanning finite finrank_eq" end IsResidualRealization
namespace IsResidualRealization
p2m_open_scoped "ModularCurve.IsResidualRealization" in

private theorem _root_.ModularCurve.IsResidualRealization.frobenius_quadratic
    (h : IsResidualRealization p J k φ V π ρ)
    (hES : FrobeniusQuadratic (K := K) (L := L) N p J)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p)
    {A : ValuationSubring L} (hA : A.LiesOverPrime ℓ)
    {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ ℓ) :
    (ρ σ).toLinearMap * (ρ σ).toLinearMap - φ (heckeGen ⟨ℓ, hℓ⟩) • (ρ σ).toLinearMap
      + (ℓ : k) • (1 : Module.End k V) = 0 := by
  apply h.linearMap_eq_zero
  intro x hx

  have hx1 : p • (σ • x) = 0 := PTorsion.galois_smul σ hx
  have hx2 : p • (σ • σ • x) = 0 := PTorsion.galois_smul σ hx1
  have hx3 : p • (heckeGen ⟨ℓ, hℓ⟩ • (σ • x)) = 0 := PTorsion.hecke_smul _ hx1
  have hx4 : p • ((ℓ : ℕ) • x) = 0 := PTorsion.nsmul ℓ hx

  have hrel := hES ℓ hℓ hℓNp A hA σ hσ x (PTorsion.isPPowTorsion hx)

  have e1 : π (σ • σ • x) = (ρ σ) ((ρ σ) (π x)) := by
    rw [h.map_galois σ _ hx1, h.map_galois σ _ hx]
  have e2 : π (heckeGen ⟨ℓ, hℓ⟩ • (σ • x)) = φ (heckeGen ⟨ℓ, hℓ⟩) • (ρ σ) (π x) := by
    rw [h.map_hecke _ _ hx1, h.map_galois σ _ hx]
  have e3 : π ((ℓ : ℕ) • x) = (ℓ : k) • π x := h.map_nsmul ℓ x hx
  have hπ : π (σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x)
      = (ρ σ) ((ρ σ) (π x)) - φ (heckeGen ⟨ℓ, hℓ⟩) • (ρ σ) (π x) + (ℓ : k) • π x := by
    rw [h.map_add _ _ (PTorsion.sub hx2 hx3) hx4, h.map_sub _ _ hx2 hx3, e1, e2, e3]
  calc ((ρ σ).toLinearMap * (ρ σ).toLinearMap - φ (heckeGen ⟨ℓ, hℓ⟩) • (ρ σ).toLinearMap
      + (ℓ : k) • (1 : Module.End k V)) (π x)
      = (ρ σ) ((ρ σ) (π x)) - φ (heckeGen ⟨ℓ, hℓ⟩) • (ρ σ) (π x) + (ℓ : k) • π x := by
        simp [Module.End.mul_apply]
    _ = π (σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x) := hπ.symm
    _ = π 0 := by rw [hrel]
    _ = 0 := h.map_zero

end IsResidualRealization
p2m_export "ModularCurve" "IsResidualRealization.frobenius_quadratic"
end Descent
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

theorem not_dvd_mul_of_prime_of_not_dvd_of_ne {p M ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hdvd : ¬ ℓ ∣ M) (hne : ℓ ≠ p) : ¬ ℓ ∣ M * p := by
  intro h
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h' | h'
  · exact hdvd h'
  · exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h')

private lemma natCast_prime_ne_zero_of_natCast_prime_eq_zero' {k : Type*} [Field k] {p ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) (hpk : (p : k) = 0) : (ℓ : k) ≠ 0 := by
  intro hℓk
  have hcop : Nat.Coprime p ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hne)
  have hbezout := Nat.gcd_eq_gcd_ab p ℓ
  rw [hcop.gcd_eq_one] at hbezout
  have hcast := congrArg (fun z : ℤ => ((z : k))) hbezout
  push_cast at hcast
  rw [hpk, hℓk, zero_mul, zero_mul, add_zero] at hcast
  exact one_ne_zero hcast

namespace IsResidualRealization
p2m_open_scoped "ModularCurve.IsResidualRealization" in

private theorem _root_.ModularCurve.IsResidualRealization.trace_frobenius_eq
    {N p : ℕ} {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    {k : Type*} [Field k] {φ : HeckeAlg →+* k}
    {V : Type*} [AddCommGroup V] [Module k V] {π : J → V}
    {ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V ≃ₗ[k] V)}
    (hreal : IsResidualRealization p J k φ V π ρ)
    (hiii : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    (hdet : CyclotomicDeterminant N p ρ)
    (hp : p.Prime) (hpk : (p : k) = 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime ℓ)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : A.IsFrobeniusAt τ ℓ) :
    LinearMap.trace k V (ρ τ).toLinearMap = φ (heckeGen ⟨ℓ, hℓ⟩) := by
  haveI : Module.Finite k V := hreal.finite
  have b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hreal.finrank_eq
  have hquad := hreal.frobenius_quadratic hiii hℓ hℓNp hA hτ
  have hdetτ := hdet ℓ hℓ hℓNp A hA τ hτ
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact hℓNp (dvd_mul_left ℓ N)
  have hℓk : (ℓ : k) ≠ 0 := natCast_prime_ne_zero_of_natCast_prime_eq_zero' hp hℓ hℓp hpk
  exact Module.End.trace_eq_of_mul_self_sub_smul_add_smul_eq_zero b hquad hdetτ hℓk

end IsResidualRealization
p2m_export "ModularCurve" "IsResidualRealization.trace_frobenius_eq"
end ModularCurve
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

theorem solution (P : FreyPackage) (M : ℕ) [NeZero M] :
    letI := ModularCurve.heckeModuleBar M
    ModularCurve.FrobeniusQuadraticConcrete M P.p → P.EigenformRealizationSupplyFieldAt M →
      P.EigenformResidualAttachmentAt M := by
  letI : Module HeckeAlg (JZero M) := ModularCurve.heckeModuleBar M
  intro hiii hsupply g hg 𝔪 h𝔪 hp𝔪
  obtain ⟨k, ik, φ, V, iV, iMV, π, ρ, ψ, F, iF, iNF, iGF, iAF, iST,
    hpk, hreal, hdet, hker, hcoeff, hF⟩ := hsupply g hg 𝔪 h𝔪 hp𝔪

  haveI : CharP k P.p := (CharP.charP_iff_prime_eq_zero P.pp).mpr hpk
  letI : Algebra (ZMod P.p) k := ZMod.algebra k P.p
  refine ⟨k, ik, inferInstance, V, iV, iMV, ρ.toEndRep, ψ, F, iF, iNF, iGF, iAF, iST,
    hker, hreal.finrank_eq, ?_, ?_, ?_⟩
  ·

    exact le_inf (hF.trans inf_le_left)
      ((hF.trans inf_le_right).trans (FreyPackage.ker_le_toEndRep_ker ρ))
  ·
    intro ℓ hℓ hdvd hne A hA τ hτ
    have hℓMp : ¬ ℓ ∣ M * P.p :=
      ModularCurve.not_dvd_mul_of_prime_of_not_dvd_of_ne P.pp hℓ hdvd hne
    obtain ⟨a, ha, hφa⟩ := hcoeff ℓ hℓ hℓMp
    refine ⟨a, ha, ?_⟩
    have htr := hreal.trace_frobenius_eq hiii hdet P.pp hpk hℓ hℓMp hA hτ
    rw [MonoidHom.toEndRep_apply, htr, hφa]
  ·
    intro ℓ hℓ hdvd hne A hA τ hτ
    have hℓMp : ¬ ℓ ∣ M * P.p :=
      ModularCurve.not_dvd_mul_of_prime_of_not_dvd_of_ne P.pp hℓ hdvd hne
    rw [MonoidHom.toEndRep_apply]
    exact hdet ℓ hℓ hℓMp A hA τ hτ

end
p2m_reactivate "P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt.MonoidHom"

end S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt
end P2MW
export P2MW.S_FreyPackage_eigenformResidualAttachmentAt_of_realizationSupplyFieldAt (solution)
