-- Prove2me | solution 1 for CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c25a566a-252e-5656-bb1b-af28d8e9c1bc

import Mathlib
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Theorems.Thm_CerednikDrinfeld_ribbon_kernelEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching

set_option autoImplicit false

p2m_open "ModularCurve CerednikDrinfeld P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "TwoPlaceTorsionDatum JPrimeTorsionDatum DegeneracyData ribbonKernel ribbonGram ribbonComponentGroup ribbonComponentGroupProj HeckeData heckeKernelMap Matching ribbon_kernelEquiv"
p2m_open "CerednikDrinfeld"

namespace RibbonTransport

variable {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}

omit [Fintype V₁] [Fintype V₂] in

theorem map_dualMap_range_ribbonGram_eq
    (e : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂))
    (hiso : ∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (e x) (e y) = ribbonGram D₁ x y) :
    (LinearMap.range (ribbonGram D₁)).map (e.symm.dualMap : Module.Dual ℤ ↥(ribbonKernel D₁) →ₗ[ℤ] Module.Dual ℤ ↥(ribbonKernel D₂)) =
      LinearMap.range (ribbonGram D₂) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hf
    refine LinearMap.mem_range.mpr ⟨e x, ?_⟩
    ext y
    simp only [LinearEquiv.coe_coe, LinearEquiv.dualMap_apply]
    conv_lhs => rw [← e.apply_symm_apply y]
    exact hiso x (e.symm y)
  · rintro _ ⟨x', rfl⟩
    refine ⟨ribbonGram D₁ (e.symm x'), LinearMap.mem_range.mpr ⟨e.symm x', rfl⟩, ?_⟩
    ext y
    simp only [LinearEquiv.coe_coe, LinearEquiv.dualMap_apply]
    conv_rhs => rw [← e.apply_symm_apply x', ← e.apply_symm_apply y]
    exact (hiso (e.symm x') (e.symm y)).symm

noncomputable def psi
    (e : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂))
    (hiso : ∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (e x) (e y) = ribbonGram D₁ x y) :
    ribbonComponentGroup D₁ ≃ₗ[ℤ] ribbonComponentGroup D₂ :=
  Submodule.Quotient.equiv (LinearMap.range (ribbonGram D₁)) (LinearMap.range (ribbonGram D₂)) e.symm.dualMap
    (map_dualMap_range_ribbonGram_eq e hiso)

omit [Fintype V₁] [Fintype V₂] in

theorem psi_proj
    (e : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂))
    (hiso : ∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (e x) (e y) = ribbonGram D₁ x y)
    (φ : Module.Dual ℤ ↥(ribbonKernel D₁)) :
    psi e hiso (ribbonComponentGroupProj D₁ φ) = ribbonComponentGroupProj D₂ (φ ∘ₗ (e.symm : ↥(ribbonKernel D₂) →ₗ[ℤ] ↥(ribbonKernel D₁))) :=
  rfl

def precomp (p : ℕ) (e : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂)) :
    (↥(ribbonKernel D₁) →ₗ[ℤ] ZMod p) ≃+ (↥(ribbonKernel D₂) →ₗ[ℤ] ZMod p) where
  toFun f := f ∘ₗ (e.symm : ↥(ribbonKernel D₂) →ₗ[ℤ] ↥(ribbonKernel D₁))
  invFun g := g ∘ₗ (e : ↥(ribbonKernel D₁) →ₗ[ℤ] ↥(ribbonKernel D₂))
  left_inv f := by ext x; simp
  right_inv g := by ext y; simp
  map_add' f g := by ext; simp

omit [Fintype V₁] [Fintype V₂] in
@[scoped simp] theorem precomp_apply (p : ℕ) (e : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂)) (f : ↥(ribbonKernel D₁) →ₗ[ℤ] ZMod p) :
    precomp p e f = f ∘ₗ (e.symm : ↥(ribbonKernel D₂) →ₗ[ℤ] ↥(ribbonKernel D₁)) := rfl

theorem heckeKernelMap_comp_symm {H₁ : HeckeData D₁} {H₂ : HeckeData D₂}
    (e : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂))
    (he : ∀ (ℓ : Nat.Primes) (x : ↥(ribbonKernel D₁)), e (heckeKernelMap H₁ ℓ x) = heckeKernelMap H₂ ℓ (e x))
    (ℓ : Nat.Primes) (y : ↥(ribbonKernel D₂)) :
    heckeKernelMap H₁ ℓ (e.symm y) = e.symm (heckeKernelMap H₂ ℓ y) := by
  apply e.injective
  rw [he, e.apply_symm_apply, e.apply_symm_apply]

end RibbonTransport
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.RibbonTransport"

namespace JPrimeTorsionDatum
p2m_export "CerednikDrinfeld.JPrimeTorsionDatum" "LocalLaws GoodReductionOutside invariants comm pTorsion finiteLevel hecke toric T gal sp D toricEquiv H"
p2m_open "CerednikDrinfeld.JPrimeTorsionDatum"

open RibbonTransport

variable {p : ℕ} {E V E' V' : Type} [Fintype E] [Fintype V] [DecidableEq V] [Fintype E'] [Fintype V'] [DecidableEq V']
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  {D' : DegeneracyData E' V'}

@[reducible] private noncomputable def _root_.CerednikDrinfeld.JPrimeTorsionDatum.transport (Dm : JPrimeTorsionDatum p E V A) (H' : HeckeData D')
    (e : ↥(ribbonKernel Dm.D) ≃ₗ[ℤ] ↥(ribbonKernel D'))
    (hiso : ∀ x y : ↥(ribbonKernel Dm.D), ribbonGram D' (e x) (e y) = ribbonGram Dm.D x y) :
    JPrimeTorsionDatum p E' V' A where
  D := D'
  H := H'
  T := Dm.T
  pTorsion := Dm.pTorsion
  hecke := Dm.hecke
  gal := Dm.gal
  comm := Dm.comm
  finiteLevel := Dm.finiteLevel
  toric := Dm.toric
  toricEquiv := Dm.toricEquiv.trans (precomp p e)
  sp := (psi e hiso).toLinearMap.toAddMonoidHom.comp Dm.sp

p2m_export "CerednikDrinfeld.JPrimeTorsionDatum" "transport"
section

variable (Dm : JPrimeTorsionDatum p E V A) (H' : HeckeData D')
    (e : ↥(ribbonKernel Dm.D) ≃ₗ[ℤ] ↥(ribbonKernel D'))
    (hiso : ∀ x y : ↥(ribbonKernel Dm.D), ribbonGram D' (e x) (e y) = ribbonGram Dm.D x y)

@[scoped simp] theorem transport_D : (Dm.transport H' e hiso).D = D' := rfl
@[scoped simp] theorem transport_H : (Dm.transport H' e hiso).H = H' := rfl
@[scoped simp] theorem transport_T : (Dm.transport H' e hiso).T = Dm.T := rfl
@[scoped simp] theorem transport_hecke : (Dm.transport H' e hiso).hecke = Dm.hecke := rfl
@[scoped simp] theorem transport_gal : (Dm.transport H' e hiso).gal = Dm.gal := rfl
@[scoped simp] theorem transport_toric : (Dm.transport H' e hiso).toric = Dm.toric := rfl
theorem transport_invariants : (Dm.transport H' e hiso).invariants = Dm.invariants := rfl
theorem transport_toricEquiv_apply (t : ↥Dm.toric) :
    (Dm.transport H' e hiso).toricEquiv t = (Dm.toricEquiv t) ∘ₗ (e.symm : ↥(ribbonKernel D') →ₗ[ℤ] ↥(ribbonKernel Dm.D)) := rfl
theorem transport_sp_apply (t : ↥Dm.invariants) :
    (Dm.transport H' e hiso).sp t = psi e hiso (Dm.sp t) := rfl

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.RibbonTransport"

theorem hecke_mem_invariants (Dm : JPrimeTorsionDatum p E V A) (x : HeckeAlg) {t : Dm.T} (ht : t ∈ Dm.invariants) :
    Dm.hecke x t ∈ Dm.invariants := by
  simp only [invariants, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom, sub_eq_zero] at ht ⊢
  intro σ hσ
  rw [Dm.comm σ x t, ht σ hσ]

theorem sp_hecke_ringHom_of_sp_hecke (Dm : JPrimeTorsionDatum p E V A)
    (hsp : ∀ (ℓ : Nat.Primes) (t : ↥Dm.invariants)
      (hℓt : Dm.hecke (heckeGen ℓ) (t : Dm.T) ∈ Dm.invariants)
      (φ : Module.Dual ℤ ↥(ribbonKernel Dm.D)),
      Dm.sp t = ribbonComponentGroupProj Dm.D φ →
        Dm.sp ⟨Dm.hecke (heckeGen ℓ) (t : Dm.T), hℓt⟩ =
          ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H ℓ))
    (heckeΨ : HeckeAlg →+* Module.End ℤ (ribbonComponentGroup Dm.D))
    (hgen : ∀ (ℓ : Nat.Primes) (φ : Module.Dual ℤ ↥(ribbonKernel Dm.D)),
      heckeΨ (heckeGen ℓ) (ribbonComponentGroupProj Dm.D φ) =
        ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H ℓ))
    (x : HeckeAlg) (t : ↥Dm.invariants) (ht : Dm.hecke x (t : Dm.T) ∈ Dm.invariants) :
    Dm.sp ⟨Dm.hecke x (t : Dm.T), ht⟩ = heckeΨ x (Dm.sp t) := by
  revert ht t
  induction x using MvPolynomial.induction_on with
  | C a =>
    intro t ht
    have hC : (MvPolynomial.C a : HeckeAlg) = (a : HeckeAlg) := eq_intCast MvPolynomial.C a
    have h1 : Dm.hecke (MvPolynomial.C a) (t : Dm.T) = a • (t : Dm.T) := by
      rw [hC, map_intCast, Module.End.intCast_apply]
    have h2 : heckeΨ (MvPolynomial.C a) (Dm.sp t) = a • Dm.sp t := by
      rw [hC, map_intCast, Module.End.intCast_apply]
    have h3 : Dm.sp ⟨Dm.hecke (MvPolynomial.C a) (t : Dm.T), ht⟩ = Dm.sp (a • t) := by
      congr 1
      exact Subtype.ext (by simp)
    have h4 : Dm.sp (a • t) = a • Dm.sp t := map_zsmul Dm.sp a t
    rw [h3]
    exact h4.trans h2.symm
  | add f g hf hg =>
    intro t ht
    have hf' : Dm.hecke f (t : Dm.T) ∈ Dm.invariants := hecke_mem_invariants Dm f t.2
    have hg' : Dm.hecke g (t : Dm.T) ∈ Dm.invariants := hecke_mem_invariants Dm g t.2
    have h3 : Dm.sp ⟨Dm.hecke (f + g) (t : Dm.T), ht⟩ =
        Dm.sp ⟨Dm.hecke f (t : Dm.T), hf'⟩ + Dm.sp ⟨Dm.hecke g (t : Dm.T), hg'⟩ := by
      rw [← map_add]
      congr 1
      exact Subtype.ext (by
        change Dm.hecke (f + g) (t : Dm.T) = Dm.hecke f (t : Dm.T) + Dm.hecke g (t : Dm.T)
        rw [map_add, LinearMap.add_apply])
    rw [h3, hf t hf', hg t hg', map_add, LinearMap.add_apply]
  | mul_X f n hf =>
    intro t ht
    have hn : Dm.hecke (heckeGen n) (t : Dm.T) ∈ Dm.invariants := hecke_mem_invariants Dm _ t.2
    obtain ⟨φ, hφ⟩ := Submodule.mkQ_surjective _ (Dm.sp t)
    have hgenstep : Dm.sp ⟨Dm.hecke (heckeGen n) (t : Dm.T), hn⟩ = heckeΨ (heckeGen n) (Dm.sp t) :=
      calc Dm.sp ⟨Dm.hecke (heckeGen n) (t : Dm.T), hn⟩
          = ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H n) := hsp n t hn φ hφ.symm
        _ = heckeΨ (heckeGen n) (ribbonComponentGroupProj Dm.D φ) := (hgen n φ).symm
        _ = heckeΨ (heckeGen n) (Dm.sp t) := by rw [← hφ]
    have h3 : Dm.sp ⟨Dm.hecke (f * heckeGen n) (t : Dm.T), ht⟩ =
        Dm.sp ⟨Dm.hecke f (Dm.hecke (heckeGen n) (t : Dm.T)), hecke_mem_invariants Dm f hn⟩ := by
      congr 1
      exact Subtype.ext (by
        change Dm.hecke (f * heckeGen n) (t : Dm.T) = Dm.hecke f (Dm.hecke (heckeGen n) (t : Dm.T))
        rw [map_mul]
        rfl)
    show Dm.sp ⟨Dm.hecke (f * heckeGen n) (t : Dm.T), ht⟩ = heckeΨ (f * heckeGen n) (Dm.sp t)
    calc Dm.sp ⟨Dm.hecke (f * heckeGen n) (t : Dm.T), ht⟩
        = Dm.sp ⟨Dm.hecke f (Dm.hecke (heckeGen n) (t : Dm.T)), hecke_mem_invariants Dm f hn⟩ := h3
      _ = heckeΨ f (Dm.sp ⟨Dm.hecke (heckeGen n) (t : Dm.T), hn⟩) :=
          hf ⟨Dm.hecke (heckeGen n) (t : Dm.T), hn⟩ (hecke_mem_invariants Dm f hn)
      _ = heckeΨ f (heckeΨ (heckeGen n) (Dm.sp t)) := by rw [hgenstep]
      _ = heckeΨ (f * heckeGen n) (Dm.sp t) := by rw [map_mul]; rfl

namespace LocalLaws p2m_export "CerednikDrinfeld.JPrimeTorsionDatum.LocalLaws" "frobenius_toric toric_le_invariants frobenius_quot sp_hecke sp_hecke_ringHom toricEquiv_hecke mem_range_sp_iff toric_hecke sp_eq_zero_iff" end LocalLaws
namespace LocalLaws
p2m_open_scoped "CerednikDrinfeld.JPrimeTorsionDatum.LocalLaws" in

private theorem _root_.CerednikDrinfeld.JPrimeTorsionDatum.LocalLaws.transport {Dm : JPrimeTorsionDatum p E V A} {r : ℕ} [Fact r.Prime] (h : Dm.LocalLaws r)
    (H' : HeckeData D')
    (e : ↥(ribbonKernel Dm.D) ≃ₗ[ℤ] ↥(ribbonKernel D'))
    (he : ∀ (ℓ : Nat.Primes) (x : ↥(ribbonKernel Dm.D)), e (heckeKernelMap Dm.H ℓ x) = heckeKernelMap H' ℓ (e x))
    (hiso : ∀ x y : ↥(ribbonKernel Dm.D), ribbonGram D' (e x) (e y) = ribbonGram Dm.D x y) :
    (Dm.transport H' e hiso).LocalLaws r where
  toric_hecke := h.toric_hecke
  toricEquiv_hecke := by
    intro ℓ t ht hℓt
    have hlaw : Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = Dm.toricEquiv ⟨t, ht⟩ ∘ₗ heckeKernelMap Dm.H ℓ :=
      h.toricEquiv_hecke ℓ t ht hℓt
    show Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ ∘ₗ (e.symm : ↥(ribbonKernel D') →ₗ[ℤ] ↥(ribbonKernel Dm.D)) =
      (Dm.toricEquiv ⟨t, ht⟩ ∘ₗ (e.symm : ↥(ribbonKernel D') →ₗ[ℤ] ↥(ribbonKernel Dm.D))) ∘ₗ heckeKernelMap H' ℓ
    rw [hlaw, LinearMap.comp_assoc, LinearMap.comp_assoc]
    congr 1
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact heckeKernelMap_comp_symm e he ℓ y
  toric_le_invariants := h.toric_le_invariants
  sp_eq_zero_iff := by
    intro t
    show psi e hiso (Dm.sp t) = 0 ↔ (t : Dm.T) ∈ Dm.toric
    exact (psi e hiso).map_eq_zero_iff.trans (h.sp_eq_zero_iff t)
  mem_range_sp_iff := by
    intro (ψ' : ribbonComponentGroup D')
    show ψ' ∈ ((psi e hiso).toLinearMap.toAddMonoidHom.comp Dm.sp).range ↔ p • ψ' = 0
    constructor
    · rintro ⟨t, rfl⟩
      show p • psi e hiso (Dm.sp t) = 0
      rw [← map_nsmul, (h.mem_range_sp_iff (Dm.sp t)).mp ⟨t, rfl⟩, map_zero]
    · intro hp
      have hp' : p • (psi e hiso).symm ψ' = 0 := by rw [← map_nsmul, hp, map_zero]
      obtain ⟨t, ht⟩ := (h.mem_range_sp_iff ((psi e hiso).symm ψ')).mpr hp'
      refine ⟨t, ?_⟩
      show psi e hiso (Dm.sp t) = ψ'
      rw [ht, LinearEquiv.apply_symm_apply]
  sp_hecke := by
    intro ℓ t hℓt φ' hφ'
    rw [transport_sp_apply] at hφ' ⊢

    set φ : Module.Dual ℤ ↥(ribbonKernel Dm.D) := φ' ∘ₗ (e : ↥(ribbonKernel Dm.D) →ₗ[ℤ] ↥(ribbonKernel D')) with hφ
    have hrep : psi e hiso (ribbonComponentGroupProj Dm.D φ) = ribbonComponentGroupProj D' φ' := by
      rw [psi_proj]
      congr 1
      apply LinearMap.ext; intro y
      simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have hsp : Dm.sp t = ribbonComponentGroupProj Dm.D φ := (psi e hiso).injective (hφ'.trans hrep.symm)
    rw [h.sp_hecke ℓ t hℓt φ hsp, psi_proj]
    congr 1
    apply LinearMap.ext; intro y
    simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [heckeKernelMap_comp_symm e he ℓ y]
    exact congrArg φ' (e.apply_symm_apply _)
  sp_hecke_ringHom := by
    intro heckeΨ hgen x t ht
    refine sp_hecke_ringHom_of_sp_hecke (Dm.transport H' e hiso) ?_ heckeΨ hgen x t ht

    intro ℓ t hℓt φ' hφ'
    rw [transport_sp_apply] at hφ' ⊢
    set φ : Module.Dual ℤ ↥(ribbonKernel Dm.D) := φ' ∘ₗ (e : ↥(ribbonKernel Dm.D) →ₗ[ℤ] ↥(ribbonKernel D')) with hφ
    have hrep : psi e hiso (ribbonComponentGroupProj Dm.D φ) = ribbonComponentGroupProj D' φ' := by
      rw [psi_proj]
      congr 1
      apply LinearMap.ext; intro y
      simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have hsp : Dm.sp t = ribbonComponentGroupProj Dm.D φ := (psi e hiso).injective (hφ'.trans hrep.symm)
    rw [h.sp_hecke ℓ t hℓt φ hsp, psi_proj]
    congr 1
    apply LinearMap.ext; intro y
    simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [heckeKernelMap_comp_symm e he ℓ y]
    exact congrArg φ' (e.apply_symm_apply _)
  frobenius_toric := h.frobenius_toric
  frobenius_quot := h.frobenius_quot

end LocalLaws
p2m_export "CerednikDrinfeld.JPrimeTorsionDatum" "LocalLaws.transport"
namespace GoodReductionOutside p2m_export "CerednikDrinfeld.JPrimeTorsionDatum.GoodReductionOutside" "unramified eichlerShimura" end GoodReductionOutside
namespace GoodReductionOutside
p2m_open_scoped "CerednikDrinfeld.JPrimeTorsionDatum.GoodReductionOutside" in

private theorem _root_.CerednikDrinfeld.JPrimeTorsionDatum.GoodReductionOutside.transport {Dm : JPrimeTorsionDatum p E V A} {M : ℕ} (h : Dm.GoodReductionOutside M)
    (H' : HeckeData D')
    (e : ↥(ribbonKernel Dm.D) ≃ₗ[ℤ] ↥(ribbonKernel D'))
    (hiso : ∀ x y : ↥(ribbonKernel Dm.D), ribbonGram D' (e x) (e y) = ribbonGram Dm.D x y) :
    (Dm.transport H' e hiso).GoodReductionOutside M where
  unramified := h.unramified
  eichlerShimura := h.eichlerShimura

end GoodReductionOutside
p2m_export "CerednikDrinfeld.JPrimeTorsionDatum" "GoodReductionOutside.transport"
end JPrimeTorsionDatum
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.RibbonTransport P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.JPrimeTorsionDatum"

namespace TwoPlaceTorsionDatum
p2m_export "CerednikDrinfeld.TwoPlaceTorsionDatum" "fst snd Laws toric₁ T toricEquiv₁ hecke finiteLevel toricEquiv₂ sp₂ pTorsion comm gal sp₁ toric₂"
p2m_open "CerednikDrinfeld.TwoPlaceTorsionDatum"

open RibbonTransport

variable {p : ℕ} {E₁ V₁ E₁' V₁' E₂ V₂ E₂' V₂' : Type}
  [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₁'] [Fintype V₁'] [DecidableEq V₁']
  [Fintype E₂] [Fintype V₂] [DecidableEq V₂] [Fintype E₂'] [Fintype V₂'] [DecidableEq V₂']
  {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₁' : DegeneracyData E₁' V₁'} {H₁' : HeckeData D₁'}
  {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂} {D₂' : DegeneracyData E₂' V₂'} {H₂' : HeckeData D₂'}
  {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}

@[reducible] private noncomputable def _root_.CerednikDrinfeld.TwoPlaceTorsionDatum.transport (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (H₁' : HeckeData D₁') (H₂' : HeckeData D₂')
    (e₁ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₁'))
    (hiso₁ : ∀ x y : ↥(ribbonKernel D₁), ribbonGram D₁' (e₁ x) (e₁ y) = ribbonGram D₁ x y)
    (e₂ : ↥(ribbonKernel D₂) ≃ₗ[ℤ] ↥(ribbonKernel D₂'))
    (hiso₂ : ∀ x y : ↥(ribbonKernel D₂), ribbonGram D₂' (e₂ x) (e₂ y) = ribbonGram D₂ x y) :
    TwoPlaceTorsionDatum p D₁' H₁' D₂' H₂' A₁ A₂ where
  T := 𝒥.T
  pTorsion := 𝒥.pTorsion
  hecke := 𝒥.hecke
  gal := 𝒥.gal
  comm := 𝒥.comm
  finiteLevel := 𝒥.finiteLevel
  toric₁ := 𝒥.toric₁
  toricEquiv₁ := 𝒥.toricEquiv₁.trans (precomp p e₁)
  sp₁ := (psi e₁ hiso₁).toLinearMap.toAddMonoidHom.comp 𝒥.sp₁
  toric₂ := 𝒥.toric₂
  toricEquiv₂ := 𝒥.toricEquiv₂.trans (precomp p e₂)
  sp₂ := (psi e₂ hiso₂).toLinearMap.toAddMonoidHom.comp 𝒥.sp₂

p2m_export "CerednikDrinfeld.TwoPlaceTorsionDatum" "transport"
theorem transport_fst (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (H₁' : HeckeData D₁') (H₂' : HeckeData D₂') (e₁ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₁')) (hiso₁)
    (e₂ : ↥(ribbonKernel D₂) ≃ₗ[ℤ] ↥(ribbonKernel D₂')) (hiso₂) :
    (𝒥.transport H₁' H₂' e₁ hiso₁ e₂ hiso₂).fst = 𝒥.fst.transport H₁' e₁ hiso₁ := rfl

theorem transport_snd (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (H₁' : HeckeData D₁') (H₂' : HeckeData D₂') (e₁ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₁')) (hiso₁)
    (e₂ : ↥(ribbonKernel D₂) ≃ₗ[ℤ] ↥(ribbonKernel D₂')) (hiso₂) :
    (𝒥.transport H₁' H₂' e₁ hiso₁ e₂ hiso₂).snd = 𝒥.snd.transport H₂' e₂ hiso₂ := rfl

namespace Laws p2m_export "CerednikDrinfeld.TwoPlaceTorsionDatum.Laws" "fst snd goodReduction" end Laws
namespace Laws
p2m_open_scoped "CerednikDrinfeld.TwoPlaceTorsionDatum.Laws" in

private theorem _root_.CerednikDrinfeld.TwoPlaceTorsionDatum.Laws.transport {𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂} {M r₁ r₂ : ℕ} [Fact r₁.Prime] [Fact r₂.Prime]
    (h𝒥 : 𝒥.Laws M r₁ r₂) (H₁' : HeckeData D₁') (H₂' : HeckeData D₂')
    (e₁ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₁'))
    (he₁ : ∀ (ℓ : Nat.Primes) (x : ↥(ribbonKernel D₁)), e₁ (heckeKernelMap H₁ ℓ x) = heckeKernelMap H₁' ℓ (e₁ x))
    (hiso₁ : ∀ x y : ↥(ribbonKernel D₁), ribbonGram D₁' (e₁ x) (e₁ y) = ribbonGram D₁ x y)
    (e₂ : ↥(ribbonKernel D₂) ≃ₗ[ℤ] ↥(ribbonKernel D₂'))
    (he₂ : ∀ (ℓ : Nat.Primes) (x : ↥(ribbonKernel D₂)), e₂ (heckeKernelMap H₂ ℓ x) = heckeKernelMap H₂' ℓ (e₂ x))
    (hiso₂ : ∀ x y : ↥(ribbonKernel D₂), ribbonGram D₂' (e₂ x) (e₂ y) = ribbonGram D₂ x y) :
    (𝒥.transport H₁' H₂' e₁ hiso₁ e₂ hiso₂).Laws M r₁ r₂ where
  goodReduction := by rw [transport_fst]; exact h𝒥.goodReduction.transport H₁' e₁ hiso₁
  fst := by rw [transport_fst]; exact h𝒥.fst.transport H₁' e₁ he₁ hiso₁
  snd := by rw [transport_snd]; exact h𝒥.snd.transport H₂' e₂ he₂ hiso₂

end Laws
p2m_export "CerednikDrinfeld.TwoPlaceTorsionDatum" "Laws.transport"

theorem exists_laws_of_kernelEquiv (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (H₁' : HeckeData D₁') (H₂' : HeckeData D₂')
    (e₁ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₁'))
    (he₁ : ∀ (ℓ : Nat.Primes) (x : ↥(ribbonKernel D₁)), e₁ (heckeKernelMap H₁ ℓ x) = heckeKernelMap H₁' ℓ (e₁ x))
    (hiso₁ : ∀ x y : ↥(ribbonKernel D₁), ribbonGram D₁' (e₁ x) (e₁ y) = ribbonGram D₁ x y)
    (e₂ : ↥(ribbonKernel D₂) ≃ₗ[ℤ] ↥(ribbonKernel D₂'))
    (he₂ : ∀ (ℓ : Nat.Primes) (x : ↥(ribbonKernel D₂)), e₂ (heckeKernelMap H₂ ℓ x) = heckeKernelMap H₂' ℓ (e₂ x))
    (hiso₂ : ∀ x y : ↥(ribbonKernel D₂), ribbonGram D₂' (e₂ x) (e₂ y) = ribbonGram D₂ x y)
    (M r₁ r₂ : ℕ) [Fact r₁.Prime] [Fact r₂.Prime] (h𝒥 : 𝒥.Laws M r₁ r₂) :
    ∃ 𝒥' : TwoPlaceTorsionDatum p D₁' H₁' D₂' H₂' A₁ A₂, 𝒥'.Laws M r₁ r₂ :=
  ⟨𝒥.transport H₁' H₂' e₁ hiso₁ e₂ hiso₂, h𝒥.transport H₁' H₂' e₁ he₁ hiso₁ e₂ he₂ hiso₂⟩

theorem exists_laws_of_matching
    {p : ℕ} {E₁ V₁ E₁' V₁' E₂ V₂ E₂' V₂' : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₁'] [Fintype V₁'] [DecidableEq V₁']
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂] [Fintype E₂'] [Fintype V₂'] [DecidableEq V₂']
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₁' : DegeneracyData E₁' V₁'} {H₁' : HeckeData D₁'}
    {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂} {D₂' : DegeneracyData E₂' V₂'} {H₂' : HeckeData D₂'}
    (M₁ : Matching H₁ H₁') (M₂ : Matching H₂ H₂')
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (M : ℕ) (r₁ r₂ : ℕ) [Fact r₁.Prime] [Fact r₂.Prime]
    (h𝒥 : 𝒥.Laws M r₁ r₂) :
    ∃ 𝒥' : TwoPlaceTorsionDatum p D₁' H₁' D₂' H₂' A₁ A₂, 𝒥'.Laws M r₁ r₂ := by
  obtain ⟨e₁, he₁, hiso₁⟩ := ribbon_kernelEquiv H₁ H₁' M₁
  obtain ⟨e₂, he₂, hiso₂⟩ := ribbon_kernelEquiv H₂ H₂' M₂
  exact exists_laws_of_kernelEquiv 𝒥 H₁' H₂' e₁ he₁ hiso₁ e₂ he₂ hiso₂ M r₁ r₂ h𝒥

end TwoPlaceTorsionDatum
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.RibbonTransport P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.JPrimeTorsionDatum"

end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.RibbonTransport P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld.JPrimeTorsionDatum P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.CerednikDrinfeld"

theorem solution
    {p : ℕ} {E₁ V₁ E₁' V₁' E₂ V₂ E₂' V₂' : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₁'] [Fintype V₁'] [DecidableEq V₁']
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂] [Fintype E₂'] [Fintype V₂'] [DecidableEq V₂']
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₁' : DegeneracyData E₁' V₁'} {H₁' : HeckeData D₁'}
    {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂} {D₂' : DegeneracyData E₂' V₂'} {H₂' : HeckeData D₂'}
    (M₁ : Matching H₁ H₁') (M₂ : Matching H₂ H₂')
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (M : ℕ) (r₁ r₂ : ℕ) [Fact r₁.Prime] [Fact r₂.Prime]
    (h𝒥 : 𝒥.Laws M r₁ r₂) :
    ∃ 𝒥' : TwoPlaceTorsionDatum p D₁' H₁' D₂' H₂' A₁ A₂, 𝒥'.Laws M r₁ r₂ :=
  CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching M₁ M₂ 𝒥 M r₁ r₂ h𝒥

end S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching
end P2MW
export P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching (solution)
