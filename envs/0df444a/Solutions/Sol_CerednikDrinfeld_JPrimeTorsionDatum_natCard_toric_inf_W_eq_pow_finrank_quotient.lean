-- Prove2me | solution 1 for CerednikDrinfeld.JPrimeTorsionDatum.natCard_toric_inf_W_eq_pow_finrank_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8c342cc1-28d8-5288-a15b-3251d37ae374

import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient

set_option autoImplicit false
open CerednikDrinfeld ModularCurve

namespace K1

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem law_all (Dm : JPrimeTorsionDatum p E V A)
    (htor : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (hlaw : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric) (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ)
    {Y : Type} [AddCommGroup Y] [Module HeckeAlg Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D))
    (hY : ∀ (ℓ : Nat.Primes) (m : Y), eY (heckeGen ℓ • m) = heckeKernelMap Dm.H ℓ (eY m)) :
    ∀ (x : HeckeAlg) (t : ↥Dm.toric) (m : Y),
      Dm.toricEquiv ⟨Dm.hecke x t, htor x t t.2⟩ (eY m) = Dm.toricEquiv t (eY (x • m)) := by
  intro x
  induction x using MvPolynomial.induction_on with
  | C a =>
    intro t m
    have h1 : (⟨Dm.hecke (MvPolynomial.C a) t, htor _ _ t.2⟩ : ↥Dm.toric) = a • t := by
      apply Subtype.ext
      change Dm.hecke (MvPolynomial.C a) (t : Dm.T) = ((a • t : ↥Dm.toric) : Dm.T)
      rw [eq_intCast MvPolynomial.C a, map_intCast, Module.End.intCast_apply, AddSubgroup.coe_zsmul]
    rw [h1, map_zsmul, LinearMap.smul_apply, eq_intCast MvPolynomial.C a, Int.cast_smul_eq_zsmul, map_zsmul,
      map_zsmul]
  | add x y hx hy =>
    intro t m
    have h1 : (⟨Dm.hecke (x + y) t, htor _ _ t.2⟩ : ↥Dm.toric) =
        ⟨Dm.hecke x t, htor _ _ t.2⟩ + ⟨Dm.hecke y t, htor _ _ t.2⟩ := by
      apply Subtype.ext
      change Dm.hecke (x + y) (t : Dm.T) = Dm.hecke x (t : Dm.T) + Dm.hecke y (t : Dm.T)
      rw [map_add, LinearMap.add_apply]
    rw [h1, map_add, LinearMap.add_apply, hx, hy, add_smul, map_add, map_add]
  | mul_X x ℓ hx =>
    intro t m
    have hXt : Dm.hecke (MvPolynomial.X ℓ) (t : Dm.T) ∈ Dm.toric := htor _ _ t.2
    have h1 : (⟨Dm.hecke (x * MvPolynomial.X ℓ) t, htor _ _ t.2⟩ : ↥Dm.toric) =
        ⟨Dm.hecke x (Dm.hecke (MvPolynomial.X ℓ) (t : Dm.T)), htor _ _ hXt⟩ := by
      apply Subtype.ext
      change Dm.hecke (x * MvPolynomial.X ℓ) (t : Dm.T) = _
      rw [map_mul, Module.End.mul_apply]
    have h2 : Dm.toricEquiv ⟨Dm.hecke (MvPolynomial.X ℓ) (t : Dm.T), hXt⟩ =
        (Dm.toricEquiv ⟨(t : Dm.T), t.2⟩) ∘ₗ heckeKernelMap Dm.H ℓ := hlaw ℓ t t.2 hXt
    rw [h1, hx ⟨_, hXt⟩ m, h2, LinearMap.comp_apply, ← hY, Subtype.coe_eta, ← mul_smul, mul_comm]
    rfl

theorem mem_W_iff (Dm : JPrimeTorsionDatum p E V A) (𝔪 : Ideal HeckeAlg) (t : Dm.T) :
    t ∈ Dm.W 𝔪 ↔ ∀ x ∈ 𝔪, Dm.hecke x t = 0 := by
  simp only [JPrimeTorsionDatum.W, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]

noncomputable def form (Dm : JPrimeTorsionDatum p E V A) {Y : Type} [AddCommGroup Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D)) (t : ↥Dm.toric) : Y →+ ZMod p :=
  (Dm.toricEquiv t).toAddMonoidHom.comp eY.toAddMonoidHom

theorem form_apply (Dm : JPrimeTorsionDatum p E V A) {Y : Type} [AddCommGroup Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D)) (t : ↥Dm.toric) (m : Y) :
    form Dm eY t m = Dm.toricEquiv t (eY m) := rfl

theorem form_injective (Dm : JPrimeTorsionDatum p E V A) {Y : Type} [AddCommGroup Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D)) : Function.Injective (form Dm eY) := by
  intro t t' h
  apply Dm.toricEquiv.injective
  ext z
  have := congrArg (fun f : Y →+ ZMod p => f (eY.symm z)) h
  simpa [form_apply] using this

section StepB

variable (Dm : JPrimeTorsionDatum p E V A)
    (htor : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (hlaw : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric) (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ)
    (𝔪 : Ideal HeckeAlg)
    {Y : Type} [AddCommGroup Y] [Module HeckeAlg Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D))
    (hY : ∀ (ℓ : Nat.Primes) (m : Y), eY (heckeGen ℓ • m) = heckeKernelMap Dm.H ℓ (eY m))

noncomputable def MY : AddSubgroup Y := (𝔪 • (⊤ : Submodule HeckeAlg Y)).toAddSubgroup

theorem mem_MY {y : Y} : y ∈ MY 𝔪 (Y := Y) ↔ y ∈ (𝔪 • (⊤ : Submodule HeckeAlg Y)) := Iff.rfl

include htor hlaw hY in

theorem form_vanishes (t : ↥Dm.toric) (hW : (t : Dm.T) ∈ Dm.W 𝔪) :
    ∀ y ∈ MY 𝔪 (Y := Y), form Dm eY t y = 0 := by
  intro y hy
  rw [mem_MY] at hy
  refine Submodule.smul_induction_on hy (fun x hx n _ => ?_) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
  rw [form_apply, ← law_all Dm htor hlaw eY hY x t n]
  have h0 : (⟨Dm.hecke x t, htor x t t.2⟩ : ↥Dm.toric) = 0 :=
    Subtype.ext (((mem_W_iff Dm 𝔪 t).1 hW) x hx)
  rw [h0, map_zero, LinearMap.zero_apply]

noncomputable def toHom (s : ↥(Dm.toric ⊓ Dm.W 𝔪)) : Y ⧸ MY 𝔪 (Y := Y) →+ ZMod p :=
  QuotientAddGroup.lift (MY 𝔪) (form Dm eY ⟨s.1, s.2.1⟩)
    (fun y hy => form_vanishes Dm htor hlaw 𝔪 eY hY ⟨s.1, s.2.1⟩ s.2.2 y hy)

theorem toHom_mk (s : ↥(Dm.toric ⊓ Dm.W 𝔪)) (y : Y) :
    toHom Dm htor hlaw 𝔪 eY hY s (QuotientAddGroup.mk y) = form Dm eY ⟨s.1, s.2.1⟩ y := rfl

include htor hlaw hY in
theorem toHom_injective : Function.Injective (toHom Dm htor hlaw 𝔪 eY hY) := by
  intro s s' h
  apply Subtype.ext
  have hf : form Dm eY ⟨s.1, s.2.1⟩ = form Dm eY ⟨s'.1, s'.2.1⟩ := by
    ext y
    rw [← toHom_mk Dm htor hlaw 𝔪 eY hY s y, ← toHom_mk Dm htor hlaw 𝔪 eY hY s' y, h]
  exact congrArg (fun u : ↥Dm.toric => (u : Dm.T)) (form_injective Dm eY hf)

include htor hlaw hY in
theorem toHom_surjective : Function.Surjective (toHom Dm htor hlaw 𝔪 eY hY) := by
  intro g

  let f : ↥(ribbonKernel Dm.D) →ₗ[ℤ] ZMod p :=
    ((g.comp (QuotientAddGroup.mk' (MY 𝔪))).comp eY.symm.toAddMonoidHom).toIntLinearMap
  have hf : ∀ y : Y, f (eY y) = g (QuotientAddGroup.mk y) := by
    intro y
    simp [f]
  let t : ↥Dm.toric := Dm.toricEquiv.symm f
  have ht : Dm.toricEquiv t = f := Dm.toricEquiv.apply_symm_apply f
  have hW : (t : Dm.T) ∈ Dm.W 𝔪 := by
    rw [mem_W_iff]
    intro x hx
    have h0 : (⟨Dm.hecke x t, htor x t t.2⟩ : ↥Dm.toric) = 0 := by
      apply Dm.toricEquiv.injective
      rw [map_zero]
      ext z
      rw [LinearMap.zero_apply, ← eY.apply_symm_apply z, law_all Dm htor hlaw eY hY x t, ht, hf]
      have hz : (QuotientAddGroup.mk (x • eY.symm z) : Y ⧸ MY 𝔪 (Y := Y)) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).2 ((mem_MY 𝔪).2 (Submodule.smul_mem_smul hx Submodule.mem_top))
      rw [hz, map_zero]
    exact congrArg Subtype.val h0
  refine ⟨⟨t, t.2, hW⟩, AddMonoidHom.ext fun y => ?_⟩
  induction y using QuotientAddGroup.induction_on with
  | H y => rw [toHom_mk, form_apply, ht, hf]

noncomputable def equivHom : ↥(Dm.toric ⊓ Dm.W 𝔪) ≃ (Y ⧸ MY 𝔪 (Y := Y) →+ ZMod p) :=
  Equiv.ofBijective _ ⟨toHom_injective Dm htor hlaw 𝔪 eY hY, toHom_surjective Dm htor hlaw 𝔪 eY hY⟩

end StepB

section Count

def addMonoidHomEquivLinear (Q : Type) [AddCommGroup Q] [Module (ZMod p) Q] :
    (Q →+ ZMod p) ≃ (Q →ₗ[ZMod p] ZMod p) where
  toFun f := f.toZModLinearMap p
  invFun g := g.toAddMonoidHom
  left_inv f := by ext; rfl
  right_inv g := by ext; rfl

variable [Fact p.Prime]

theorem natCard_addMonoidHom_zmod (Q : Type) [AddCommGroup Q] (instQ : Module (ZMod p) Q)
    (hfin : Module.Finite (ZMod p) Q) :
    Nat.card (Q →+ ZMod p) = Nat.card Q := by
  rw [Nat.card_congr (addMonoidHomEquivLinear Q), Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q →ₗ[ZMod p] ZMod p),
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q)]
  congr 1
  exact Subspace.dual_finrank_eq

end Count

set_option maxHeartbeats 1600000 in
theorem main [Fact p.Prime] (Dm : JPrimeTorsionDatum p E V A)
    (htor : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (hlaw : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric) (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    {Y : Type} [AddCommGroup Y] [Module HeckeAlg Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D))
    (hY : ∀ (ℓ : Nat.Primes) (m : Y), eY (heckeGen ℓ • m) = heckeKernelMap Dm.H ℓ (eY m)) :
    Nat.card ↥(Dm.toric ⊓ Dm.W 𝔪) =
      Nat.card (HeckeAlg ⧸ 𝔪) ^ Module.finrank (HeckeAlg ⧸ 𝔪) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := by

  have e1 : ↥(Dm.toric ⊓ Dm.W 𝔪) ≃ (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y)) →+ ZMod p) :=
    equivHom Dm htor hlaw 𝔪 eY hY
  rw [Nat.card_congr e1]

  haveI : Module.Finite ℤ Y := Module.Finite.equiv eY.symm.toIntLinearEquiv
  haveI : Module.Finite ℤ (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := Module.Finite.quotient ℤ _

  have hpQ : ∀ q : Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y)), p • q = 0 := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ y =>
      rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        ← Nat.cast_smul_eq_nsmul HeckeAlg p y]
      exact Submodule.smul_mem_smul hp Submodule.mem_top
  letI instZ : Module (ZMod p) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := AddCommGroup.zmodModule hpQ
  haveI instF : Module.Finite (ZMod p) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod p) _
  haveI : Finite (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) :=
    @Module.finite_of_finite (ZMod p) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) _ _ instZ _ instF

  have h3 : Nat.card ((Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) →+ ZMod p) =
      Nat.card (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := natCard_addMonoidHom_zmod (p := p) _ instZ instF
  rw [h3]

  letI := Ideal.Quotient.field 𝔪
  haveI : Module.Finite (HeckeAlg ⧸ 𝔪) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

end K1

theorem solution
    {p : ℕ} [Fact p.Prime] {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    (Dm : JPrimeTorsionDatum p E V A)
    (htor : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (hlaw : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric) (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    {Y : Type} [AddCommGroup Y] [Module HeckeAlg Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D))
    (hY : ∀ (ℓ : Nat.Primes) (m : Y), eY (heckeGen ℓ • m) = heckeKernelMap Dm.H ℓ (eY m)) :
    Nat.card ↥(Dm.toric ⊓ Dm.W 𝔪) =
      Nat.card (HeckeAlg ⧸ 𝔪) ^ Module.finrank (HeckeAlg ⧸ 𝔪) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) :=
  K1.main Dm htor hlaw 𝔪 hp eY hY

end S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient (solution)
