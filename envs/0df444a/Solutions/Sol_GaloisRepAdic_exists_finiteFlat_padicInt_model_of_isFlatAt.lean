-- Prove2me | solution 1 for GaloisRepAdic.exists_finiteFlat_padicInt_model_of_isFlatAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f22482c5-fe12-5760-b229-1c45f1bce538

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt

set_option autoImplicit false

namespace E87C0

open scoped PadicInt

theorem norm_cast_le_one (p : ℕ) [Fact p.Prime] (r : GaloisRep.ratLocalizedAt p) :
    ‖(algebraMap ℚ ℚ_[p] (r : ℚ))‖ ≤ 1 := by
  obtain ⟨r, hr⟩ := r
  have hden : Nat.Coprime r.den p := hr
  change ‖(algebraMap ℚ ℚ_[p] r)‖ ≤ 1
  have hr' : (algebraMap ℚ ℚ_[p] r) = ((r.num : ℚ_[p]) / (r.den : ℚ_[p])) := by
    rw [eq_ratCast, Rat.cast_def]
  rw [hr', norm_div]
  have hd : ‖(r.den : ℚ_[p])‖ = 1 := (Padic.norm_natCast_eq_one_iff).mpr (Nat.Coprime.symm hden)
  rw [hd, div_one]
  exact Padic.norm_int_le_one r.num

noncomputable def toPadicInt (p : ℕ) [Fact p.Prime] : GaloisRep.ratLocalizedAt p →+* ℤ_[p] where
  toFun r := ⟨algebraMap ℚ ℚ_[p] (r : ℚ), norm_cast_le_one p r⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

@[scoped simp] theorem coe_toPadicInt (p : ℕ) [Fact p.Prime] (r : GaloisRep.ratLocalizedAt p) :
    ((toPadicInt p r : ℤ_[p]) : ℚ_[p]) = algebraMap ℚ ℚ_[p] (r : ℚ) := rfl

theorem exists_padicEmbedding_eq_of_isAlgebraic (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p}
    (hx : IsAlgebraic ℚ x) : ∃ y : AlgebraicClosure ℚ, padicEmbedding p y = x := by
  have hint : IsIntegral ℚ x := hx.isIntegral
  set f : Polynomial ℚ := minpoly ℚ x with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint

  set g : Polynomial (AlgebraicClosure ℚ) := f.map (algebraMap ℚ (AlgebraicClosure ℚ)) with hg
  have hsplit : g.Splits := IsAlgClosed.splits g
  have hroots := hsplit.roots_map (padicEmbedding p).toRingHom
  have hgmap : g.map (padicEmbedding p).toRingHom = f.map (algebraMap ℚ (PadicAlgCl p)) := by
    rw [hg, Polynomial.map_map]
    congr 1
    ext q
    simp
  have hmem : x ∈ (g.map (padicEmbedding p).toRingHom).roots := by
    rw [hgmap, Polynomial.mem_roots (Polynomial.map_ne_zero hf0), Polynomial.IsRoot.def,
      Polynomial.eval_map, ← Polynomial.aeval_def, hf, minpoly.aeval]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

theorem exists_padicEmbedding_comp_eq (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra ℚ R]
    [Algebra.IsAlgebraic ℚ R] (φ : R →ₐ[ℚ] PadicAlgCl p) :
    ∃ ψ : R →ₐ[ℚ] AlgebraicClosure ℚ, (padicEmbedding p).comp ψ = φ := by

  have key : ∀ r : R, ∃ y : AlgebraicClosure ℚ, padicEmbedding p y = φ r := fun r =>
    exists_padicEmbedding_eq_of_isAlgebraic p ((Algebra.IsAlgebraic.isAlgebraic r).algHom φ)
  choose ψ₀ hψ₀ using key
  have hinj := (padicEmbedding p).injective
  refine ⟨{ toFun := ψ₀, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
            commutes' := ?_ }, ?_⟩
  · apply hinj; show padicEmbedding p _ = padicEmbedding p _; rw [hψ₀, map_one, map_one]
  · intro a b; apply hinj; show padicEmbedding p _ = padicEmbedding p _
    rw [hψ₀, map_mul, map_mul, hψ₀, hψ₀]
  · apply hinj; show padicEmbedding p _ = padicEmbedding p _; rw [hψ₀, map_zero, map_zero]
  · intro a b; apply hinj; show padicEmbedding p _ = padicEmbedding p _
    rw [hψ₀, map_add, map_add, hψ₀, hψ₀]
  · intro q; apply hinj; show padicEmbedding p _ = padicEmbedding p _
    rw [hψ₀, AlgHom.commutes, AlgHom.commutes]
  · ext r; exact hψ₀ r

open scoped TensorProduct

section points
variable (p : ℕ) [Fact p.Prime]

local notation "Qpb" => PadicAlgCl p

noncomputable scoped instance algZp : Algebra (GaloisRep.ratLocalizedAt p) ℤ_[p] := (toPadicInt p).toAlgebra

theorem algebraMap_R_Qpb (r : GaloisRep.ratLocalizedAt p) :
    algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r
      = algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (r : ℚ)) := by
  have h1 : algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r = algebraMap ℚ (PadicAlgCl p) (r : ℚ) := rfl
  rw [h1, eq_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← eq_ratCast (algebraMap ℚ ℚ_[p])]

theorem algebraMap_toPadicInt (r : GaloisRep.ratLocalizedAt p) :
    algebraMap ℤ_[p] (PadicAlgCl p) (toPadicInt p r) = algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r := by
  rw [algebraMap_R_Qpb]; rfl

scoped instance tower : @IsScalarTower (GaloisRep.ratLocalizedAt p) ℤ_[p] (PadicAlgCl p)
    Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  constructor
  intro r z x
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
    show (algebraMap (GaloisRep.ratLocalizedAt p) ℤ_[p]) r = toPadicInt p r from rfl, algebraMap_toPadicInt]

theorem padicEmbedding_algebraMap (r : GaloisRep.ratLocalizedAt p) :
    padicEmbedding p (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r)
      = algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r := by
  have h1 : algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r
      = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl
  have h2 : algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r = algebraMap ℚ (PadicAlgCl p) (r : ℚ) := rfl
  rw [h1, h2, AlgHom.commutes]

variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
  [Module.Finite (GaloisRep.ratLocalizedAt p) H]

noncomputable def ptsBC :
    ((ℤ_[p] ⊗[GaloisRep.ratLocalizedAt p] H) →ₐ[ℤ_[p]] PadicAlgCl p) ≃
      (H →ₐ[GaloisRep.ratLocalizedAt p] PadicAlgCl p) :=
  { toFun := fun F => (F.restrictScalars (GaloisRep.ratLocalizedAt p)).comp Algebra.TensorProduct.includeRight
    invFun := fun g => Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] (PadicAlgCl p)) g (fun _ _ => Commute.all _ _)
    left_inv := fun F => by
      apply Algebra.TensorProduct.ext'
      intro a h
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
        Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply]
      rw [show a ⊗ₜ[GaloisRep.ratLocalizedAt p] h = (a ⊗ₜ 1) * (1 ⊗ₜ h) from by simp, map_mul]
      congr 1
      rw [show (a ⊗ₜ[GaloisRep.ratLocalizedAt p] (1 : H)) = algebraMap ℤ_[p] _ a from by
        simp [Algebra.TensorProduct.algebraMap_apply], AlgHom.commutes]
    right_inv := fun g => by
      ext h
      simp [Algebra.TensorProduct.lift_tmul] }

noncomputable def reprBC {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr (GaloisRep.ratLocalizedAt p) h ι𝓡) :
    Coalgebra.Repr ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[GaloisRep.ratLocalizedAt p] h) ι𝓡 where
  index := 𝓡.index
  left i := (1 : ℤ_[p]) ⊗ₜ 𝓡.left i
  right i := (1 : ℤ_[p]) ⊗ₜ 𝓡.right i
  eq := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq, TensorProduct.tmul_sum, map_sum]
    simp

theorem ptsBC_mul (F G : WithConv ((ℤ_[p] ⊗[GaloisRep.ratLocalizedAt p] H) →ₐ[ℤ_[p]] PadicAlgCl p)) :
    ptsBC p H (F * G).ofConv
      = (WithConv.toConv (ptsBC p H F.ofConv) * WithConv.toConv (ptsBC p H G.ofConv)).ofConv := by
  apply AlgHom.ext
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary (GaloisRep.ratLocalizedAt p) h

  have hR : (WithConv.toConv (ptsBC p H F.ofConv) * WithConv.toConv (ptsBC p H G.ofConv)).ofConv h
      = ∑ i ∈ 𝓡.index, ptsBC p H F.ofConv (𝓡.left i) * ptsBC p H G.ofConv (𝓡.right i) := by
    have key := AlgHom.toLinearMap_convMul (WithConv.toConv (ptsBC p H F.ofConv)) (WithConv.toConv (ptsBC p H G.ofConv))
    have := congrArg (fun L => (WithConv.ofConv L) h) key
    simpa [Coalgebra.Repr.convMul_apply 𝓡] using this

  have hL : (F * G).ofConv ((1 : ℤ_[p]) ⊗ₜ h)
      = ∑ i ∈ 𝓡.index, F.ofConv ((1 : ℤ_[p]) ⊗ₜ 𝓡.left i) * G.ofConv ((1 : ℤ_[p]) ⊗ₜ 𝓡.right i) := by
    have key := AlgHom.toLinearMap_convMul F G
    have := congrArg (fun L => (WithConv.ofConv L) ((1 : ℤ_[p]) ⊗ₜ[GaloisRep.ratLocalizedAt p] h)) key
    simp [Coalgebra.Repr.convMul_apply (reprBC p H 𝓡)] at this
    exact this
  show (F * G).ofConv (Algebra.TensorProduct.includeRight h) = _
  rw [Algebra.TensorProduct.includeRight_apply, hL, hR]
  rfl

end points

end E87C0
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.E87C0"

open Coalgebra

namespace E88C0

variable (p : ℕ) [Fact p.Prime]

local notation "K" => AlgebraicClosure ℚ
local notation "Q" => PadicAlgCl p
local notation "Rp" => GaloisRep.ratLocalizedAt p

noncomputable def embQ : K →ₐ[Rp] Q :=
  { (padicEmbedding p).toRingHom with
    commutes' := fun r => by
      change padicEmbedding p (((r : ℚ) : K)) = ((r : ℚ) : Q)
      exact map_ratCast (padicEmbedding p) (r : ℚ) }

theorem embQ_apply (x : K) : embQ p x = padicEmbedding p x := rfl

theorem embQ_injective : Function.Injective (embQ p) := (padicEmbedding p).injective

section pts

variable {p}
variable {H : Type} [CommRing H] [Algebra (GaloisRep.ratLocalizedAt p) H]
  [Module.Finite (GaloisRep.ratLocalizedAt p) H]

theorem exists_embQ_eq_apply (φ : H →ₐ[Rp] Q) (h : H) : ∃ y : K, embQ p y = φ h := by
  have hint : IsIntegral Rp h := Algebra.IsIntegral.isIntegral h
  obtain ⟨P, hPmonic, hPeval⟩ := hint
  have hP0 : P ≠ 0 := hPmonic.ne_zero

  have hroot : (P.map (algebraMap Rp Q)).IsRoot (φ h) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hPeval, map_zero]

  set g : Polynomial K := P.map (algebraMap Rp K) with hg
  have hsplit : g.Splits := IsAlgClosed.splits g
  have hroots := hsplit.roots_map (embQ p).toRingHom
  have hgmap : g.map (embQ p).toRingHom = P.map (algebraMap Rp Q) := by
    rw [hg, Polynomial.map_map]
    congr 1
    ext r
    exact (embQ p).commutes r
  have hmem : φ h ∈ (g.map (embQ p).toRingHom).roots := by
    rw [hgmap, Polynomial.mem_roots (Polynomial.map_monic_ne_zero hPmonic)]
    exact hroot
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

private noncomputable def _root_.E88C0.lift (φ : H →ₐ[Rp] Q) : H →ₐ[Rp] K where
  toFun h := (exists_embQ_eq_apply φ h).choose
  map_one' := embQ_injective p (by rw [(exists_embQ_eq_apply φ 1).choose_spec, map_one, map_one])
  map_mul' a b := embQ_injective p (by
    rw [(exists_embQ_eq_apply φ (a * b)).choose_spec, map_mul, map_mul,
      (exists_embQ_eq_apply φ a).choose_spec, (exists_embQ_eq_apply φ b).choose_spec])
  map_zero' := embQ_injective p (by rw [(exists_embQ_eq_apply φ 0).choose_spec, map_zero, map_zero])
  map_add' a b := embQ_injective p (by
    rw [(exists_embQ_eq_apply φ (a + b)).choose_spec, map_add, map_add,
      (exists_embQ_eq_apply φ a).choose_spec, (exists_embQ_eq_apply φ b).choose_spec])
  commutes' r := embQ_injective p (by
    rw [(exists_embQ_eq_apply φ (algebraMap Rp H r)).choose_spec, AlgHom.commutes, AlgHom.commutes])

p2m_export "E88C0" "lift"
theorem embQ_lift (φ : H →ₐ[Rp] Q) (h : H) : embQ p (lift φ h) = φ h :=
  (exists_embQ_eq_apply φ h).choose_spec

theorem embQ_comp_lift (φ : H →ₐ[Rp] Q) : (embQ p).comp (lift φ) = φ :=
  AlgHom.ext fun h => embQ_lift φ h

theorem lift_embQ_comp (ψ : H →ₐ[Rp] K) : lift ((embQ p).comp ψ) = ψ :=
  AlgHom.ext fun h => embQ_injective p (by rw [embQ_lift]; rfl)

noncomputable def ptsQbar : WithConv (H →ₐ[Rp] Q) ≃ WithConv (H →ₐ[Rp] K) where
  toFun F := WithConv.toConv (lift (WithConv.ofConv F))
  invFun f := WithConv.toConv ((embQ p).comp (WithConv.ofConv f))
  left_inv F := by simp [embQ_comp_lift]
  right_inv f := by simp [lift_embQ_comp]

theorem embQ_ptsQbar_apply (F : WithConv (H →ₐ[Rp] Q)) (h : H) : embQ p (ptsQbar F h) = F h :=
  embQ_lift _ h

theorem ptsQbar_symm_apply (f : WithConv (H →ₐ[Rp] K)) (h : H) : ptsQbar.symm f h = embQ p (f h) := rfl

theorem ptsQbar_apply_of_forall_eq (τ : Q ≃ₐ[ℚ_[p]] Q) (F G : WithConv (H →ₐ[Rp] Q))
    (hFG : ∀ h : H, G h = τ (F h)) (h : H) :
    ptsQbar G h = localGaloisToGlobal p τ (ptsQbar F h) := by
  apply embQ_injective p
  rw [embQ_ptsQbar_apply, hFG, embQ_apply, padicEmbedding_localGaloisToGlobal, ← embQ_apply,
    embQ_ptsQbar_apply]

end pts
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.E87C0"

section hopf

variable {p}
variable {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
  [Module.Finite (GaloisRep.ratLocalizedAt p) H]

theorem convMul_apply_repr {L : Type} [CommRing L] [Algebra Rp L] (f g : WithConv (H →ₐ[Rp] L))
    {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr Rp h ι𝓡) :
    (f * g) h = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  have := congrArg (fun (φ : WithConv (H →ₗ[Rp] L)) => (WithConv.ofConv φ) h)
    (AlgHom.toLinearMap_convMul f g)
  simp only [WithConv.ofConv_toConv, AlgHom.toLinearMap_apply] at this
  rw [this, Coalgebra.Repr.convMul_apply 𝓡]
  rfl

theorem ptsQbar_symm_mul (f g : WithConv (H →ₐ[Rp] K)) :
    (ptsQbar.symm (f * g) : WithConv (H →ₐ[Rp] Q)) = ptsQbar.symm f * ptsQbar.symm g := by
  classical
  have hext : ∀ (F G : WithConv (H →ₐ[Rp] Q)), (∀ h : H, F h = G h) → F = G := by
    intro F G hFG
    have : WithConv.ofConv F = WithConv.ofConv G := AlgHom.ext hFG
    simpa using congrArg WithConv.toConv this
  apply hext
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary Rp h
  rw [ptsQbar_symm_apply, convMul_apply_repr f g 𝓡, convMul_apply_repr _ _ 𝓡, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ptsQbar_symm_apply, ptsQbar_symm_apply]

theorem ptsQbar_mul (F G : WithConv (H →ₐ[Rp] Q)) :
    (ptsQbar (F * G) : WithConv (H →ₐ[Rp] K)) = ptsQbar F * ptsQbar G := by
  apply ptsQbar.symm.injective
  rw [Equiv.symm_apply_apply, ptsQbar_symm_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end hopf
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.E87C0"

section bot

variable {p}
variable {A : Type} [CommRing A] [IsLocalRing A]

theorem exists_model_of_isFlatAt [Finite A] (ρ : GaloisRepAdic A) (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra Rp H),
      Module.Finite Rp H ∧ Module.Flat Rp H ∧ Coalgebra.IsCocomm Rp H ∧
      ∃ e : WithConv (H →ₐ[Rp] K) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[Rp] K)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ σ (e f) := by
  obtain ⟨-, hflat⟩ := hρ
  haveI : Finite (A ⧸ (⊥ : Ideal A)) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨H, _, _, hfin, hfl, hcc, e, he_add, he_act⟩ := hflat ⊥ inferInstance
  have hbot : ((⊥ : Ideal A) • (⊤ : Submodule A ρ.V)) = ⊥ := Submodule.bot_smul _
  let q : (ρ.V ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A ρ.V))) ≃ₗ[A] ρ.V :=
    Submodule.quotEquivOfEqBot _ hbot
  refine ⟨H, inferInstance, inferInstance, hfin, hfl, hcc, e.trans q.toEquiv, ?_, ?_⟩
  · intro f g
    show q (e (f * g)) = q (e f) + q (e g)
    rw [he_add, map_add]
  · intro σ f g hfg
    show q (e g) = ρ.ρ σ (q (e f))
    rw [he_act σ f g hfg]
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (e f)
    rw [← hv]
    rfl

end bot
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.E87C0"

end E88C0
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.E87C0"

p2m_open_scoped "PadicInt TensorProduct Coalgebra.TensorProduct"

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime]
    (ρ : GaloisRepAdic A) (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ (localGaloisToGlobal p σ) (e f) := by
  classical
  obtain ⟨H0, i1, i2, hfin, hfl, hcc, e0, he0_add, he0_act⟩ :=
    E88C0.exists_model_of_isFlatAt (p := p) ρ hρ
  haveI := hfin; haveI := hfl; haveI := hcc
  let R := GaloisRep.ratLocalizedAt p
  let HB := ℤ_[p] ⊗[GaloisRep.ratLocalizedAt p] H0

  let E : WithConv (HB →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V :=
    (((Equiv.mk WithConv.ofConv WithConv.toConv (fun _ => rfl) (fun _ => rfl)).trans
      (E87C0.ptsBC p H0)).trans
      (Equiv.mk WithConv.toConv WithConv.ofConv (fun _ => rfl) (fun _ => rfl))).trans
      (E88C0.ptsQbar.trans e0)
  have hE : ∀ F : WithConv (HB →ₐ[ℤ_[p]] PadicAlgCl p),
      E F = e0 (E88C0.ptsQbar (WithConv.toConv (E87C0.ptsBC p H0 (WithConv.ofConv F)))) := fun _ => rfl
  refine ⟨HB, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, E, ?_, ?_⟩
  · intro F G
    rw [hE, hE, hE, E87C0.ptsBC_mul, WithConv.toConv_ofConv, E88C0.ptsQbar_mul, he0_add]
  · intro σ F G hFG
    rw [hE, hE]
    apply he0_act
    intro h
    apply E88C0.ptsQbar_apply_of_forall_eq σ
    intro h'
    show E87C0.ptsBC p H0 (WithConv.ofConv G) h' = σ (E87C0.ptsBC p H0 (WithConv.ofConv F) h')
    exact hFG _

end S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt
end P2MW
export P2MW.S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt (solution)
