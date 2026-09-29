-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9be7a6da-a85b-55ab-855f-014e4ad30e35

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_Module_Grassmannian_exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural
import Theorems.Thm_MvFormalGroup_map_mkQ_adicEval_sumElim_tmul_eq_zero_iff_mem_span_image_subst
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbFinAlg

open TensorProduct Module

section Alg
variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {k : ℕ}

def W (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  ∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule

noncomputable def mulA (B : Type) [CommRing B] [Algebra R B] (a : A) : B ⊗[R] A →ₗ[B] B ⊗[R] A :=
  LinearMap.mulLeft B ((1 : B) ⊗ₜ[R] a)

theorem mulA_apply (B : Type) [CommRing B] [Algebra R B] (a : A) (x : B ⊗[R] A) :
    mulA B a x = ((1 : B) ⊗ₜ[R] a) * x := rfl

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem W_map_iff (N : Grassmannian B (B ⊗[R] A) k) :
    W B' (Grassmannian.map φ N) ↔
      ∀ (a : A) (n : B ⊗[R] A), n ∈ N.toSubmodule →
        (letI : Algebra B B' := φ.toAlgebra
         ((1 : B') ⊗ₜ[B] (N.toSubmodule.mkQ (((1 : B) ⊗ₜ[R] a) * n)) :
            B' ⊗[B] ((B ⊗[R] A) ⧸ N.toSubmodule)) = 0) := by
  letI : Algebra B B' := φ.toAlgebra
  letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hmapN : (Grassmannian.map φ N).toSubmodule =
      LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule) := Grassmannian.map_toSubmodule φ N

  have hq' : ∀ x : B' ⊗[R] A, Grassmannian.baseChangeMkQ B' N.toSubmodule x =
      (N.toSubmodule.mkQ.baseChange B') ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) :=
    fun x => rfl

  have hT : ∀ (a : A) (x : B' ⊗[R] A),
      (AlgebraTensorModule.cancelBaseChange R B B' B' A).symm (((1 : B') ⊗ₜ[R] a) * x) =
        (mulA B a).baseChange B' ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' a₀ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, AlgebraTensorModule.cancelBaseChange_symm_tmul,
          AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul, mulA_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]

  have hex : Function.Exact (N.toSubmodule.subtype.baseChange B') (N.toSubmodule.mkQ.baseChange B') := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact B' (LinearMap.exact_subtype_mkQ N.toSubmodule) (Submodule.mkQ_surjective _)
  constructor
  · intro hW a n hn
    have hx : (AlgebraTensorModule.cancelBaseChange R B B' B' A) ((1 : B') ⊗ₜ[B] n) ∈
        (Grassmannian.map φ N).toSubmodule := by
      rw [hmapN, LinearMap.mem_ker, hq', LinearEquiv.symm_apply_apply]
      exact (hex _).mpr ⟨(1 : B') ⊗ₜ[B] ⟨n, hn⟩, by rw [LinearMap.baseChange_tmul]; rfl⟩
    have h2 := hW ((1 : B') ⊗ₜ[R] a) _ hx
    rw [hmapN, LinearMap.mem_ker, hq', hT, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, mulA_apply] at h2
    exact h2
  · intro h a' x hx
    rw [hmapN, LinearMap.mem_ker] at hx ⊢

    have hone : ∀ a : A, Grassmannian.baseChangeMkQ B' N.toSubmodule (((1 : B') ⊗ₜ[R] a) * x) = 0 := by
      intro a
      obtain ⟨z, hz⟩ := (hex _).mp (show (N.toSubmodule.mkQ.baseChange B')
        ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) = 0 by rw [← hq']; exact hx)
      rw [hq', hT, ← hz, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
        ← LinearMap.baseChange_comp]
      clear hz

      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]
      | tmul b' m =>
          rw [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
          have hm := h a m m.2
          rw [show (b' ⊗ₜ[B] N.toSubmodule.mkQ (mulA B a (m : B ⊗[R] A))) =
              b' • ((1 : B') ⊗ₜ[B] N.toSubmodule.mkQ (mulA B a (m : B ⊗[R] A))) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], mulA_apply, hm, smul_zero]
      | add u v hu hv => rw [map_add, hu, hv, add_zero]

    induction a' using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero]
    | tmul b' a =>
        have hs : (b' ⊗ₜ[R] a) * x = b' • ((((1 : B') ⊗ₜ[R] a) * x)) := by
          rw [← smul_mul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hs, map_smul, hone a, smul_zero]
    | add u v hu hv => rw [add_mul, map_add, hu, hv, add_zero]

theorem W_map (N : Grassmannian B (B ⊗[R] A) k) (hN : W B N) : W B' (Grassmannian.map φ N) := by
  rw [W_map_iff φ N]
  intro a n hn
  have h0 : N.toSubmodule.mkQ (((1 : B) ⊗ₜ[R] a) * n) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hN _ _ hn
  rw [h0, TensorProduct.tmul_zero]

end Alg

end HilbFinAlg

theorem comul_adicEval_of_comul_X {S A : Type} [CommRing S] [CommRing A] [Bialgebra S A]
    (x : Fin 2 → A) (hx : ∀ i, IsNilpotent (x i)) (F : MvFormalGroup 2 S)
    (hcomul : ∀ i, Coalgebra.comul (R := S) (x i) =
      MvFormalGroup.adicEval (⊥ : Ideal (A ⊗[S] A))
        (Sum.elim (fun j => x j ⊗ₜ[S] (1 : A)) (fun j => (1 : A) ⊗ₜ[S] x j)) (F.toPowerSeries i))
    (G : MvPowerSeries (Fin 2) S) :
    Coalgebra.comul (R := S) (MvFormalGroup.adicEval (⊥ : Ideal A) x G) =
      MvFormalGroup.adicEval (⊥ : Ideal (A ⊗[S] A))
        (Sum.elim (fun j => x j ⊗ₜ[S] (1 : A)) (fun j => (1 : A) ⊗ₜ[S] x j))
        (MvPowerSeries.subst F.toPowerSeries G) := by
  have hxrad : ∀ s : Fin 2, x s ∈ (⊥ : Ideal A).radical := fun s => by
    obtain ⟨n, hn⟩ := hx s
    exact Ideal.mem_radical_iff.mpr ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩
  have hpowL : ∀ (a : A) (n : ℕ), (a ⊗ₜ[S] (1 : A)) ^ n = (a ^ n) ⊗ₜ[S] (1 : A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ n ih => rw [pow_succ, ih, pow_succ, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hpowR : ∀ (a : A) (n : ℕ), ((1 : A) ⊗ₜ[S] a) ^ n = (1 : A) ⊗ₜ[S] (a ^ n) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ n ih => rw [pow_succ, ih, pow_succ, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hyrad : ∀ t : Fin 2 ⊕ Fin 2,
      Sum.elim (fun j => x j ⊗ₜ[S] (1 : A)) (fun j => (1 : A) ⊗ₜ[S] x j) t ∈ (⊥ : Ideal (A ⊗[S] A)).radical := by
    rintro (j | j)
    · obtain ⟨n, hn⟩ := hx j
      refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
      rw [Sum.elim_inl, hpowL, hn, TensorProduct.zero_tmul]; exact Ideal.zero_mem _
    · obtain ⟨n, hn⟩ := hx j
      refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
      rw [Sum.elim_inr, hpowR, hn, TensorProduct.tmul_zero]; exact Ideal.zero_mem _
  have h1 := @MvFormalGroup.map_adicEval S _ A _ (_) (A ⊗[S] A) _ (_) (Fin 2) _
    ⊥ _ ⊥ _ (Bialgebra.comulAlgHom S A) Submodule.fg_bot
    (fun s hs => by rw [(Submodule.mem_bot _).mp hs, map_zero]; exact Ideal.zero_mem _) x hxrad G
  have h1' : Coalgebra.comul (R := S) (MvFormalGroup.adicEval (⊥ : Ideal A) x G) =
      MvFormalGroup.adicEval (⊥ : Ideal (A ⊗[S] A)) (fun s => Coalgebra.comul (R := S) (x s)) G := h1
  rw [h1']
  have h2 : (fun s => Coalgebra.comul (R := S) (x s)) =
      fun i => MvFormalGroup.adicEval (⊥ : Ideal (A ⊗[S] A))
        (Sum.elim (fun j => x j ⊗ₜ[S] (1 : A)) (fun j => (1 : A) ⊗ₜ[S] x j)) (F.toPowerSeries i) := funext hcomul
  rw [h2]
  exact (MvFormalGroup.adicEval_subst _ hyrad F.hasSubst_toPowerSeries G).symm

namespace KernelHilb

variable (p : ℕ) [Fact p.Prime] {B₀ : Type} [CommRing B₀] (Φ : FormalODModule p B₀) (N h : ℕ)

def PZ (S : Type) [CommRing S] [Algebra B₀ S] (I : Ideal (MvPowerSeries (Fin 2) S)) : Prop :=
  Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I)

section Dict

variable {L : Type} [CommRing L] [HopfAlgebra B₀ L] [Module.Finite B₀ L]
variable (ρ : Zp2 p → (L →ₐc[B₀] L)) (ϖ : L →ₐc[B₀] L)
variable (θ : ∀ (S : Type) [CommRing S] [Algebra B₀ S], MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L)

def σfam : Option (Zp2 p) → (L →ₐ[B₀] L) :=
  fun o => o.elim (ϖ : L →ₐ[B₀] L) (fun a => (ρ a : L →ₐ[B₀] L))

def WH (S : Type) [CommRing S] [Algebra B₀ S] (M : Module.Grassmannian S (S ⊗[B₀] L) (p ^ h)) : Prop :=
  (∀ (a x : S ⊗[B₀] L), x ∈ M.toSubmodule → a * x ∈ M.toSubmodule) ∧
  (Ideal.span (M.toSubmodule : Set (S ⊗[B₀] L))).IsHopfIdeal' S ∧
  ∀ (i : Option (Zp2 p)) (x : S ⊗[B₀] L), x ∈ M.toSubmodule →
    (σfam p ρ ϖ i).toLinearMap.baseChange S x ∈ M.toSubmodule

structure ThetaSpec : Prop where
  surj : ∀ (S : Type) [CommRing S] [Algebra B₀ S], Function.Surjective (θ S)
  ker : ∀ (S : Type) [CommRing S] [Algebra B₀ S],
    RingHom.ker (θ S) = Ideal.span (Set.range ((Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N)))
  ev : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (G : MvPowerSeries (Fin 2) S),
    θ S G = MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B₀] L)) (fun i => θ S (MvPowerSeries.X i)) G
  nil : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (i : Fin 2), IsNilpotent (θ S (MvPowerSeries.X i))
  comul : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (i : Fin 2),
    Coalgebra.comul (R := S) (θ S (MvPowerSeries.X i)) =
      MvFormalGroup.adicEval (⊥ : Ideal ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)))
        (Sum.elim (fun j => θ S (MvPowerSeries.X j) ⊗ₜ[S] (1 : S ⊗[B₀] L))
          (fun j => (1 : S ⊗[B₀] L) ⊗ₜ[S] θ S (MvPowerSeries.X j)))
        ((Φ.map (algebraMap B₀ S)).F.toPowerSeries i)
  counit : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (G : MvPowerSeries (Fin 2) S),
    Coalgebra.counit (R := S) (θ S G) = MvPowerSeries.constantCoeff G
  rho : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (a : Zp2 p) (G : MvPowerSeries (Fin 2) S),
    Algebra.TensorProduct.map (AlgHom.id S S) (ρ a : L →ₐ[B₀] L) (θ S G) =
      θ S (MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) G)
  varpi : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (G : MvPowerSeries (Fin 2) S),
    Algebra.TensorProduct.map (AlgHom.id S S) (ϖ : L →ₐ[B₀] L) (θ S G) =
      θ S (MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi G)
  antipode : ∀ (S : Type) [CommRing S] [Algebra B₀ S] (G : MvPowerSeries (Fin 2) S),
    HopfAlgebra.antipode S (A := S ⊗[B₀] L) (θ S G) =
      θ S (MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act (-1)) G)
  nat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (f : S →ₐ[B₀] S')
    (G : MvPowerSeries (Fin 2) S),
    Algebra.TensorProduct.map f (AlgHom.id B₀ L) (θ S G) = θ S' (MvPowerSeries.map (f : S →+* S') G)

omit ρ ϖ in
theorem eq_of_image_eq' (S : Type) [CommRing S] [Algebra B₀ S]
    (I I' : Ideal (MvPowerSeries (Fin 2) S)) (hI : RingHom.ker (θ S) ≤ I) (hI' : RingHom.ker (θ S) ≤ I')
    (h : θ S '' (I : Set (MvPowerSeries (Fin 2) S)) = θ S '' (I' : Set (MvPowerSeries (Fin 2) S))) : I = I' := by
  have key : ∀ (J J' : Ideal (MvPowerSeries (Fin 2) S)), RingHom.ker (θ S) ≤ J' →
      θ S '' (J : Set _) ⊆ θ S '' (J' : Set _) → J ≤ J' := by
    intro J J' hJ' hsub x hx
    obtain ⟨y, hy, hxy⟩ := hsub ⟨x, hx, rfl⟩
    have : x - y ∈ RingHom.ker (θ S) := by rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have := J'.add_mem (hJ' this) hy
    rwa [sub_add_cancel] at this
  exact le_antisymm (key I I' hI' h.le) (key I' I hI h.ge)

omit ρ ϖ in
theorem ker_le_of_PZ'_aux (hker : ∀ (S : Type) [CommRing S] [Algebra B₀ S],
    RingHom.ker (θ S) = Ideal.span (Set.range ((Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N))))
    (S : Type) [CommRing S] [Algebra B₀ S]
    (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) : RingHom.ker (θ S) ≤ I := by
  rw [hker S, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact hI.2.2.2.2.2.2.2.2 j

theorem ker_le_of_PZ' (hθ : ThetaSpec p Φ N ρ ϖ θ) (S : Type) [CommRing S] [Algebra B₀ S]
    (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) : RingHom.ker (θ S) ≤ I :=
  ker_le_of_PZ'_aux p Φ N h θ hθ.ker S I hI

variable (S : Type) [CommRing S] [Algebra B₀ S]

noncomputable def imS (I : Ideal (MvPowerSeries (Fin 2) S)) : Submodule S (S ⊗[B₀] L) :=
  (I.map (θ S)).restrictScalars S

omit ρ ϖ in
theorem coe_imS (hsurj : Function.Surjective (θ S)) (I : Ideal (MvPowerSeries (Fin 2) S)) :
    (imS θ S I : Set (S ⊗[B₀] L)) = θ S '' (I : Set (MvPowerSeries (Fin 2) S)) := by
  haveI : RingHomSurjective ((θ S : MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L) : MvPowerSeries (Fin 2) S →+* S ⊗[B₀] L) :=
    ⟨hsurj⟩
  show ((I.map (θ S)).restrictScalars S : Set (S ⊗[B₀] L)) = _
  rw [Submodule.coe_restrictScalars,
    show I.map (θ S) = I.map ((θ S : MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L) : MvPowerSeries (Fin 2) S →+* S ⊗[B₀] L)
      from rfl,
    Ideal.map_eq_submodule_map, Submodule.map_coe]
  rfl

omit ρ ϖ in

theorem exists_quotEquiv (hsurj : Function.Surjective (θ S)) (I : Ideal (MvPowerSeries (Fin 2) S))
    (hI : RingHom.ker (θ S) ≤ I) :
    ∃ e : (MvPowerSeries (Fin 2) S ⧸ I) ≃ₗ[S] ((S ⊗[B₀] L) ⧸ imS θ S I),
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (θ S x) := by
  let q : (MvPowerSeries (Fin 2) S ⧸ I) →ₐ[S] ((S ⊗[B₀] L) ⧸ I.map (θ S)) :=
    Ideal.quotientMapₐ (I.map (θ S)) (θ S) Ideal.le_comap_map
  have hqs : Function.Surjective q := Ideal.quotientMap_surjective (H := Ideal.le_comap_map) hsurj
  have hqi : Function.Injective q := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      have hx' : θ S x ∈ I.map (θ S) :=
        (Ideal.Quotient.eq_zero_iff_mem (I := I.map (θ S)) (a := θ S x)).mp hx
      have := Ideal.mem_comap.mpr hx'
      rw [Ideal.comap_map_of_surjective _ hsurj] at this
      rcases Submodule.mem_sup.mp this with ⟨y, hy, z, hz, rfl⟩
      exact I.add_mem hy (hI (by simpa [Ideal.mem_comap] using hz))
  let e₁ := (AlgEquiv.ofBijective q ⟨hqi, hqs⟩).toLinearEquiv
  let e₂ := (Submodule.Quotient.restrictScalarsEquiv S (I.map (θ S))).symm
  refine ⟨e₁ ≪≫ₗ e₂, fun x => ?_⟩
  rfl

theorem rankAtStalk_of_PZ (hθ : ThetaSpec p Φ N ρ ϖ θ) (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I)
    [Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I)] [Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I)] :
    ∀ 𝔭 : PrimeSpectrum S, Module.rankAtStalk (R := S) (MvPowerSeries (Fin 2) S ⧸ I) 𝔭 = p ^ h := by
  intro 𝔭
  classical

  let κ : Type := 𝔭.asIdeal.ResidueField
  let g : S →+* κ := algebraMap S κ
  rw [Module.rankAtStalk_eq]
  change Module.finrank κ (κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ I)) = p ^ h

  have h1 : Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S)) = I := by
    rw [Subtype.range_coe, Ideal.span_eq]
  have hN : ∃ q : ℕ, ∀ s : Fin 2, (MvPowerSeries.X s : MvPowerSeries (Fin 2) S) ^ q ∈
      Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S)) := by
    obtain ⟨q, hq⟩ := hI.2.2.2.1
    exact ⟨q, fun s => h1.symm ▸ hq s⟩
  obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ)
    (Subtype.val : ↥I → MvPowerSeries (Fin 2) S) hN

  have h2 : Ideal.span (Set.range fun i : ↥I => MvPowerSeries.map (algebraMap S κ) (i : MvPowerSeries (Fin 2) S)) =
      I.map (MvPowerSeries.map g) := by
    show _ = Ideal.span (MvPowerSeries.map g '' (I : Set (MvPowerSeries (Fin 2) S)))
    rw [Set.image_eq_range]
    rfl
  let e₀ : (MvPowerSeries (Fin 2) S ⧸ I) ≃ₐ[S]
      (MvPowerSeries (Fin 2) S ⧸ Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S))) :=
    Ideal.quotientEquivAlgOfEq S h1.symm
  let e₁ : κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ I) ≃ₗ[κ]
      κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S))) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ) e₀.toLinearEquiv
  let e₂ : (MvPowerSeries (Fin 2) κ ⧸
      Ideal.span (Set.range fun i : ↥I => MvPowerSeries.map (algebraMap S κ) (i : MvPowerSeries (Fin 2) S))) ≃ₐ[κ]
      (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map g)) :=
    Ideal.quotientEquivAlgOfEq κ h2
  rw [(e₁ ≪≫ₗ e.toLinearEquiv ≪≫ₗ e₂.toLinearEquiv).finrank_eq]
  exact hI.2.2.1 κ g

noncomputable def toN (hθ : ThetaSpec p Φ N ρ ϖ θ) (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) :
    Module.Grassmannian S (S ⊗[B₀] L) (p ^ h) :=
  letI : Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) := hI.1
  letI : Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) := hI.2.1
  let e := (exists_quotEquiv θ S (hθ.surj S) I (ker_le_of_PZ' p Φ N h ρ ϖ θ hθ S I hI)).choose
  { toSubmodule := imS θ S I
    finite_quotient := Module.Finite.equiv e
    projective_quotient := Module.Projective.of_equiv e
    rankAtStalk_eq := fun 𝔭 => by
      rw [← Module.rankAtStalk_eq_of_equiv e]
      exact rankAtStalk_of_PZ p Φ N h ρ ϖ θ S hθ I hI 𝔭 }

omit ρ ϖ in

theorem baseChange_eq_tensorMap (S : Type) [CommRing S] [Algebra B₀ S] (g : L →ₐ[B₀] L) (z : S ⊗[B₀] L) :
    g.toLinearMap.baseChange S z = Algebra.TensorProduct.map (AlgHom.id S S) g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s l => rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit ρ ϖ θ in

theorem algHom_adicEval_bot {R A C : Type} [CommRing R] [CommRing A] [CommRing C] {_iA : Algebra R A} {_iC : Algebra R C}
    {σ : Type} [Finite σ] (φ : A →ₐ[R] C) (x : σ → A) (hx : ∀ s, IsNilpotent (x s)) (f : MvPowerSeries σ R) :
    φ (MvFormalGroup.adicEval (⊥ : Ideal A) x f) = MvFormalGroup.adicEval (⊥ : Ideal C) (fun s => φ (x s)) f := by
  have hxrad : ∀ s, x s ∈ (⊥ : Ideal A).radical := fun s => by
    obtain ⟨n, hn⟩ := hx s
    exact Ideal.mem_radical_iff.mpr ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩
  exact MvFormalGroup.map_adicEval (⊥ : Ideal A) (⊥ : Ideal C) φ Submodule.fg_bot
    (fun s hs => by rw [(Submodule.mem_bot _).mp hs, map_zero]; exact Ideal.zero_mem _) hxrad f

theorem comul_theta (hθ : ThetaSpec p Φ N ρ ϖ θ) (S : Type) [CommRing S] [Algebra B₀ S] (G : MvPowerSeries (Fin 2) S) :
    Coalgebra.comul (R := S) (θ S G) =
      MvFormalGroup.adicEval (⊥ : Ideal ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)))
        (Sum.elim (fun j => θ S (MvPowerSeries.X j) ⊗ₜ[S] (1 : S ⊗[B₀] L))
          (fun j => (1 : S ⊗[B₀] L) ⊗ₜ[S] θ S (MvPowerSeries.X j)))
        (MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries G) := by
  rw [hθ.ev S G]
  exact comul_adicEval_of_comul_X (fun i => θ S (MvPowerSeries.X i)) (hθ.nil S) (Φ.map (algebraMap B₀ S)).F (hθ.comul S) G

theorem toN_WH (hθ : ThetaSpec p Φ N ρ ϖ θ) (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) :
    WH p h ρ ϖ S (toN p Φ N h ρ ϖ θ S hθ I hI) := by
  obtain ⟨hfin, hproj, hrank, hnil, hunit, hmul, hact, hvarpi, hpN⟩ := hI
  have hker := ker_le_of_PZ' p Φ N h ρ ϖ θ hθ S I ⟨hfin, hproj, hrank, hnil, hunit, hmul, hact, hvarpi, hpN⟩
  haveI : RingHomSurjective ((θ S : MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L) : MvPowerSeries (Fin 2) S →+* S ⊗[B₀] L) :=
    ⟨hθ.surj S⟩

  have hmem : ∀ x : S ⊗[B₀] L, x ∈ (toN p Φ N h ρ ϖ θ S hθ I ⟨hfin, hproj, hrank, hnil, hunit, hmul, hact, hvarpi, hpN⟩).toSubmodule ↔
      ∃ G ∈ I, θ S G = x := fun x => by
    show x ∈ (I.map (θ S)).restrictScalars S ↔ _
    rw [Submodule.restrictScalars_mem, Ideal.mem_map_iff_of_surjective (θ S) (hθ.surj S)]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro a x hx
    obtain ⟨G, hG, rfl⟩ := (hmem x).mp hx
    obtain ⟨b, rfl⟩ := hθ.surj S a
    exact (hmem _).mpr ⟨b * G, I.mul_mem_left b hG, map_mul _ _ _⟩
  ·
    have hspan : Ideal.span ((toN p Φ N h ρ ϖ θ S hθ I ⟨hfin, hproj, hrank, hnil, hunit, hmul, hact, hvarpi, hpN⟩).toSubmodule :
        Set (S ⊗[B₀] L)) = I.map (θ S) := Ideal.span_eq (I.map (θ S))
    rw [hspan]
    have hmemJ : ∀ x : S ⊗[B₀] L, x ∈ I.map (θ S) ↔ ∃ G ∈ I, θ S G = x := fun x => by
      rw [Ideal.mem_map_iff_of_surjective (θ S) (hθ.surj S)]
    refine ⟨?_, ?_, ?_⟩
    ·
      intro x hx
      obtain ⟨G, hG, rfl⟩ := (hmemJ x).mp hx

      set J : Ideal (S ⊗[B₀] L) := I.map (θ S) with hJ
      let E : ((S ⊗[B₀] L) ⧸ J) ≃ₗ[S] ((S ⊗[B₀] L) ⧸ J.restrictScalars S) :=
        (Submodule.Quotient.restrictScalarsEquiv S J).symm
      have hE : ∀ y, E (Ideal.Quotient.mkₐ S J y) = (J.restrictScalars S).mkQ y := fun y => by
        show (Submodule.Quotient.restrictScalarsEquiv S J).symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
        rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
      have hcongr : ∀ z : (S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L),
          TensorProduct.congr E E (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ S J) (Ideal.Quotient.mkₐ S J) z) =
            TensorProduct.map (J.restrictScalars S).mkQ (J.restrictScalars S).mkQ z := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, LinearEquiv.map_zero, map_zero]
        | tmul u v => rw [Algebra.TensorProduct.map_tmul, TensorProduct.congr_tmul, hE, hE, TensorProduct.map_tmul]
        | add u v hu hv => rw [map_add, LinearEquiv.map_add, map_add, hu, hv]
      rw [← (TensorProduct.congr E E).map_eq_zero_iff, hcongr, comul_theta p Φ N ρ ϖ θ hθ S G]
      exact (MvFormalGroup.map_mkQ_adicEval_sumElim_tmul_eq_zero_iff_mem_span_image_subst (θ S) (hθ.surj S)
        (hθ.nil S) (hθ.ev S) I hker _).mpr (hmul G hG)
    ·
      intro x hx
      obtain ⟨G, hG, rfl⟩ := (hmemJ x).mp hx
      rw [hθ.counit S G]; exact hunit G hG
    ·
      intro x hx
      obtain ⟨G, hG, rfl⟩ := (hmemJ x).mp hx
      rw [hθ.antipode S G]
      exact (hmemJ _).mpr ⟨_, hact (-1) G hG, rfl⟩
  ·
    rintro (_ | a) x hx <;> obtain ⟨G, hG, rfl⟩ := (hmem x).mp hx
    · show (ϖ : L →ₐ[B₀] L).toLinearMap.baseChange S (θ S G) ∈ _
      rw [baseChange_eq_tensorMap, hθ.varpi S G]
      exact (hmem _).mpr ⟨_, hvarpi G hG, rfl⟩
    · show (ρ a : L →ₐ[B₀] L).toLinearMap.baseChange S (θ S G) ∈ _
      rw [baseChange_eq_tensorMap, hθ.rho S a G]
      exact (hmem _).mpr ⟨_, hact a G hG, rfl⟩

theorem exists_of_WH (hθ : ThetaSpec p Φ N ρ ϖ θ) (M : Module.Grassmannian S (S ⊗[B₀] L) (p ^ h))
    (hM : WH p h ρ ϖ S M) :
    ∃ (I : Ideal (MvPowerSeries (Fin 2) S)), PZ p Φ N h S I ∧
      (M.toSubmodule : Set (S ⊗[B₀] L)) = θ S '' (I : Set (MvPowerSeries (Fin 2) S)) := by
  classical
  obtain ⟨hMW, hMH, hMσ⟩ := hM

  let J : Ideal (S ⊗[B₀] L) :=
    { carrier := M.toSubmodule
      add_mem' := fun hx hy => M.toSubmodule.add_mem hx hy
      zero_mem' := M.toSubmodule.zero_mem
      smul_mem' := fun a x hx => hMW a x hx }
  have hmemJ : ∀ x : S ⊗[B₀] L, x ∈ J ↔ x ∈ M.toSubmodule := fun x => Iff.rfl
  have hspan : Ideal.span (M.toSubmodule : Set (S ⊗[B₀] L)) = J := Ideal.span_eq J
  have hH : J.IsHopfIdeal' S := by rw [← hspan]; exact hMH

  let I : Ideal (MvPowerSeries (Fin 2) S) := J.comap (θ S)
  have hmemI : ∀ G : MvPowerSeries (Fin 2) S, G ∈ I ↔ θ S G ∈ M.toSubmodule := fun G => Ideal.mem_comap
  have hker : RingHom.ker (θ S) ≤ I := by
    intro G hG
    rw [RingHom.mem_ker] at hG
    rw [hmemI, hG]
    exact M.toSubmodule.zero_mem
  have hIJ : I.map (θ S) = J := Ideal.map_comap_of_surjective (θ S) (hθ.surj S) J
  have himS : imS θ S I = M.toSubmodule := by
    ext x
    show x ∈ (I.map (θ S)).restrictScalars S ↔ x ∈ M.toSubmodule
    rw [Submodule.restrictScalars_mem, hIJ]
    exact hmemJ x
  have himage : (M.toSubmodule : Set (S ⊗[B₀] L)) = θ S '' (I : Set (MvPowerSeries (Fin 2) S)) := by
    rw [← himS]; exact coe_imS θ S (hθ.surj S) I

  obtain ⟨e0, -⟩ := exists_quotEquiv θ S (hθ.surj S) I hker
  let eQ : (MvPowerSeries (Fin 2) S ⧸ I) ≃ₗ[S] ((S ⊗[B₀] L) ⧸ M.toSubmodule) :=
    e0 ≪≫ₗ Submodule.quotEquivOfEq _ _ himS
  have hfinI : Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) := Module.Finite.equiv eQ.symm
  have hprojI : Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) := Module.Projective.of_equiv eQ.symm

  have hnilI : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I := by
    have hXI : ∀ i : Fin 2, ∃ n : ℕ, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ n ∈ I := by
      intro i
      obtain ⟨n, hn⟩ := hθ.nil S i
      exact ⟨n, hker (by rw [RingHom.mem_ker, map_pow, hn])⟩
    choose n hn using hXI
    exact ⟨n 0 + n 1, fun i => by
      fin_cases i
      · exact Ideal.pow_mem_of_pow_mem I (hn 0) (Nat.le_add_right _ _)
      · exact Ideal.pow_mem_of_pow_mem I (hn 1) (Nat.le_add_left _ _)⟩

  have hpNI : ∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I := by
    intro j
    apply hker
    rw [hθ.ker S]
    exact Ideal.subset_span ⟨j, rfl⟩
  refine ⟨I, ⟨hfinI, hprojI, ?_, hnilI, ?_, ?_, ?_, ?_, hpNI⟩, himage⟩
  ·
    intro κ _ f
    letI : Algebra S κ := f.toAlgebra
    haveI : Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) := hfinI
    haveI : Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) := hprojI

    have hbc : Module.finrank κ (κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ I)) = p ^ h := by
      have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := κ) (M := κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ I)))
        ⟨⊥, Ideal.isPrime_bot⟩
      rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv eQ, M.rankAtStalk_eq] at h1
      exact h1.symm

    have h1 : Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S)) = I := by
      rw [Subtype.range_coe, Ideal.span_eq]
    have hN : ∃ q : ℕ, ∀ s : Fin 2, (MvPowerSeries.X s : MvPowerSeries (Fin 2) S) ^ q ∈
        Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S)) := by
      obtain ⟨q, hq⟩ := hnilI
      exact ⟨q, fun s => h1.symm ▸ hq s⟩
    obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ)
      (Subtype.val : ↥I → MvPowerSeries (Fin 2) S) hN
    have h2 : Ideal.span (Set.range fun i : ↥I => MvPowerSeries.map (algebraMap S κ) (i : MvPowerSeries (Fin 2) S)) =
        I.map (MvPowerSeries.map f) := by
      show _ = Ideal.span (MvPowerSeries.map f '' (I : Set (MvPowerSeries (Fin 2) S)))
      rw [Set.image_eq_range]
      rfl
    let e₀ : (MvPowerSeries (Fin 2) S ⧸ I) ≃ₐ[S]
        (MvPowerSeries (Fin 2) S ⧸ Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S))) :=
      Ideal.quotientEquivAlgOfEq S h1.symm
    let e₁ : κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ I) ≃ₗ[κ]
        κ ⊗[S] (MvPowerSeries (Fin 2) S ⧸ Ideal.span (Set.range (Subtype.val : ↥I → MvPowerSeries (Fin 2) S))) :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ) e₀.toLinearEquiv
    let e₂ : (MvPowerSeries (Fin 2) κ ⧸
        Ideal.span (Set.range fun i : ↥I => MvPowerSeries.map (algebraMap S κ) (i : MvPowerSeries (Fin 2) S))) ≃ₐ[κ]
        (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) :=
      Ideal.quotientEquivAlgOfEq κ h2
    rw [← (e₁ ≪≫ₗ e.toLinearEquiv ≪≫ₗ e₂.toLinearEquiv).finrank_eq]
    exact hbc
  ·
    intro G hG
    rw [← hθ.counit S G]
    exact hH.counit_eq_zero (θ S G) (Ideal.mem_comap.mp hG)
  ·
    intro G hG
    have hGJ : θ S G ∈ J := Ideal.mem_comap.mp hG
    have key := MvFormalGroup.map_mkQ_adicEval_sumElim_tmul_eq_zero_iff_mem_span_image_subst (θ S) (hθ.surj S)
      (hθ.nil S) (hθ.ev S) I hker (MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries G)
    rw [hIJ] at key
    let E : ((S ⊗[B₀] L) ⧸ J) ≃ₗ[S] ((S ⊗[B₀] L) ⧸ J.restrictScalars S) :=
      (Submodule.Quotient.restrictScalarsEquiv S J).symm
    have hE : ∀ y, E (Ideal.Quotient.mkₐ S J y) = (J.restrictScalars S).mkQ y := fun y => by
      show (Submodule.Quotient.restrictScalarsEquiv S J).symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
      rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
    have hcongr : ∀ z : (S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L),
        TensorProduct.congr E E (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ S J) (Ideal.Quotient.mkₐ S J) z) =
          TensorProduct.map (J.restrictScalars S).mkQ (J.restrictScalars S).mkQ z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, LinearEquiv.map_zero, map_zero]
      | tmul u v => rw [Algebra.TensorProduct.map_tmul, TensorProduct.congr_tmul, hE, hE, TensorProduct.map_tmul]
      | add u v hu hv => rw [map_add, LinearEquiv.map_add, map_add, hu, hv]
    have hc := hH.map_mkₐ_comul_eq_zero (θ S G) hGJ
    rw [← (TensorProduct.congr E E).map_eq_zero_iff, hcongr, comul_theta p Φ N ρ ϖ θ hθ S G] at hc
    exact key.mp hc
  ·
    intro a G hG
    rw [hmemI] at hG ⊢
    rw [← hθ.rho S a G, ← baseChange_eq_tensorMap]
    exact hMσ (some a) (θ S G) hG
  ·
    intro G hG
    rw [hmemI] at hG ⊢
    rw [← hθ.varpi S G, ← baseChange_eq_tensorMap]
    exact hMσ none (θ S G) hG

theorem exists_equiv (hθ : ThetaSpec p Φ N ρ ϖ θ) (S : Type) [CommRing S] [Algebra B₀ S] :
    ∃ e : { I : Ideal (MvPowerSeries (Fin 2) S) // PZ p Φ N h S I } ≃
        { M : Module.Grassmannian S (S ⊗[B₀] L) (p ^ h) // WH p h ρ ϖ S M },
      ∀ I, ((e I).1.toSubmodule : Set (S ⊗[B₀] L)) = θ S '' (I.1 : Set (MvPowerSeries (Fin 2) S)) := by
  classical
  let fwd : { I : Ideal (MvPowerSeries (Fin 2) S) // PZ p Φ N h S I } →
      { M : Module.Grassmannian S (S ⊗[B₀] L) (p ^ h) // WH p h ρ ϖ S M } :=
    fun I => ⟨toN p Φ N h ρ ϖ θ S hθ I.1 I.2, toN_WH p Φ N h ρ ϖ θ S hθ I.1 I.2⟩
  have hfwd : ∀ I, ((fwd I).1.toSubmodule : Set (S ⊗[B₀] L)) = θ S '' (I.1 : Set _) :=
    fun I => coe_imS θ S (hθ.surj S) I.1
  have hinj : Function.Injective fwd := by
    intro I I' hII'
    apply Subtype.ext
    exact eq_of_image_eq' θ S I.1 I'.1 (ker_le_of_PZ' p Φ N h ρ ϖ θ hθ S I.1 I.2)
      (ker_le_of_PZ' p Φ N h ρ ϖ θ hθ S I'.1 I'.2) ((hfwd I).symm.trans ((congrArg (fun M => ((M.1.toSubmodule : Set (S ⊗[B₀] L)))) hII').trans (hfwd I')))
  have hsurj : Function.Surjective fwd := by
    intro M
    obtain ⟨I, hI, hM⟩ := exists_of_WH p Φ N h ρ ϖ θ S hθ M.1 M.2
    refine ⟨⟨I, hI⟩, Subtype.ext (Module.Grassmannian.ext (SetLike.coe_injective ((hfwd ⟨I, hI⟩).trans hM.symm)))⟩
  exact ⟨Equiv.ofBijective fwd ⟨hinj, hsurj⟩, fun I => hfwd I⟩

end Dict

end KernelHilb

namespace KernelHilb

section Asm

open TensorProduct

variable (p : ℕ) [Fact p.Prime] {B₀ : Type} [CommRing B₀] (Φ : FormalODModule p B₀) (N h : ℕ)
variable {L : Type} [CommRing L] [HopfAlgebra B₀ L] [Module.Finite B₀ L]
variable (ρ : Zp2 p → (L →ₐc[B₀] L)) (ϖ : L →ₐc[B₀] L)
variable (θ : ∀ (S : Type) [CommRing S] [Algebra B₀ S], MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L)

theorem ker_le_of_PZ (hθ : ThetaSpec p Φ N ρ ϖ θ) (S : Type) [CommRing S] [Algebra B₀ S]
    (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) : RingHom.ker (θ S) ≤ I := by
  rw [hθ.ker S, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact hI.2.2.2.2.2.2.2.2 j

theorem eq_of_image_eq (S : Type) [CommRing S] [Algebra B₀ S]
    (I I' : Ideal (MvPowerSeries (Fin 2) S)) (hI : RingHom.ker (θ S) ≤ I) (hI' : RingHom.ker (θ S) ≤ I')
    (h : θ S '' (I : Set (MvPowerSeries (Fin 2) S)) = θ S '' (I' : Set (MvPowerSeries (Fin 2) S))) : I = I' := by
  have key : ∀ (J J' : Ideal (MvPowerSeries (Fin 2) S)), RingHom.ker (θ S) ≤ J' →
      θ S '' (J : Set _) ⊆ θ S '' (J' : Set _) → J ≤ J' := by
    intro J J' hJ' hsub x hx
    obtain ⟨y, hy, hxy⟩ := hsub ⟨x, hx, rfl⟩
    have : x - y ∈ RingHom.ker (θ S) := by rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have := J'.add_mem (hJ' this) hy
    rwa [sub_add_cancel] at this
  exact le_antisymm (key I I' hI' h.le) (key I' I hI h.ge)

theorem ker_le_map (hθ : ThetaSpec p Φ N ρ ϖ θ) (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S']
    (f : S →ₐ[B₀] S') (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) :
    RingHom.ker (θ S') ≤ I.map (MvPowerSeries.map (f : S →+* S')) := by
  rw [hθ.ker S', Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have hj := Ideal.mem_map_of_mem (MvPowerSeries.map (f : S →+* S')) (hI.2.2.2.2.2.2.2.2 j)
  refine (congrArg (· ∈ I.map (MvPowerSeries.map (f : S →+* S'))) ?_).mpr hj
  show MvPowerSeries.map (algebraMap B₀ S') (Φ.act ((p : Zp2 p) ^ N) j) =
    MvPowerSeries.map (f : S →+* S') (MvPowerSeries.map (algebraMap B₀ S) (Φ.act ((p : Zp2 p) ^ N) j))
  ext n
  simp only [MvPowerSeries.coeff_map]
  exact (f.commutes _).symm

theorem map_compat (hθ : ThetaSpec p Φ N ρ ϖ θ) (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S']
    (f : S →ₐ[B₀] S') (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I)
    (M : Module.Grassmannian S (S ⊗[B₀] L) (p ^ h))
    (hM : (M.toSubmodule : Set (S ⊗[B₀] L)) = θ S '' (I : Set (MvPowerSeries (Fin 2) S))) :
    ((Module.Grassmannian.map f M).toSubmodule : Set (S' ⊗[B₀] L)) =
      θ S' '' (I.map (MvPowerSeries.map (f : S →+* S')) : Set (MvPowerSeries (Fin 2) S')) := by
  classical
  letI : Algebra S S' := f.toAlgebra
  letI : IsScalarTower B₀ S S' := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm

  set F : S ⊗[B₀] L →ₐ[B₀] S' ⊗[B₀] L := Algebra.TensorProduct.map f (AlgHom.id B₀ L) with hF
  have hmapN : (Module.Grassmannian.map f M).toSubmodule =
      LinearMap.ker (Module.Grassmannian.baseChangeMkQ S' M.toSubmodule) := Module.Grassmannian.map_toSubmodule f M
  have hq' : ∀ x : S' ⊗[B₀] L, Module.Grassmannian.baseChangeMkQ S' M.toSubmodule x =
      (M.toSubmodule.mkQ.baseChange S') ((AlgebraTensorModule.cancelBaseChange B₀ S S' S' L).symm x) :=
    fun x => rfl
  have hex : Function.Exact (M.toSubmodule.subtype.baseChange S') (M.toSubmodule.mkQ.baseChange S') := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact S' (LinearMap.exact_subtype_mkQ M.toSubmodule) (Submodule.mkQ_surjective _)

  have hFe : ∀ m : S ⊗[B₀] L,
      (AlgebraTensorModule.cancelBaseChange B₀ S S' S' L).symm (F m) = (1 : S') ⊗ₜ[S] m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
        rw [hF, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
          show (s ⊗ₜ[B₀] l : S ⊗[B₀] L) = s • ((1 : S) ⊗ₜ[B₀] l) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]

  have hN' : (Module.Grassmannian.map f M).toSubmodule = Submodule.span S' (F '' (M.toSubmodule : Set (S ⊗[B₀] L))) := by
    apply le_antisymm
    · intro x hx
      rw [hmapN, LinearMap.mem_ker, hq'] at hx
      obtain ⟨z, hz⟩ := (hex _).mp hx
      have hx' : x = AlgebraTensorModule.cancelBaseChange B₀ S S' S' L ((M.toSubmodule.subtype.baseChange S') z) := by
        rw [hz, LinearEquiv.apply_symm_apply]
      rw [hx']
      clear hx hz hx'
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s' m =>
          rw [LinearMap.baseChange_tmul, Submodule.subtype_apply,
            show (s' ⊗ₜ[S] (m : S ⊗[B₀] L)) = s' • ((1 : S') ⊗ₜ[S] (m : S ⊗[B₀] L)) by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
            map_smul, ← hFe, LinearEquiv.apply_symm_apply]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, m.2, rfl⟩)
      | add u v hu hv => rw [map_add, map_add]; exact Submodule.add_mem _ hu hv
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      show F m ∈ (Module.Grassmannian.map f M).toSubmodule
      rw [hmapN, LinearMap.mem_ker, hq', hFe]
      exact (hex _).mpr ⟨(1 : S') ⊗ₜ[S] ⟨m, hm⟩, by rw [LinearMap.baseChange_tmul]; rfl⟩

  have hFM : F '' (M.toSubmodule : Set (S ⊗[B₀] L)) =
      θ S' '' (MvPowerSeries.map (f : S →+* S') '' (I : Set (MvPowerSeries (Fin 2) S))) := by
    rw [hM, Set.image_image, Set.image_image]
    refine Set.image_congr fun G _ => ?_
    rw [hF]; exact hθ.nat S S' f G

  have hMW : HilbFinAlg.W S M := by
    intro a x hx
    have hx' : x ∈ (M.toSubmodule : Set (S ⊗[B₀] L)) := hx
    rw [hM] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    obtain ⟨b, rfl⟩ := hθ.surj S a
    show θ S b * θ S y ∈ M.toSubmodule
    have : θ S (b * y) ∈ (M.toSubmodule : Set (S ⊗[B₀] L)) := by rw [hM]; exact ⟨b * y, I.mul_mem_left b hy, rfl⟩
    rwa [map_mul] at this
  have hW' := HilbFinAlg.W_map f M hMW

  set g : MvPowerSeries (Fin 2) S →+* MvPowerSeries (Fin 2) S' := MvPowerSeries.map (f : S →+* S') with hg
  haveI : RingHomSurjective ((θ S' : MvPowerSeries (Fin 2) S' →ₐ[S'] S' ⊗[B₀] L) : MvPowerSeries (Fin 2) S' →+* S' ⊗[B₀] L) :=
    ⟨hθ.surj S'⟩
  have e1 : θ S' '' (I.map g : Set (MvPowerSeries (Fin 2) S')) =
      (Ideal.map ((θ S' : MvPowerSeries (Fin 2) S' →ₐ[S'] S' ⊗[B₀] L) : MvPowerSeries (Fin 2) S' →+* S' ⊗[B₀] L)
        (I.map g) : Set (S' ⊗[B₀] L)) := by
    rw [Ideal.map_eq_submodule_map ((θ S' : MvPowerSeries (Fin 2) S' →ₐ[S'] S' ⊗[B₀] L) : MvPowerSeries (Fin 2) S' →+* S' ⊗[B₀] L) (I.map g), Submodule.map_coe]; rfl
  have e2 : Ideal.map ((θ S' : MvPowerSeries (Fin 2) S' →ₐ[S'] S' ⊗[B₀] L) : MvPowerSeries (Fin 2) S' →+* S' ⊗[B₀] L)
      (I.map g) = Ideal.span (θ S' '' (g '' (I : Set (MvPowerSeries (Fin 2) S)))) := by
    show Ideal.map _ (Ideal.span (g '' (I : Set (MvPowerSeries (Fin 2) S)))) = _
    rw [Ideal.map_span]; rfl
  rw [hN', hFM, e1, e2]

  set T : Set (S' ⊗[B₀] L) := θ S' '' (g '' (I : Set (MvPowerSeries (Fin 2) S))) with hT
  have hTW : ∀ (a x : S' ⊗[B₀] L), x ∈ Submodule.span S' T → a * x ∈ Submodule.span S' T := by
    intro a x hx
    have h1 : x ∈ (Module.Grassmannian.map f M).toSubmodule := by rw [hN', hFM]; exact hx
    have h2 := hW' a x h1
    rw [hN', hFM] at h2
    exact h2
  let J : Ideal (S' ⊗[B₀] L) :=
    { carrier := Submodule.span S' T
      add_mem' := fun hx hy => (Submodule.span S' T).add_mem hx hy
      zero_mem' := (Submodule.span S' T).zero_mem
      smul_mem' := fun a x hx => hTW a x hx }
  apply Set.Subset.antisymm
  · exact (Submodule.span_le (p := (Ideal.span T).restrictScalars S')).mpr Ideal.subset_span
  · exact (Ideal.span_le (I := J)).mpr Submodule.subset_span

end Asm

end KernelHilb

open KernelHilb in
theorem solution
    (p : ℕ) [Fact p.Prime] (B₀ : Type) [CommRing B₀] (Φ : FormalODModule p B₀) (N h : ℕ)
    [Module.Finite B₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    [Module.Free B₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    (hX : ∀ i, IsNilpotent
      (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N)))) (MvPowerSeries.X i))) :
    ∃ (H : Scheme.{0}) (q : H ⟶ Spec (CommRingCat.of B₀))
      (pt : ∀ (S : Type) [CommRing S] [Algebra B₀ S],
        { I : Ideal (MvPowerSeries (Fin 2) S) //
            Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I) } ≃
          {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap B₀ S))})
      (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (φ : S →ₐ[B₀] S')
        (I : { I : Ideal (MvPowerSeries (Fin 2) S) //
            Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I) }),
        Module.Finite S' (MvPowerSeries (Fin 2) S' ⧸ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            Module.Projective S' (MvPowerSeries (Fin 2) S' ⧸ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ (κ : Type) [Field κ] (f : S' →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ ((I.1.map (MvPowerSeries.map (φ : S →+* S')))).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S') ^ q ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.subst (Φ.map (algebraMap B₀ S')).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S'))) ''
                    ((I.1.map (MvPowerSeries.map (φ : S →+* S'))) : Set (MvPowerSeries (Fin 2) S')) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S'))) ''
                    ((I.1.map (MvPowerSeries.map (φ : S →+* S'))) : Set (MvPowerSeries (Fin 2) S')))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.subst ((Φ.map (algebraMap B₀ S')).act a) f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))), MvPowerSeries.subst (Φ.map (algebraMap B₀ S')).varpi f ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S')))) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S')).act ((p : Zp2 p) ^ N) j ∈ (I.1.map (MvPowerSeries.map (φ : S →+* S'))))),
      (∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (φ : S →ₐ[B₀] S')
        (I : { I : Ideal (MvPowerSeries (Fin 2) S) //
            Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I) }),
        (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
          Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1) ∧
      ∃ (m : ℕ) (ιP : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B₀)),
        IsClosedImmersion ιP ∧ ιP ≫ ProjSpace.π B₀ m = q := by
  classical

  obtain ⟨L, _, _, _, _, _, π, hπ, hker, -, hXn, hev, hΔ, hε0, hε, hρ, hϖ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act p Φ N hX
  choose ρ hρ using hρ
  obtain ⟨ϖ, hϖ⟩ := hϖ

  obtain ⟨θ, hθS, hθnat⟩ :=
    CerednikDrinfeld.FormalODModule.exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural
      p Φ N L π hπ hker hXn hev hΔ hε ρ hρ ϖ hϖ
  have hθ : ThetaSpec p Φ N ρ ϖ θ :=
    { surj := fun S _ _ => (hθS S).2.2.1
      ker := fun S _ _ => (hθS S).2.2.2.1
      ev := fun S _ _ G => by rw [(hθS S).2.1 G]; exact congrArg (fun x => MvFormalGroup.adicEval _ x G) (funext fun i => ((hθS S).1 i).symm)
      nil := fun S _ _ i => by rw [(hθS S).1 i]; exact (hXn i).map (Algebra.TensorProduct.includeRight (R := B₀) (A := S) (B := L))
      comul := fun S _ _ => (hθS S).2.2.2.2.1
      counit := fun S _ _ => (hθS S).2.2.2.2.2.1
      rho := fun S _ _ => (hθS S).2.2.2.2.2.2.1
      varpi := fun S _ _ => (hθS S).2.2.2.2.2.2.2.1
      antipode := fun S _ _ => (hθS S).2.2.2.2.2.2.2.2
      nat := hθnat }

  obtain ⟨H, q, pt, hmapH, natH, m, ιP, hιP, hcomp⟩ :=
    Module.Grassmannian.exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace B₀ L
      (Option (Zp2 p)) (σfam p ρ ϖ) (p ^ h)

  have E := fun (S : Type) [CommRing S] [Algebra B₀ S] => exists_equiv p Φ N h ρ ϖ θ hθ S
  choose e he using E

  have hmapPZ : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (f : S →ₐ[B₀] S')
      (I : { I : Ideal (MvPowerSeries (Fin 2) S) // PZ p Φ N h S I }),
      PZ p Φ N h S' (I.1.map (MvPowerSeries.map (f : S →+* S'))) := by
    intro S S' _ _ _ _ f I

    let M' : { M : Module.Grassmannian S' (S' ⊗[B₀] L) (p ^ h) // WH p h ρ ϖ S' M } :=
      ⟨Module.Grassmannian.map f (e S I).1, hmapH S S' f (e S I)⟩
    have h1 := he S' ((e S').symm M')
    rw [Equiv.apply_symm_apply] at h1
    have h2 := map_compat p Φ N h ρ ϖ θ hθ S S' f I.1 I.2 (e S I).1 (he S I)
    have h3 : ((e S').symm M').1 = I.1.map (MvPowerSeries.map (f : S →+* S')) :=
      eq_of_image_eq θ S' _ _ (ker_le_of_PZ p Φ N h ρ ϖ θ hθ S' _ ((e S').symm M').2)
        (ker_le_map p Φ N h ρ ϖ θ hθ S S' f I.1 I.2) (h1.symm.trans h2)
    exact h3 ▸ ((e S').symm M').2
  refine ⟨H, q, fun S _ _ => (e S).trans (pt S), hmapPZ, ?_, m, ιP, hιP, hcomp⟩
  intro S S' _ _ _ _ f I

  have hpt : e S' ⟨I.1.map (MvPowerSeries.map (f : S →+* S')), hmapPZ S S' f I⟩ =
      ⟨Module.Grassmannian.map f (e S I).1, hmapH S S' f (e S I)⟩ := by
    apply Subtype.ext
    apply Module.Grassmannian.ext
    exact SetLike.coe_injective ((he S' _).trans ((map_compat p Φ N h ρ ϖ θ hθ S S' f I.1 I.2 (e S I).1 (he S I)).symm))
  show (pt S' (e S' ⟨_, _⟩)).1 = Spec.map (CommRingCat.ofHom (f : S →+* S')) ≫ (pt S (e S I)).1
  rw [hpt]
  exact natH S S' f (e S I)

end S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace (solution)
