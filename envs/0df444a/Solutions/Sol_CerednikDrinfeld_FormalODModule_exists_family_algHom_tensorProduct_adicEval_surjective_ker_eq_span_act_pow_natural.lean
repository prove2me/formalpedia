-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/17144de9-14e5-52f4-a00a-a29c3eaadf50

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff X subst_X)

namespace P2mD1a

section Generic

theorem mem_radical_bot {T : Type*} [CommRing T] {x : T} (h : IsNilpotent x) : x ∈ ((⊥ : Ideal T)).radical := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hk]; exact Ideal.zero_mem _⟩

theorem tmul_one_mem_radical_bot {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {a : A} (ha : a ∈ ((⊥ : Ideal A)).radical) : a ⊗ₜ[R] (1 : B) ∈ ((⊥ : Ideal (A ⊗[R] B))).radical := by
  obtain ⟨k, hk⟩ := ha
  rw [Ideal.mem_bot] at hk
  refine ⟨k, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, hk, TensorProduct.zero_tmul]
  exact Ideal.zero_mem _

theorem one_tmul_mem_radical_bot {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {b : B} (hb : b ∈ ((⊥ : Ideal B)).radical) : (1 : A) ⊗ₜ[R] b ∈ ((⊥ : Ideal (A ⊗[R] B))).radical := by
  obtain ⟨k, hk⟩ := hb
  rw [Ideal.mem_bot] at hk
  refine ⟨k, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, hk, TensorProduct.tmul_zero]
  exact Ideal.zero_mem _

theorem pair_mem_radical_bot {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} {x : Fin d → A}
    (hx : ∀ i, x i ∈ ((⊥ : Ideal A)).radical) :
    ∀ t, Sum.elim (fun j => x j ⊗ₜ[R] (1 : A)) (fun j => (1 : A) ⊗ₜ[R] x j) t ∈ ((⊥ : Ideal (A ⊗[R] A))).radical := by
  rintro (j | j)
  · exact tmul_one_mem_radical_bot (hx j)
  · exact one_tmul_mem_radical_bot (hx j)

theorem algHom_apply_eq_of_X {R : Type*} [CommRing R] {T : Type*} [CommRing T] [Algebra R T] {σ : Type*} [Finite σ]
    (J : Ideal T) [IsAdicComplete J T]
    (ψ₁ ψ₂ : MvPowerSeries σ R →ₐ[R] T) (hn : ∀ s, ψ₁ (X s) ∈ J.radical)
    (h : ∀ s, ψ₁ (X s) = ψ₂ (X s)) (f : MvPowerSeries σ R) : ψ₁ f = ψ₂ f := by
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ₁ hn f,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ₂ (fun s => (h s) ▸ hn s) f]
  congr 1
  funext s
  exact h s

theorem algHom_adicEval {R : Type*} [CommRing R] {T T' : Type*} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    {σ : Type*} [Finite σ] (lam : T →ₐ[R] T') (J' : Ideal T') [IsAdicComplete J' T']
    {w : σ → T} (hw : ∀ s, w s ∈ ((⊥ : Ideal T)).radical) (f : MvPowerSeries σ R) :
    lam (MvFormalGroup.adicEval (⊥ : Ideal T) w f) = MvFormalGroup.adicEval J' (fun s => lam (w s)) f :=
  MvFormalGroup.map_adicEval ⊥ J' lam Submodule.fg_bot
    (fun s hs => by rw [Ideal.mem_bot] at hs; rw [hs, map_zero]; exact Ideal.zero_mem _) hw f

theorem adicEval_map_algebraMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] {σ : Type*} [Finite σ] (J : Ideal T) [IsAdicComplete J T]
    {w : σ → T} (hw : ∀ s, w s ∈ J.radical) (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval J w (MvPowerSeries.map (algebraMap R S) f) =
      MvFormalGroup.adicEval J w f := by
  let ψ : MvPowerSeries σ R →ₐ[R] T :=
    { toRingHom := (MvFormalGroup.adicEvalAlgHom (R := S) J hw).toRingHom.comp
        (MvPowerSeries.map (algebraMap R S))
      commutes' := fun r => by
        show MvFormalGroup.adicEvalAlgHom (R := S) J hw
            (MvPowerSeries.map (algebraMap R S) (algebraMap R (MvPowerSeries σ R) r)) = algebraMap R T r
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply, MvPowerSeries.map_C,
          show (MvPowerSeries.C (algebraMap R S r) : MvPowerSeries σ S) = algebraMap S (MvPowerSeries σ S) (algebraMap R S r) by
            rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply],
          AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  have hψX : ∀ s, ψ (X s) = w s := fun s => by
    show MvFormalGroup.adicEvalAlgHom (R := S) J hw (MvPowerSeries.map (algebraMap R S) (X s)) = w s
    rw [MvPowerSeries.map_X, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ
    (fun s => by rw [hψX]; exact hw s) f
  have hx : (fun s => ψ (X s)) = w := funext hψX
  rw [hx] at h
  rw [← h]
  show _ = MvFormalGroup.adicEvalAlgHom (R := S) J hw (MvPowerSeries.map (algebraMap R S) f)
  rw [MvFormalGroup.coe_adicEvalAlgHom]

theorem algHom_adicEval_map {R S T T' : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    [CommRing T'] [Algebra R T'] [Algebra S T'] [IsScalarTower R S T'] {σ : Type*} [Finite σ]
    (lam : T →ₐ[R] T') (J' : Ideal T') [IsAdicComplete J' T'] {w : σ → T}
    (hw : ∀ s, w s ∈ ((⊥ : Ideal T)).radical) (f : MvPowerSeries σ R) :
    lam (MvFormalGroup.adicEval (⊥ : Ideal T) w f) =
      MvFormalGroup.adicEval J' (fun s => lam (w s)) (MvPowerSeries.map (algebraMap R S) f) := by
  have hw' : ∀ s, lam (w s) ∈ J'.radical := fun s => by
    obtain ⟨k, hk⟩ := hw s
    rw [Ideal.mem_bot] at hk
    exact ⟨k, by rw [← map_pow, hk, map_zero]; exact J'.zero_mem⟩
  rw [algHom_adicEval lam J' hw f, adicEval_map_algebraMap J' hw' f]

noncomputable def constantCoeffAlgHom {B : Type*} [CommRing B] {σ : Type*} : MvPowerSeries σ B →ₐ[B] B :=
  { (MvPowerSeries.constantCoeff : MvPowerSeries σ B →+* B) with
    commutes' := fun r => MvPowerSeries.constantCoeff_C r }

theorem adicEval_zero_eq {B : Type*} [CommRing B] {σ : Type*} [Finite σ] {T : Type*} [CommRing T] [Algebra B T]
    (G : MvPowerSeries σ B) :
    MvFormalGroup.adicEval (⊥ : Ideal T) (fun _ : σ => (0 : T)) G = algebraMap B T (constantCoeff G) := by
  let ψ : MvPowerSeries σ B →ₐ[B] T := (Algebra.ofId B T).comp constantCoeffAlgHom
  have hψ0 : ∀ s : σ, ψ (X s) = 0 := fun s => by
    show algebraMap B T (constantCoeff (X s : MvPowerSeries σ B)) = 0
    rw [MvPowerSeries.constantCoeff_X, map_zero]
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal T) ψ
    (fun s => by rw [hψ0]; exact Ideal.zero_mem _) G
  have hx : (fun s : σ => ψ (X s)) = fun _ => (0 : T) := funext hψ0
  rw [hx] at h
  exact h.symm

end Generic

section Theta

variable {B₀ : Type} [CommRing B₀] {d : ℕ} {L : Type} [CommRing L] [HopfAlgebra B₀ L]
  (π : MvPowerSeries (Fin d) B₀ →ₐ[B₀] L) (hX : ∀ i, IsNilpotent (π (X i)))
  (S : Type) [CommRing S] [Algebra B₀ S]

include hX in
theorem X_mem (i : Fin d) : π (X i) ∈ ((⊥ : Ideal L)).radical := mem_radical_bot (hX i)

include hX in
theorem π_mem_of_constantCoeff (H : MvPowerSeries (Fin d) B₀) (hH : constantCoeff H = 0) :
    π H ∈ ((⊥ : Ideal L)).radical := by
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ⊥ π (X_mem π hX) H]
  exact MvFormalGroup.adicEval_mem_radical _ (X_mem π hX) hH

include hX in
theorem xS_mem (i : Fin d) : (1 : S) ⊗ₜ[B₀] π (X i) ∈ ((⊥ : Ideal (S ⊗[B₀] L))).radical :=
  one_tmul_mem_radical_bot (X_mem π hX i)

noncomputable def theta : MvPowerSeries (Fin d) S →ₐ[S] S ⊗[B₀] L :=
  MvFormalGroup.adicEvalAlgHom (⊥ : Ideal (S ⊗[B₀] L)) (xS_mem π hX S)

theorem theta_apply (G : MvPowerSeries (Fin d) S) :
    theta π hX S G = MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B₀] L)) (fun i => (1 : S) ⊗ₜ[B₀] π (X i)) G :=
  congrFun (MvFormalGroup.coe_adicEvalAlgHom _ _) G

theorem theta_X (i : Fin d) : theta π hX S (X i) = (1 : S) ⊗ₜ[B₀] π (X i) := by
  rw [theta_apply, MvFormalGroup.adicEval_X]

theorem theta_X_mem (i : Fin d) : theta π hX S (X i) ∈ ((⊥ : Ideal (S ⊗[B₀] L))).radical := by
  rw [theta_X]; exact xS_mem π hX S i

theorem theta_map (H : MvPowerSeries (Fin d) B₀) :
    theta π hX S (MvPowerSeries.map (algebraMap B₀ S) H) = (1 : S) ⊗ₜ[B₀] π H := by
  rw [theta_apply, adicEval_map_algebraMap _ (xS_mem π hX S)]
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal (S ⊗[B₀] L))
    ((Algebra.TensorProduct.includeRight : L →ₐ[B₀] S ⊗[B₀] L).comp π)
    (fun i => by rw [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]; exact xS_mem π hX S i) H
  rw [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply] at h
  rw [h]
  rfl

section Ker

variable {ι : Type} (φ : ι → MvPowerSeries (Fin d) B₀) (hπ : Function.Surjective π)
  (hker : RingHom.ker π = Ideal.span (Set.range φ))

include hX hker in
theorem exists_X_pow_mem : ∃ N : ℕ, ∀ s, (X s : MvPowerSeries (Fin d) B₀) ^ N ∈ Ideal.span (Set.range φ) := by
  classical
  have hX' : ∀ i : Fin d, ∃ k : ℕ, π (X i) ^ k = 0 := hX
  choose k hk using hX'
  refine ⟨Finset.univ.sup k, fun s => ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) (Finset.mem_univ s))
  rw [hm, pow_add]
  refine Ideal.mul_mem_right _ _ ?_
  rw [← hker, RingHom.mem_ker, map_pow]
  exact hk s

include hX hker hπ in

theorem exists_factor :
    ∃ Ψ : (MvPowerSeries (Fin d) S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap B₀ S) (φ i))) ≃ₐ[S]
        S ⊗[B₀] L,
      ∀ G, theta π hX S G = Ψ (Ideal.Quotient.mk _ G) := by
  obtain ⟨e, he⟩ :=
    MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := S) φ (exists_X_pow_mem π hX φ hker)
  let e₀ : (MvPowerSeries (Fin d) B₀ ⧸ Ideal.span (Set.range φ)) ≃ₐ[B₀] L :=
    (Ideal.quotientEquivAlgOfEq B₀ hker).symm.trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have he₀ : ∀ q, e₀ (Ideal.Quotient.mk _ q) = π q := fun q => by
    simp only [e₀, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_symm, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
  let Ψ := e.symm.trans (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e₀)
  refine ⟨Ψ, fun G => ?_⟩
  refine algHom_apply_eq_of_X ⊥ (theta π hX S) (Ψ.toAlgHom.comp (Ideal.Quotient.mkₐ S _)) (theta_X_mem π hX S)
    (fun s => ?_) G
  rw [theta_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toAlgHom_apply]
  have h1 : Ideal.Quotient.mk (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap B₀ S) (φ i)))
        (X s : MvPowerSeries (Fin d) S)
      = e ((1 : S) ⊗ₜ[B₀] Ideal.Quotient.mk (Ideal.span (Set.range φ)) (X s)) := by
    rw [he, one_smul, MvPowerSeries.map_X]
  rw [h1]
  simp only [Ψ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, AlgEquiv.refl_toAlgHom, AlgHom.id_apply, he₀]

include hX hker hπ in
theorem theta_surjective : Function.Surjective (theta π hX S) := by
  obtain ⟨Ψ, hΨ⟩ := exists_factor π hX S φ hπ hker
  intro y
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective (Ψ.symm y)
  exact ⟨G, by rw [hΨ, hG, AlgEquiv.apply_symm_apply]⟩

include hX hker hπ in
theorem ker_theta :
    RingHom.ker (theta π hX S) = Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap B₀ S) (φ i)) := by
  obtain ⟨Ψ, hΨ⟩ := exists_factor π hX S φ hπ hker
  ext G
  rw [RingHom.mem_ker, hΨ, map_eq_zero_iff _ Ψ.injective, Ideal.Quotient.eq_zero_iff_mem]

end Ker

theorem counit_theta (hε : ∀ G, Coalgebra.counit (R := B₀) (π G) = constantCoeff G) (G : MvPowerSeries (Fin d) S) :
    Coalgebra.counit (R := S) (theta π hX S G) = constantCoeff G := by
  have h0 : ∀ i, ((Bialgebra.counitAlgHom S (S ⊗[B₀] L)).comp (theta π hX S)) (X i) = 0 := fun i => by
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, theta_X, TensorProduct.counit_tmul, hε,
      MvPowerSeries.constantCoeff_X, zero_smul]
  have h := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal S)
    ((Bialgebra.counitAlgHom S (S ⊗[B₀] L)).comp (theta π hX S)) (fun i => by rw [h0]; exact Ideal.zero_mem _) G
  have hx : (fun i => ((Bialgebra.counitAlgHom S (S ⊗[B₀] L)).comp (theta π hX S)) (X i)) = fun _ => (0 : S) :=
    funext h0
  rw [hx, adicEval_zero_eq, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply] at h
  rw [h]
  rfl

theorem map_id_theta (τ : L →ₐc[B₀] L) (s : Fin d → MvPowerSeries (Fin d) B₀) (hs0 : ∀ i, constantCoeff (s i) = 0)
    (hτ : ∀ G, τ (π G) = π (subst s G)) (G : MvPowerSeries (Fin d) S) :
    Algebra.TensorProduct.map (AlgHom.id S S) (τ : L →ₐ[B₀] L) (theta π hX S G) =
      theta π hX S (subst (fun i => MvPowerSeries.map (algebraMap B₀ S) (s i)) G) := by
  have hsS : ∀ i, constantCoeff (MvPowerSeries.map (algebraMap B₀ S) (s i)) = 0 := fun i => by
    rw [MvPowerSeries.constantCoeff_map, hs0, map_zero]
  have hnil : ∀ i, π (s i) ∈ ((⊥ : Ideal L)).radical := fun i => π_mem_of_constantCoeff π hX (s i) (hs0 i)
  have key := algHom_apply_eq_of_X ⊥
    ((Algebra.TensorProduct.map (AlgHom.id S S) (τ : L →ₐ[B₀] L)).comp (theta π hX S))
    ((theta π hX S).comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hsS))) ?_ ?_ G
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply] at key
    exact key
  · intro i
    rw [AlgHom.comp_apply, theta_X, Algebra.TensorProduct.map_tmul, map_one, BialgHom.coe_toAlgHom, hτ,
      subst_X (hasSubst_of_constantCoeff_zero hs0)]
    exact one_tmul_mem_radical_bot (hnil i)
  · intro i
    rw [AlgHom.comp_apply, theta_X, Algebra.TensorProduct.map_tmul, map_one, BialgHom.coe_toAlgHom, hτ,
      subst_X (hasSubst_of_constantCoeff_zero hs0), AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply,
      subst_X (hasSubst_of_constantCoeff_zero hsS), theta_map]

end Theta

section Antipode

open WithConv

variable {B₀ : Type} [CommRing B₀] {d : ℕ} (F : MvFormalGroup d B₀) {L : Type} [CommRing L] [HopfAlgebra B₀ L]
  (π : MvPowerSeries (Fin d) B₀ →ₐ[B₀] L) (hπ : Function.Surjective π) (hX : ∀ i, IsNilpotent (π (X i)))
  (hΔ : ∀ i, Coalgebra.comul (R := B₀) (π (X i)) =
    MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B₀] L))
      (Sum.elim (fun j => π (X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (X j))) (F.toPowerSeries i))
  (hε : ∀ G, Coalgebra.counit (R := B₀) (π G) = constantCoeff G)
  (τ : L →ₐ[B₀] L) (s : Fin d → MvPowerSeries (Fin d) B₀) (hs0 : ∀ i, constantCoeff (s i) = 0)
  (hτ : ∀ G, τ (π G) = π (subst s G))
  (hinv : ∀ i, subst (Sum.elim s fun j => X j) (F.toPowerSeries i) = 0)

include hX in
theorem w_mem : ∀ t : Fin d ⊕ Fin d,
    Sum.elim (fun j => π (X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (X j)) t ∈
      ((⊥ : Ideal (L ⊗[B₀] L))).radical := by
  rintro (j | j)
  · exact tmul_one_mem_radical_bot (X_mem π hX j)
  · exact one_tmul_mem_radical_bot (X_mem π hX j)

include hπ hX hΔ hε hs0 hτ hinv in

theorem conv_tau_id : (toConv τ * toConv (AlgHom.id B₀ L) : WithConv (L →ₐ[B₀] L)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro z
  obtain ⟨G, rfl⟩ := hπ z
  have hs' : ∀ t : Fin d ⊕ Fin d, constantCoeff (Sum.elim s (fun j => (X j : MvPowerSeries (Fin d) B₀)) t) = 0 := by
    rintro (j | j)
    · exact hs0 j
    · exact MvPowerSeries.constantCoeff_X j
  have hR : ∀ i, ((1 : WithConv (L →ₐ[B₀] L)).ofConv.comp π) (X i) = 0 := fun i => by
    rw [AlgHom.comp_apply]
    show (1 : WithConv (L →ₐ[B₀] L)) (π (X i)) = 0
    rw [AlgHom.convOne_apply, hε, MvPowerSeries.constantCoeff_X, map_zero]
  have hL : ∀ i, ((toConv τ * toConv (AlgHom.id B₀ L) : WithConv (L →ₐ[B₀] L)).ofConv.comp π) (X i) = 0 := fun i => by
    rw [AlgHom.comp_apply]
    show (toConv τ * toConv (AlgHom.id B₀ L) : WithConv (L →ₐ[B₀] L)) (π (X i)) = 0
    rw [AlgHom.convMul_apply, hΔ i,
      algHom_adicEval (Algebra.TensorProduct.lift (toConv τ).ofConv (toConv (AlgHom.id B₀ L)).ofConv _) ⊥ (w_mem π hX)
        (F.toPowerSeries i)]
    have ht : (fun t => Algebra.TensorProduct.lift (toConv τ).ofConv (toConv (AlgHom.id B₀ L)).ofConv
          (fun _ _ => Commute.all _ _)
          (Sum.elim (fun j => π (X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (X j)) t)) =
        fun t => π (Sum.elim s (fun j => (X j : MvPowerSeries (Fin d) B₀)) t) := by
      funext t
      rcases t with j | j
      · simp only [Sum.elim_inl, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        show τ (π (X j)) = π (s j)
        rw [hτ, subst_X (hasSubst_of_constantCoeff_zero hs0)]
      · simp only [Sum.elim_inr, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
    rw [ht]
    have h2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal L)
      (π.comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs'))) ?_ (F.toPowerSeries i)
    · have ht2 : (fun t => (π.comp (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hs'))) (X t)) =
          fun t => π (Sum.elim s (fun j => (X j : MvPowerSeries (Fin d) B₀)) t) := by
        funext t
        rw [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, subst_X (hasSubst_of_constantCoeff_zero hs')]
      rw [ht2, AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, hinv, map_zero] at h2
      exact h2.symm
    · intro t
      rw [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, subst_X (hasSubst_of_constantCoeff_zero hs')]
      rcases t with j | j
      · exact π_mem_of_constantCoeff π hX (s j) (hs0 j)
      · exact X_mem π hX j
  exact algHom_apply_eq_of_X ⊥ ((toConv τ * toConv (AlgHom.id B₀ L) : WithConv (L →ₐ[B₀] L)).ofConv.comp π)
    ((1 : WithConv (L →ₐ[B₀] L)).ofConv.comp π) (fun i => by rw [hL]; exact Ideal.zero_mem _)
    (fun i => by rw [hL, hR]) G

end Antipode

section Antipode2

open WithConv

variable {B₀ : Type} [CommRing B₀] {L : Type} [CommRing L] [HopfAlgebra B₀ L]

theorem antipode_eq_of_conv (τ : L →ₐ[B₀] L)
    (h : (toConv τ * toConv (AlgHom.id B₀ L) : WithConv (L →ₐ[B₀] L)) = 1) (y : L) :
    HopfAlgebra.antipode B₀ (A := L) y = τ y := by
  have h1 : (toConv τ.toLinearMap * toConv (LinearMap.id : L →ₗ[B₀] L) : WithConv (L →ₗ[B₀] L)) = 1 := by
    have h' := congrArg (fun f : WithConv (L →ₐ[B₀] L) => toConv f.ofConv.toLinearMap) h
    simp only [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne] at h'
    exact h'
  have h2 : (toConv (LinearMap.id : L →ₗ[B₀] L) * toConv (HopfAlgebra.antipode B₀ (A := L)) :
      WithConv (L →ₗ[B₀] L)) = 1 := by
    rw [LinearMap.convMul_def, LinearMap.convOne_def]
    exact congrArg toConv (HopfAlgebra.mul_antipode_lTensor_comul (R := B₀) (A := L))
  have h3 := left_inv_eq_right_inv h1 h2
  have h4 := congrArg (fun f : WithConv (L →ₗ[B₀] L) => f.ofConv y) h3
  exact h4.symm

variable (S : Type) [CommRing S] [Algebra B₀ S]

theorem antipode_tensor (τ : L →ₐ[B₀] L) (hant : ∀ y : L, HopfAlgebra.antipode B₀ (A := L) y = τ y)
    (z : S ⊗[B₀] L) :
    HopfAlgebra.antipode S (A := S ⊗[B₀] L) z = Algebra.TensorProduct.map (AlgHom.id S S) τ z := by
  rw [TensorProduct.antipode_def]
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.TensorProduct.map_tmul, CommSemiring.antipode_eq_id,
      LinearMap.id_apply, AlgHom.id_apply, hant]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Antipode2

section Comul

variable {B₀ : Type} [CommRing B₀] {d : ℕ} (F : MvFormalGroup d B₀) {L : Type} [CommRing L] [HopfAlgebra B₀ L]
  (π : MvPowerSeries (Fin d) B₀ →ₐ[B₀] L) (hX : ∀ i, IsNilpotent (π (X i)))
  (hΔ : ∀ i, Coalgebra.comul (R := B₀) (π (X i)) =
    MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B₀] L))
      (Sum.elim (fun j => π (X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (X j))) (F.toPowerSeries i))
  (S : Type) [CommRing S] [Algebra B₀ S]

include hΔ in
theorem comul_theta_X (i : Fin d) :
    Coalgebra.comul (R := S) (theta π hX S (X i)) =
      MvFormalGroup.adicEval (⊥ : Ideal ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)))
        (Sum.elim (fun j => theta π hX S (X j) ⊗ₜ[S] (1 : S ⊗[B₀] L))
          (fun j => (1 : S ⊗[B₀] L) ⊗ₜ[S] theta π hX S (X j)))
        (MvPowerSeries.map (algebraMap B₀ S) (F.toPowerSeries i)) := by
  let jL : S ⊗[B₀] L →ₐ[S] ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)) := Algebra.TensorProduct.includeLeft
  let jR : S ⊗[B₀] L →ₐ[S] ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)) := Algebra.TensorProduct.includeRight
  let iR : L →ₐ[B₀] S ⊗[B₀] L := Algebra.TensorProduct.includeRight
  let κ : L ⊗[B₀] L →ₐ[B₀] ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)) :=
    Algebra.TensorProduct.lift ((jL.restrictScalars B₀).comp iR) ((jR.restrictScalars B₀).comp iR)
      (fun x y => Commute.all (((jL.restrictScalars B₀).comp iR) x) (((jR.restrictScalars B₀).comp iR) y))
  have hκ : ∀ a b : L, κ (a ⊗ₜ[B₀] b) = ((1 : S) ⊗ₜ[B₀] a) ⊗ₜ[S] ((1 : S) ⊗ₜ[B₀] b) := fun a b => by
    simp only [κ, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.restrictScalars_apply, jL, jR, iR,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hcomm : ∀ y : L ⊗[B₀] L,
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm B₀ S B₀ S S S L L)
        (((1 : S) ⊗ₜ[S] (1 : S)) ⊗ₜ[B₀] y) = κ y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
    | tmul a b => rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, hκ]
    | add x y hx hy => rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, hx, hy]
  have e1 := algHom_adicEval_map (R := B₀) (S := S) (T := L ⊗[B₀] L) (T' := ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L))) κ ⊥ (w_mem π hX)
    (F.toPowerSeries i)
  have hu : (fun t => κ (Sum.elim (fun j => π (X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (X j)) t)) =
      Sum.elim (fun j => theta π hX S (X j) ⊗ₜ[S] (1 : S ⊗[B₀] L))
        (fun j => (1 : S ⊗[B₀] L) ⊗ₜ[S] theta π hX S (X j)) := by
    funext t
    rcases t with j | j
    · simp only [Sum.elim_inl, hκ, theta_X, Algebra.TensorProduct.one_def]
    · simp only [Sum.elim_inr, hκ, theta_X, Algebra.TensorProduct.one_def]
  rw [hu] at e1
  rw [theta_X, TensorProduct.comul_tmul, CommSemiring.comul_apply, hΔ i, hcomm]
  exact e1

omit hΔ

theorem map_theta (S' : Type) [CommRing S'] [Algebra B₀ S'] (f : S →ₐ[B₀] S') (G : MvPowerSeries (Fin d) S) :
    Algebra.TensorProduct.map f (AlgHom.id B₀ L) (theta π hX S G) =
      theta π hX S' (MvPowerSeries.map (f : S →+* S') G) := by
  letI alg : Algebra S (S' ⊗[B₀] L) := ((algebraMap S' (S' ⊗[B₀] L)).comp (f : S →+* S')).toAlgebra
  have halg : ∀ r : S, algebraMap S (S' ⊗[B₀] L) r = algebraMap S' (S' ⊗[B₀] L) (f r) := fun r => rfl
  let ψ₁ : MvPowerSeries (Fin d) S →ₐ[S] S' ⊗[B₀] L :=
    { toRingHom := (Algebra.TensorProduct.map f (AlgHom.id B₀ L)).toRingHom.comp (theta π hX S).toRingHom
      commutes' := fun r => by
        show Algebra.TensorProduct.map f (AlgHom.id B₀ L) (theta π hX S (algebraMap S (MvPowerSeries (Fin d) S) r)) =
          algebraMap S (S' ⊗[B₀] L) r
        rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
          Algebra.TensorProduct.map_tmul, map_one, halg, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self_apply] }
  let ψ₂ : MvPowerSeries (Fin d) S →ₐ[S] S' ⊗[B₀] L :=
    { toRingHom := (theta π hX S').toRingHom.comp (MvPowerSeries.map (f : S →+* S'))
      commutes' := fun r => by
        show theta π hX S' (MvPowerSeries.map (f : S →+* S') (algebraMap S (MvPowerSeries (Fin d) S) r)) =
          algebraMap S (S' ⊗[B₀] L) r
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply, MvPowerSeries.map_C, halg, AlgHom.coe_toRingHom,
          show (MvPowerSeries.C (f r) : MvPowerSeries (Fin d) S') = algebraMap S' (MvPowerSeries (Fin d) S') (f r) by
            rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply],
          AlgHom.commutes] }
  have key := algHom_apply_eq_of_X ⊥ ψ₁ ψ₂ ?_ ?_ G
  · exact key
  · intro i
    show Algebra.TensorProduct.map f (AlgHom.id B₀ L) (theta π hX S (X i)) ∈ _
    rw [theta_X, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    exact xS_mem π hX S' i
  · intro i
    show Algebra.TensorProduct.map f (AlgHom.id B₀ L) (theta π hX S (X i)) =
      theta π hX S' (MvPowerSeries.map (f : S →+* S') (X i))
    rw [theta_X, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, MvPowerSeries.map_X, theta_X]

end Comul

section OD

variable {p : ℕ} [Fact p.Prime] {B₀ : Type} [CommRing B₀] (Φ : FormalODModule p B₀)

theorem act_zero : Φ.act 0 = fun _ => 0 := by
  rw [← Nat.cast_zero, Φ.act_natCast, MvFormalGroup.nthSeries_zero]

theorem subst_elim_act_neg_one (i : Fin 2) :
    subst (Sum.elim (Φ.act (-1)) fun j => X j) (Φ.F.toPowerSeries i) = 0 := by
  have h := Φ.act_add (-1) 1
  rw [neg_add_cancel, act_zero, Φ.act_one] at h
  have hi := congrFun h i
  exact hi.symm

end OD

end P2mD1a

open P2mD1a in

theorem solution
    (p : ℕ) [Fact p.Prime] {B₀ : Type} [CommRing B₀] (Φ : FormalODModule p B₀) (N : ℕ)
    (L : Type) [CommRing L] [HopfAlgebra B₀ L]
    (π : MvPowerSeries (Fin 2) B₀ →ₐ[B₀] L) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N))))
    (hX : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hΔ : ∀ i, Coalgebra.comul (R := B₀) (π (MvPowerSeries.X i)) =
      MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B₀] L))
        (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (MvPowerSeries.X j)))
        (Φ.F.toPowerSeries i))
    (hε : ∀ G, Coalgebra.counit (R := B₀) (π G) = MvPowerSeries.constantCoeff G)
    (ρ : Zp2 p → (L →ₐc[B₀] L)) (hρ : ∀ a G, ρ a (π G) = π (MvPowerSeries.subst (Φ.act a) G))
    (ϖ : L →ₐc[B₀] L) (hϖ : ∀ G, ϖ (π G) = π (MvPowerSeries.subst Φ.varpi G)) :
    ∃ θ : ∀ (S : Type) [CommRing S] [Algebra B₀ S], MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L,
      (∀ (S : Type) [CommRing S] [Algebra B₀ S],
        (∀ i, θ S (MvPowerSeries.X i) = (1 : S) ⊗ₜ[B₀] π (MvPowerSeries.X i)) ∧
        (∀ G, θ S G = MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B₀] L)) (fun i => (1 : S) ⊗ₜ[B₀] π (MvPowerSeries.X i)) G) ∧
        Function.Surjective (θ S) ∧
        RingHom.ker (θ S) = Ideal.span (Set.range ((Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N))) ∧
        (∀ i, Coalgebra.comul (R := S) (θ S (MvPowerSeries.X i)) =
          MvFormalGroup.adicEval (⊥ : Ideal ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)))
            (Sum.elim (fun j => θ S (MvPowerSeries.X j) ⊗ₜ[S] (1 : S ⊗[B₀] L))
              (fun j => (1 : S ⊗[B₀] L) ⊗ₜ[S] θ S (MvPowerSeries.X j)))
            ((Φ.map (algebraMap B₀ S)).F.toPowerSeries i)) ∧
        (∀ G, Coalgebra.counit (R := S) (θ S G) = MvPowerSeries.constantCoeff G) ∧
        (∀ (a : Zp2 p) (G : MvPowerSeries (Fin 2) S),
          Algebra.TensorProduct.map (AlgHom.id S S) (ρ a : L →ₐ[B₀] L) (θ S G) =
            θ S (MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) G)) ∧
        (∀ G : MvPowerSeries (Fin 2) S,
          Algebra.TensorProduct.map (AlgHom.id S S) (ϖ : L →ₐ[B₀] L) (θ S G) =
            θ S (MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi G)) ∧
        (∀ G : MvPowerSeries (Fin 2) S,
          HopfAlgebra.antipode S (A := S ⊗[B₀] L) (θ S G) =
            θ S (MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act (-1)) G))) ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (f : S →ₐ[B₀] S')
        (G : MvPowerSeries (Fin 2) S),
        Algebra.TensorProduct.map f (AlgHom.id B₀ L) (θ S G) = θ S' (MvPowerSeries.map (f : S →+* S') G)) := by
  refine ⟨fun S _ _ => theta π hX S, fun S _ _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun S S' _ _ _ _ f G => ?_⟩
  · exact fun i => theta_X π hX S i
  · exact fun G => theta_apply π hX S G
  · exact theta_surjective π hX S (Φ.act ((p : Zp2 p) ^ N)) hπ hker
  · exact ker_theta π hX S (Φ.act ((p : Zp2 p) ^ N)) hπ hker
  · exact fun i => comul_theta_X Φ.F π hX hΔ S i
  · exact fun G => counit_theta π hX S hε G
  · exact fun a G => map_id_theta π hX S (ρ a) (Φ.act a) (Φ.isLawHom_act a).1 (hρ a) G
  · exact fun G => map_id_theta π hX S ϖ Φ.varpi Φ.isLawHom_varpi.1 hϖ G
  · intro G
    have hant := antipode_eq_of_conv (ρ (-1) : L →ₐ[B₀] L)
      (conv_tau_id Φ.F π hπ hX hΔ hε _ (Φ.act (-1)) (Φ.isLawHom_act (-1)).1
        (fun G => by rw [BialgHom.coe_toAlgHom]; exact hρ (-1) G) (subst_elim_act_neg_one Φ))
    rw [antipode_tensor S (ρ (-1) : L →ₐ[B₀] L) hant]
    exact map_id_theta π hX S (ρ (-1)) (Φ.act (-1)) (Φ.isLawHom_act (-1)).1 (hρ (-1)) G
  · exact map_theta π hX S S' f G

end S_CerednikDrinfeld_FormalODModule_exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural (solution)
