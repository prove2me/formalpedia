-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_levelCoaction_of_subgroup_ideal_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a573e7ee-cc69-507a-8143-aff28f6d9b25

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_levelCoaction_of_subgroup_ideal_of_ne_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

namespace InvGenB29

noncomputable section

section Helpers

theorem algHom_adicEval_bot {R A C : Type} [CommRing R] [CommRing A] [CommRing C] {_iA : Algebra R A}
    {_iC : Algebra R C} {σ : Type} [Finite σ] (φ : A →ₐ[R] C) (x : σ → A)
    (hx : ∀ s, x s ∈ (⊥ : Ideal A).radical) (f : MvPowerSeries σ R) :
    φ (MvFormalGroup.adicEval (⊥ : Ideal A) x f) =
      MvFormalGroup.adicEval (⊥ : Ideal C) (fun s => φ (x s)) f :=
  MvFormalGroup.map_adicEval (⊥ : Ideal A) (⊥ : Ideal C) φ Submodule.fg_bot
    (fun s hs => by rw [(Submodule.mem_bot _).mp hs, map_zero]; exact Ideal.zero_mem _) hx f

theorem mem_radical_bot_of_isNilpotent {A : Type} [CommRing A] {a : A} (h : IsNilpotent a) :
    a ∈ (⊥ : Ideal A).radical := by
  obtain ⟨n, hn⟩ := h
  exact Ideal.mem_radical_iff.mpr ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩

theorem isNilpotent_of_mem_radical_bot {A : Type} [CommRing A] {a : A} (h : a ∈ (⊥ : Ideal A).radical) :
    IsNilpotent a := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h
  exact ⟨n, Ideal.mem_bot.mp hn⟩

theorem map_mem_radical_bot {R A C : Type} [CommRing R] [CommRing A] [CommRing C] {_iA : Algebra R A}
    {_iC : Algebra R C} (φ : A →ₐ[R] C) {a : A} (h : a ∈ (⊥ : Ideal A).radical) :
    φ a ∈ (⊥ : Ideal C).radical :=
  mem_radical_bot_of_isNilpotent ((isNilpotent_of_mem_radical_bot h).map φ)

theorem tmul_one_mem_radical_bot {R A C : Type} [CommRing R] [CommRing A] [CommRing C] [Algebra R A]
    [Algebra R C] {a : A} (h : a ∈ (⊥ : Ideal A).radical) :
    a ⊗ₜ[R] (1 : C) ∈ (⊥ : Ideal (A ⊗[R] C)).radical := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h
  refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, Ideal.mem_bot.mp hn, TensorProduct.zero_tmul]
  exact Ideal.zero_mem _

theorem one_tmul_mem_radical_bot {R A C : Type} [CommRing R] [CommRing A] [CommRing C] [Algebra R A]
    [Algebra R C] {c : C} (h : c ∈ (⊥ : Ideal C).radical) :
    (1 : A) ⊗ₜ[R] c ∈ (⊥ : Ideal (A ⊗[R] C)).radical := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h
  refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, Ideal.mem_bot.mp hn, TensorProduct.tmul_zero]
  exact Ideal.zero_mem _

theorem forall_sumElim' {α β M : Type} {p : M → Prop} {x : α → M} {y : β → M}
    (hx : ∀ a, p (x a)) (hy : ∀ b, p (y b)) : ∀ c, p (Sum.elim x y c) := by
  rintro (a | b)
  exacts [hx a, hy b]

theorem adicEval_mem_radical_bot {R A : Type} [CommRing R] [CommRing A] {_iA : Algebra R A} {σ : Type} [Finite σ]
    {x : σ → A} (hx : ∀ s, x s ∈ (⊥ : Ideal A).radical) {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    MvFormalGroup.adicEval (⊥ : Ideal A) x f ∈ (⊥ : Ideal A).radical :=
  MvFormalGroup.adicEval_mem_radical ⊥ hx hf

end Helpers

theorem eq_adicEval_of_X_pow_mem_ker {B : Type} [CommRing B] {S : Type} [CommRing S] [Algebra B S]
    (θ : MvPowerSeries (Fin 2) B →ₐ[B] S) (hθ : ∃ N : ℕ, ∀ i, (MvPowerSeries.X i) ^ N ∈ RingHom.ker θ)
    (G : MvPowerSeries (Fin 2) B) :
    θ G = MvFormalGroup.adicEval (⊥ : Ideal S) (fun i => θ (MvPowerSeries.X i)) G := by
  classical
  obtain ⟨N, hN⟩ := hθ
  have hN0 : ∀ i, θ (MvPowerSeries.X i ^ N) = 0 := fun i => hN i
  have hN' : ∀ i, θ (MvPowerSeries.X i ^ (N + 1)) = 0 := fun i => by
    rw [pow_succ, map_mul, hN0 i, zero_mul]
  have hxrad : ∀ i, θ (MvPowerSeries.X i) ∈ (⊥ : Ideal S).radical := fun i =>
    Ideal.mem_radical_iff.mpr ⟨N, by rw [← map_pow, hN0 i]; exact Ideal.zero_mem _⟩
  let E : MvPowerSeries (Fin 2) B →ₐ[B] S := MvFormalGroup.adicEvalAlgHom ⊥ hxrad
  have hE : ∀ f, E f = MvFormalGroup.adicEval ⊥ (fun i => θ (MvPowerSeries.X i)) f := fun f =>
    congrFun (MvFormalGroup.coe_adicEvalAlgHom ⊥ hxrad) f
  rw [← hE]
  have hE' : ∀ i, E (MvPowerSeries.X i ^ (N + 1)) = 0 := fun i => by
    rw [map_pow, hE, MvFormalGroup.adicEval_X, ← map_pow, hN' i]

  have hfg : θ.comp (MvPolynomial.coeToMvPowerSeries.algHom B) = E.comp (MvPolynomial.coeToMvPowerSeries.algHom B) :=
    MvPolynomial.algHom_ext fun i => by
      simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X,
        MvPowerSeries.map_X]
      rw [hE, MvFormalGroup.adicEval_X]
  have hpoly : ∀ P : MvPolynomial (Fin 2) B, θ (P : MvPowerSeries (Fin 2) B) = E P := fun P => by
    have := congrArg (fun φ => φ P) hfg
    simpa only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id, RingHom.id_apply] using this

  let m : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  have hm : ∀ i, m i = N := fun i => by simp [m]
  set P : MvPolynomial (Fin 2) B := MvPowerSeries.trunc' B m G with hP
  have hRcoeff : ∀ d : Fin 2 →₀ ℕ, d ≤ m → MvPowerSeries.coeff d (G - (P : MvPowerSeries (Fin 2) B)) = 0 := by
    intro d hd
    rw [map_sub, MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_trunc', if_pos hd, sub_self]
  let R0 : MvPowerSeries (Fin 2) B := fun d => if N + 1 ≤ d 0 then MvPowerSeries.coeff d (G - (P : MvPowerSeries (Fin 2) B)) else 0
  have hR0c : ∀ d, MvPowerSeries.coeff d R0 = if N + 1 ≤ d 0 then MvPowerSeries.coeff d (G - (P : MvPowerSeries (Fin 2) B)) else 0 :=
    fun d => MvPowerSeries.coeff_apply _ _
  have hR0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) B) ^ (N + 1) ∣ R0 :=
    MvPowerSeries.X_pow_dvd_iff.mpr fun d hd => by rw [hR0c, if_neg (not_le.mpr hd)]
  have hR1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) B) ^ (N + 1) ∣ (G - (P : MvPowerSeries (Fin 2) B) - R0) :=
    MvPowerSeries.X_pow_dvd_iff.mpr fun d hd => by
      rw [map_sub, hR0c]
      split_ifs with h0
      · rw [sub_self]
      · rw [sub_zero]
        apply hRcoeff
        rw [Finsupp.le_def, Fin.forall_fin_two, hm, hm]
        exact ⟨by omega, by omega⟩
  have hG : G = (P : MvPowerSeries (Fin 2) B) + (R0 + (G - (P : MvPowerSeries (Fin 2) B) - R0)) := by ring
  have kill : ∀ φ : MvPowerSeries (Fin 2) B →ₐ[B] S, (∀ i, φ (MvPowerSeries.X i ^ (N + 1)) = 0) →
      φ G = φ (P : MvPowerSeries (Fin 2) B) := by
    intro φ hφ
    obtain ⟨H0, e0⟩ := hR0
    obtain ⟨H1, e1⟩ := hR1
    rw [hG, map_add, map_add, e1, e0, map_mul, map_mul, hφ 0, hφ 1, zero_mul, zero_mul, add_zero, add_zero]
  rw [kill θ hN', kill E hE', hpoly]

theorem levelCoaction_aux
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    {L : Type} [CommRing L] [HopfAlgebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hcomul : ∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i))
    (hcounit : ∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G)
    {S : Type} [CommRing S] [Algebra B S] (θ : MvPowerSeries (Fin 2) B →ₐ[B] S) (hθ : Function.Surjective θ)
    (N : ℕ) (hN : N ≠ 0) (hkerθ : RingHom.ker θ = I ^ N) :
    ∃ δ : S →ₐ[B] S ⊗[B] L,
      (∀ G, δ (θ G) =
        MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L))
            (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G) ∧
      (∀ s, (_root_.TensorProduct.assoc B S L L)
          (Algebra.TensorProduct.map δ (AlgHom.id B L) (δ s)) =
        Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.comulAlgHom B L) (δ s)) ∧
      (∀ s, Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.counitAlgHom B L) (δ s) =
        s ⊗ₜ[B] (1 : B)) ∧
      (∀ (k : ℕ), ∀ f ∈ I ^ k, δ (θ f) ∈
        Ideal.span ((fun s : S => s ⊗ₜ[B] (1 : L)) '' (((I ^ k).map θ) : Set S))) ∧
      (∀ (qL : S →ₐ[B] L), (∀ G, qL (θ G) = π G) →
        ∀ G, Algebra.TensorProduct.map qL (AlgHom.id B L) (δ (θ G)) = Coalgebra.comul (R := B) (π G)) := by
  classical
  obtain ⟨q, hq⟩ := hnil
  have hF : MvPowerSeries.HasSubst X.F.toPowerSeries := X.F.hasSubst_toPowerSeries
  have hkmem : ∀ x ∈ I ^ N, θ x = 0 := fun x hx => by
    rw [← hkerθ] at hx
    exact RingHom.mem_ker.mp hx

  have hxbar : ∀ j : Fin 2, θ (MvPowerSeries.X j) ∈ (⊥ : Ideal S).radical := by
    intro j
    refine Ideal.mem_radical_iff.mpr ⟨q * N, ?_⟩
    rw [← map_pow, pow_mul, hkmem _ (Ideal.pow_mem_pow (hq j) N)]
    exact Ideal.zero_mem _
  have hπx : ∀ j : Fin 2, π (MvPowerSeries.X j) ∈ (⊥ : Ideal L).radical := fun j =>
    mem_radical_bot_of_isNilpotent (hπnil j)
  have hw : ∀ t, (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) t ∈ (⊥ : Ideal (S ⊗[B] L)).radical :=
    forall_sumElim' (fun j => tmul_one_mem_radical_bot (hxbar j)) (fun j => one_tmul_mem_radical_bot (hπx j))
  have hptF : ∀ i, (fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) i ∈ (⊥ : Ideal (S ⊗[B] L)).radical := fun i =>
    MvFormalGroup.adicEval_mem_radical ⊥ hw (X.F.constantCoeff_eq_zero i)
  have hWL : ∀ t, (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j))) t ∈ (⊥ : Ideal (L ⊗[B] L)).radical :=
    forall_sumElim' (fun j => tmul_one_mem_radical_bot (hπx j)) (fun j => one_tmul_mem_radical_bot (hπx j))
  have hWX : ∀ j, (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L ⊗[B] L)) j ∈ (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))).radical := fun j => tmul_one_mem_radical_bot (hxbar j)
  have hWY : ∀ j, (fun j => (1 : S) ⊗ₜ[B] (π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))) j ∈ (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))).radical := fun j =>
    one_tmul_mem_radical_bot (tmul_one_mem_radical_bot (hπx j))
  have hWZ : ∀ j, (fun j => (1 : S) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] π (MvPowerSeries.X j))) j ∈ (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))).radical := fun j =>
    one_tmul_mem_radical_bot (one_tmul_mem_radical_bot (hπx j))

  have hmk : ∀ G, θ G = MvFormalGroup.adicEval (⊥ : Ideal S) (fun j => θ (MvPowerSeries.X j)) G := fun G =>
    eq_adicEval_of_X_pow_mem_ker θ ⟨q * N, fun i => by rw [hkerθ, pow_mul]; exact Ideal.pow_mem_pow (hq i) _⟩ G
  have hIker : ∀ g ∈ I, π g = 0 := fun g hg => by
    rw [← hker] at hg
    exact RingHom.mem_ker.mp hg

  let δ₀ : MvPowerSeries (Fin 2) B →ₐ[B] (S ⊗[B] L) := MvFormalGroup.adicEvalAlgHom ⊥ hptF
  have hδ₀ : ∀ G, δ₀ G = MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) G := fun G =>
    congrFun (MvFormalGroup.coe_adicEvalAlgHom ⊥ hptF) G
  have hE : ∀ G, MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (MvPowerSeries.subst X.F.toPowerSeries G) = δ₀ G := by
    intro G
    rw [hδ₀, MvFormalGroup.adicEval_subst ⊥ hw hF]

  have hXl : MvPowerSeries.HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _
  have hXr : MvPowerSeries.HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _
  have hinl : ∀ g, MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) g) = θ g ⊗ₜ[B] (1 : L) := by
    intro g
    rw [MvFormalGroup.adicEval_subst ⊥ hw hXl, hmk g]
    have h2 := algHom_adicEval_bot (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L)) _ hxbar g
    rw [Algebra.TensorProduct.includeLeft_apply] at h2
    rw [h2]
    congr 1
    funext l
    rw [MvFormalGroup.adicEval_X]
    rfl
  have hinr : ∀ g, MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) g) = (1 : S) ⊗ₜ[B] π g := by
    intro g
    rw [MvFormalGroup.adicEval_subst ⊥ hw hXr, hev g]
    have h2 := algHom_adicEval_bot (Algebra.TensorProduct.includeRight (R := B) (A := S) (B := L)) _ hπx g
    rw [Algebra.TensorProduct.includeRight_apply] at h2
    rw [h2]
    congr 1
    funext l
    rw [MvFormalGroup.adicEval_X]
    rfl

  have hδI : ∀ f ∈ I, δ₀ f ∈ ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L))) := by
    intro f hf
    have hsub : Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪ (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))) ≤
        Ideal.comap (MvFormalGroup.adicEvalAlgHom (R := B) ⊥ hw) ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L))) := by
      rw [Ideal.span_le]
      rintro _ (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
      · show (MvFormalGroup.adicEvalAlgHom (R := B) ⊥ hw) ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) g) ∈ ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L)))
        rw [MvFormalGroup.coe_adicEvalAlgHom, hinl]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg)
      · show (MvFormalGroup.adicEvalAlgHom (R := B) ⊥ hw) ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) g) ∈ ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L)))
        rw [MvFormalGroup.coe_adicEvalAlgHom, hinr, hIker g hg, TensorProduct.tmul_zero]
        exact Ideal.zero_mem _
    have h3 := hsub (hmul f hf)
    rw [Ideal.mem_comap, MvFormalGroup.coe_adicEvalAlgHom, hE] at h3
    exact h3
  have hmapI : I.map δ₀ ≤ ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L))) := Ideal.map_le_iff_le_comap.mpr fun f hf => hδI f hf
  have hδIk : ∀ k, ∀ f ∈ I ^ k, δ₀ f ∈ ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L))) ^ k := fun k f hf => by
    have := Ideal.mem_map_of_mem δ₀ hf
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmapI k this
  have hINmap : (I ^ N).map θ = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, hkerθ]
  have hIn : ((I.map θ).map (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L))) ^ N = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow, hINmap, Ideal.map_bot]
  have hvan : ∀ a ∈ I ^ N, δ₀ a = 0 := fun a ha => by
    simpa only [hIn, Ideal.mem_bot] using hδIk N a ha
  have hvan' : RingHom.ker θ.toRingHom ≤ RingHom.ker δ₀.toRingHom := by
    intro a ha
    have ha' : θ a = 0 := RingHom.mem_ker.mp ha
    have ha'' : a ∈ I ^ N := by rw [← hkerθ]; exact RingHom.mem_ker.mpr ha'
    exact RingHom.mem_ker.mpr (hvan a ha'')
  let δ : S →ₐ[B] (S ⊗[B] L) := AlgHom.liftOfSurjective θ hθ δ₀ hvan'
  have hδmk : ∀ G, δ (θ G) = δ₀ G := fun G => AlgHom.liftOfSurjective_apply θ hθ δ₀ hvan' G

  have hA : ∀ i, (Algebra.TensorProduct.assoc B B B S L L) ((Algebra.TensorProduct.map δ (AlgHom.id B L)) ((fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) i)) =
      MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L)))
        (Sum.elim (fun j => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L ⊗[B] L)) (fun j => (1 : S) ⊗ₜ[B] (π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)))) (X.F.toPowerSeries j)) (fun j => (1 : S) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] π (MvPowerSeries.X j))))
        (X.F.toPowerSeries i) := by
    intro i
    show ((Algebra.TensorProduct.assoc B B B S L L).toAlgHom.comp (Algebra.TensorProduct.map δ (AlgHom.id B L))) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) = _
    rw [algHom_adicEval_bot _ _ hw]
    congr 1
    funext t
    rcases t with j | j
    · simp only [Sum.elim_inl, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, map_one]
      rw [hδmk, hδ₀, MvFormalGroup.adicEval_X]
      show ((Algebra.TensorProduct.assoc B B B S L L).toAlgHom.comp (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := (S ⊗[B] L)) (B := L))) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries j)) = _
      rw [algHom_adicEval_bot _ _ hw]
      congr 1
      funext t
      rcases t with l | l
      · show (Algebra.TensorProduct.assoc B B B S L L) ((θ (MvPowerSeries.X l) ⊗ₜ[B] (1 : L)) ⊗ₜ[B] (1 : L)) = _
        rw [Algebra.TensorProduct.assoc_tmul]
        rfl
      · show (Algebra.TensorProduct.assoc B B B S L L) (((1 : S) ⊗ₜ[B] π (MvPowerSeries.X l)) ⊗ₜ[B] (1 : L)) = _
        rw [Algebra.TensorProduct.assoc_tmul]
        rfl
    · simp only [Sum.elim_inr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      show (Algebra.TensorProduct.assoc B B B S L L) ((1 : (S ⊗[B] L)) ⊗ₜ[B] π (MvPowerSeries.X j)) = _
      rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_tmul]

  have hB : ∀ i, (Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.comulAlgHom B L)) ((fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) i) =
      MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L)))
        (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L ⊗[B] L)) (fun j => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))) (Sum.elim (fun j => (1 : S) ⊗ₜ[B] (π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))) (fun j => (1 : S) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))) (X.F.toPowerSeries j)))
        (X.F.toPowerSeries i) := by
    intro i
    show (Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.comulAlgHom B L)) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) = _
    rw [algHom_adicEval_bot _ _ hw]
    congr 1
    funext t
    rcases t with j | j
    · simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    · simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [show Bialgebra.comulAlgHom B L (π (MvPowerSeries.X j)) = Coalgebra.comul (R := B) (π (MvPowerSeries.X j)) from rfl,
        hcomul j]
      have h3 := @algHom_adicEval_bot B (L ⊗[B] L) (S ⊗[B] (L ⊗[B] L)) _ _ _ _ _ (Fin 2 ⊕ Fin 2) _
        (Algebra.TensorProduct.includeRight (R := B) (A := S) (B := L ⊗[B] L)) _ hWL (X.F.toPowerSeries j)
      rw [Algebra.TensorProduct.includeRight_apply] at h3
      refine h3.trans ?_
      congr 1
      funext t
      rcases t with l | l <;> rfl

  have hC : ∀ i, MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L)))
        (Sum.elim (fun j => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L ⊗[B] L)) (fun j => (1 : S) ⊗ₜ[B] (π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)))) (X.F.toPowerSeries j)) (fun j => (1 : S) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] π (MvPowerSeries.X j))))
        (X.F.toPowerSeries i) =
      MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L)))
        (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L ⊗[B] L)) (fun j => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] (L ⊗[B] L))) (Sum.elim (fun j => (1 : S) ⊗ₜ[B] (π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))) (fun j => (1 : S) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))) (X.F.toPowerSeries j)))
        (X.F.toPowerSeries i) := by
    intro i
    let Px : MvFormalGroup.Points X.F (S ⊗[B] (L ⊗[B] L)) ⊥ := ⟨(fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L ⊗[B] L)), hWX⟩
    let Py : MvFormalGroup.Points X.F (S ⊗[B] (L ⊗[B] L)) ⊥ := ⟨(fun j => (1 : S) ⊗ₜ[B] (π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))), hWY⟩
    let Pz : MvFormalGroup.Points X.F (S ⊗[B] (L ⊗[B] L)) ⊥ := ⟨(fun j => (1 : S) ⊗ₜ[B] ((1 : L) ⊗ₜ[B] π (MvPowerSeries.X j))), hWZ⟩
    have key : (Px + Py + Pz).val i = (Px + (Py + Pz)).val i := by rw [add_assoc]
    exact key
  refine ⟨δ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro G
    rw [hδmk, hδ₀]
  ·
    intro s
    obtain ⟨G, rfl⟩ := hθ s
    rw [hδmk, hδ₀]
    have hassoc : ∀ z : (S ⊗[B] L) ⊗[B] L, (_root_.TensorProduct.assoc B S L L) z = (Algebra.TensorProduct.assoc B B B S L L) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul y c =>
          induction y using TensorProduct.induction_on with
          | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
          | tmul a b => rw [TensorProduct.assoc_tmul, Algebra.TensorProduct.assoc_tmul]
          | add u v hu hv => rw [TensorProduct.add_tmul, map_add, map_add, hu, hv]
      | add u v hu hv => rw [map_add, map_add, hu, hv]
    rw [hassoc]
    have hcomp : ∀ z, (Algebra.TensorProduct.assoc B B B S L L) ((Algebra.TensorProduct.map δ (AlgHom.id B L)) z) = ((Algebra.TensorProduct.assoc B B B S L L).toAlgHom.comp (Algebra.TensorProduct.map δ (AlgHom.id B L))) z := fun z => rfl
    rw [hcomp, algHom_adicEval_bot _ _ hptF G, algHom_adicEval_bot _ _ hptF G]
    congr 1
    funext i
    show (Algebra.TensorProduct.assoc B B B S L L) ((Algebra.TensorProduct.map δ (AlgHom.id B L)) ((fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) i)) = (Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.comulAlgHom B L)) ((fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) i)
    rw [hA i, hB i, hC i]
  ·
    intro s
    obtain ⟨G, rfl⟩ := hθ s
    rw [hδmk, hδ₀, algHom_adicEval_bot _ _ hptF G, hmk G]
    show _ = (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := B)) (MvFormalGroup.adicEval (⊥ : Ideal S) (fun j => θ (MvPowerSeries.X j)) G)
    rw [algHom_adicEval_bot _ _ hxbar G]
    congr 1
    funext i
    show (Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.counitAlgHom B L)) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) = _
    rw [algHom_adicEval_bot _ _ hw]
    have hWε : (fun t => (Algebra.TensorProduct.map (AlgHom.id B S) (Bialgebra.counitAlgHom B L)) ((Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) t)) =
        Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : B)) (fun _ => 0) := by
      funext t
      rcases t with j | j
      · simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      · simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        rw [show Bialgebra.counitAlgHom B L (π (MvPowerSeries.X j)) = Coalgebra.counit (R := B) (π (MvPowerSeries.X j)) from rfl,
          hcounit, MvPowerSeries.constantCoeff_X, TensorProduct.tmul_zero]
    rw [hWε]
    let P0 : MvFormalGroup.Points X.F (S ⊗[B] B) ⊥ :=
      ⟨fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : B), fun j => tmul_one_mem_radical_bot (hxbar j)⟩
    have key : (P0 + 0).val i = P0.val i := by rw [add_zero]
    exact key
  ·
    intro k f hf
    rw [hδmk]
    have h1 := hδIk k f hf
    rw [← Ideal.map_pow, ← Ideal.map_pow] at h1
    have hfun : (fun s : S => s ⊗ₜ[B] (1 : L)) = ⇑(Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := S) (B := L)) :=
      funext fun s => (Algebra.TensorProduct.includeLeft_apply s).symm
    rw [hfun]
    exact h1
  ·
    intro qL hqL G
    rw [hδmk, hδ₀, algHom_adicEval_bot _ _ hptF G, hev G,
      show Coalgebra.comul (R := B) (MvFormalGroup.adicEval (⊥ : Ideal L) (fun j => π (MvPowerSeries.X j)) G) =
        Bialgebra.comulAlgHom B L (MvFormalGroup.adicEval (⊥ : Ideal L) (fun j => π (MvPowerSeries.X j)) G) from rfl,
      algHom_adicEval_bot (Bialgebra.comulAlgHom B L) _ hπx G]
    congr 1
    funext i
    rw [show Bialgebra.comulAlgHom B L (π (MvPowerSeries.X i)) = Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) from rfl,
      hcomul i]
    show Algebra.TensorProduct.map qL (AlgHom.id B L) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] π (MvPowerSeries.X j))) (X.F.toPowerSeries i)) = _
    rw [algHom_adicEval_bot _ _ hw]
    congr 1
    funext t
    rcases t with j | j
    · simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [hqL]
    · simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

end

end InvGenB29

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    {L : Type} [CommRing L] [HopfAlgebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hcomul : ∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i))
    (hcounit : ∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ δ : (MvPowerSeries (Fin 2) B ⧸ I ^ N) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L,
      (∀ G, δ (Ideal.Quotient.mk (I ^ N) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ N) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : (MvPowerSeries (Fin 2) B ⧸ I ^ N)) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G) ∧
      (∀ s, (_root_.TensorProduct.assoc B (MvPowerSeries (Fin 2) B ⧸ I ^ N) L L)
          (Algebra.TensorProduct.map δ (AlgHom.id B L) (δ s)) =
        Algebra.TensorProduct.map (AlgHom.id B (MvPowerSeries (Fin 2) B ⧸ I ^ N)) (Bialgebra.comulAlgHom B L) (δ s)) ∧
      (∀ s, Algebra.TensorProduct.map (AlgHom.id B (MvPowerSeries (Fin 2) B ⧸ I ^ N)) (Bialgebra.counitAlgHom B L) (δ s) =
        s ⊗ₜ[B] (1 : B)) ∧
      (∀ (k : ℕ), ∀ f ∈ I ^ k, δ (Ideal.Quotient.mk (I ^ N) f) ∈
        Ideal.span ((fun s : (MvPowerSeries (Fin 2) B ⧸ I ^ N) => s ⊗ₜ[B] (1 : L)) ''
          (((I ^ k).map (Ideal.Quotient.mk (I ^ N))) : Set (MvPowerSeries (Fin 2) B ⧸ I ^ N)))) ∧
      (∀ G, Algebra.TensorProduct.map
            (Ideal.Quotient.liftₐ (I ^ N) π (fun a ha => by
              rw [← RingHom.mem_ker, hker]; exact Ideal.pow_le_self hN ha))
            (AlgHom.id B L) (δ (Ideal.Quotient.mk (I ^ N) G)) =
          Coalgebra.comul (R := B) (π G)) := by
  obtain ⟨δ, h1, h2, h3, h4, h5⟩ := InvGenB29.levelCoaction_aux p X I hnil hmul π hker hπnil hev hcomul hcounit
    (Ideal.Quotient.mkₐ B (I ^ N)) (Ideal.Quotient.mkₐ_surjective B (I ^ N)) N hN (Ideal.Quotient.mkₐ_ker B (I ^ N))
  refine ⟨δ, h1, h2, h3, h4, fun G => h5 _ (fun G => rfl) G⟩

end S_CerednikDrinfeld_FormalODModule_exists_levelCoaction_of_subgroup_ideal_of_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_levelCoaction_of_subgroup_ideal_of_ne_zero (solution)
