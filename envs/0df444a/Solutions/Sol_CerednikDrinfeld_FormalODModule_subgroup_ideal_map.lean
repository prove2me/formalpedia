-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.subgroup_ideal_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c917b351-377e-5bfa-88dd-917548b05c07

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_subgroup_ideal_map

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries

namespace B26Q

noncomputable def lowExp (q : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  ((Finset.range q) ×ˢ (Finset.range q)).image fun ab => Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2

theorem mem_lowExp {q : ℕ} {e : Fin 2 →₀ ℕ} : e ∈ lowExp q ↔ e 0 < q ∧ e 1 < q := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
      Finsupp.single_eq_of_ne, add_zero, zero_ne_one, zero_add]
    exact hab
  · rintro ⟨h0, h1⟩
    refine Finset.mem_image.2 ⟨(e 0, e 1), Finset.mem_product.2 ⟨Finset.mem_range.2 h0, Finset.mem_range.2 h1⟩, ?_⟩
    ext i
    fin_cases i <;> simp

noncomputable def low {A : Type} [CommRing A] (q : ℕ) (f : MvPowerSeries (Fin 2) A) : MvPowerSeries (Fin 2) A :=
  ∑ e ∈ lowExp q, coeff e f • monomial e (1 : A)

theorem coeff_low {A : Type} [CommRing A] (q : ℕ) (f : MvPowerSeries (Fin 2) A) (e : Fin 2 →₀ ℕ) :
    coeff e (low q f) = if e ∈ lowExp q then coeff e f else 0 := by
  rw [low, map_sum]
  simp only [map_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

theorem exists_decomp {A : Type} [CommRing A] (q : ℕ) (f : MvPowerSeries (Fin 2) A) :
    ∃ g₀ g₁ : MvPowerSeries (Fin 2) A, f = X 0 ^ q * g₀ + X 1 ^ q * g₁ + low q f := by
  let g₀ : MvPowerSeries (Fin 2) A := fun e => coeff (e + Finsupp.single 0 q) f
  let g₁ : MvPowerSeries (Fin 2) A := fun e => if e 0 < q then coeff (e + Finsupp.single 1 q) f else 0
  refine ⟨g₀, g₁, ?_⟩
  ext e
  rw [map_add, map_add, X_pow_eq, X_pow_eq, coeff_monomial_mul, coeff_monomial_mul, coeff_low, one_mul, one_mul]
  have hg₀ : ∀ e', coeff e' g₀ = coeff (e' + Finsupp.single 0 q) f := fun _ => rfl
  have hg₁ : ∀ e' : Fin 2 →₀ ℕ, coeff e' g₁ = if e' 0 < q then coeff (e' + Finsupp.single 1 q) f else 0 := fun _ => rfl
  by_cases h0 : q ≤ e 0
  ·
    have hs : Finsupp.single (0 : Fin 2) q ≤ e := by
      intro i; fin_cases i <;> simp [h0]
    rw [if_pos hs, hg₀, tsub_add_cancel_of_le hs]
    have hne : e ∉ lowExp q := fun h => (not_lt.2 h0) (mem_lowExp.1 h).1
    rw [if_neg hne, add_zero]
    by_cases h1 : Finsupp.single (1 : Fin 2) q ≤ e
    · rw [if_pos h1, hg₁, tsub_add_cancel_of_le h1]
      have : ¬ (e - Finsupp.single (1 : Fin 2) q) 0 < q := by simp; omega
      rw [if_neg this, add_zero]
    · rw [if_neg h1, add_zero]
  · push Not at h0
    have hs : ¬ Finsupp.single (0 : Fin 2) q ≤ e := fun h => by
      have := h 0; simp at this; omega
    rw [if_neg hs, zero_add]
    by_cases h1 : q ≤ e 1
    · have hs1 : Finsupp.single (1 : Fin 2) q ≤ e := by
        intro i; fin_cases i <;> simp [h1]
      rw [if_pos hs1, hg₁, tsub_add_cancel_of_le hs1]
      have : (e - Finsupp.single (1 : Fin 2) q) 0 < q := by simp; omega
      rw [if_pos this]
      have hne : e ∉ lowExp q := fun h => (not_lt.2 h1) (mem_lowExp.1 h).2
      rw [if_neg hne, add_zero]
    · push Not at h1
      have hs1 : ¬ Finsupp.single (1 : Fin 2) q ≤ e := fun h => by
        have := h 1; simp at this; omega
      rw [if_neg hs1, zero_add, if_pos (mem_lowExp.2 ⟨h0, h1⟩)]

end B26Q

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries

namespace B26Q

section clauses

variable {p : ℕ} [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
  (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))

theorem map_induction {P : MvPowerSeries (Fin 2) B' → Prop}
    (hmem : ∀ g ∈ I, P (MvPowerSeries.map φ g)) (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hmul : ∀ (c f : MvPowerSeries (Fin 2) B'), P f → P (c * f)) :
    ∀ f ∈ I.map (MvPowerSeries.map φ), P f := by
  intro f hf
  change f ∈ Ideal.span _ at hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨g, hg, rfl⟩ := hx; exact hmem g hg
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hmul c x hx

theorem nil_clause (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I) :
    ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B') ^ q ∈ I.map (MvPowerSeries.map φ) := by
  obtain ⟨q, hq⟩ := hnil
  refine ⟨q, fun i => ?_⟩
  have := Ideal.mem_map_of_mem (MvPowerSeries.map φ) (hq i)
  rwa [map_pow, map_X] at this

theorem unit_clause (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) :
    ∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.constantCoeff f = 0 := by
  refine map_induction φ I (fun g hg => ?_) (map_zero _) (fun f g hf hg => by rw [map_add, hf, hg, add_zero])
    (fun c f hf => by rw [map_mul, hf, mul_zero])
  rw [constantCoeff_map, hunit g hg, map_zero]

theorem subst_clause (s : Series B) (hs0 : ∀ j, constantCoeff (s j) = 0)
    (hstab : ∀ f ∈ I, MvPowerSeries.subst s f ∈ I) :
    ∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst (s.map φ) f ∈ I.map (MvPowerSeries.map φ) := by
  have hS : HasSubst s := hasSubst_of_constantCoeff_zero hs0
  have hS' : HasSubst (s.map φ) :=
    hasSubst_of_constantCoeff_zero fun j => by show constantCoeff (MvPowerSeries.map φ (s j)) = 0; rw [constantCoeff_map, hs0, map_zero]
  refine map_induction φ I (fun g hg => ?_) ?_ (fun f g hf hg => ?_) (fun c f hf => ?_)
  · have : MvPowerSeries.subst (s.map φ) (MvPowerSeries.map φ g) = MvPowerSeries.map φ (MvPowerSeries.subst s g) := by
      rw [map_subst hS]; rfl
    rw [this]
    exact Ideal.mem_map_of_mem _ (hstab g hg)
  · rw [← coe_substAlgHom hS', map_zero]; exact Submodule.zero_mem _
  · rw [subst_add hS']; exact Ideal.add_mem _ hf hg
  · rw [subst_mul hS']; exact Ideal.mul_mem_left _ _ hf

theorem mul_clause
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))) :
    ∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst (X.map φ).F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
            (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B')) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
            (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B'))) := by
  have hF : HasSubst X.F.toPowerSeries := X.F.hasSubst_toPowerSeries
  have hF' : HasSubst (X.map φ).F.toPowerSeries := (X.map φ).F.hasSubst_toPowerSeries
  have hFmap : ∀ i, (X.map φ).F.toPowerSeries i = MvPowerSeries.map φ (X.F.toPowerSeries i) := fun i => rfl
  have hinl : HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hinr : HasSubst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine map_induction φ I (fun g hg => ?_) ?_ (fun f g hf hg => ?_) (fun c f hf => ?_)
  · have e1 : MvPowerSeries.subst (X.map φ).F.toPowerSeries (MvPowerSeries.map φ g) =
        MvPowerSeries.map φ (MvPowerSeries.subst X.F.toPowerSeries g) := by
      rw [map_subst hF]; rfl
    rw [e1]

    have key : Ideal.map (MvPowerSeries.map φ)
        (Ideal.span
          ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
           (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))) ≤
        Ideal.span
          ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
              (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B')) ∪
           (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
              (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B'))) := by
      rw [Ideal.map_span]
      apply Ideal.span_mono
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with ⟨g', hg', rfl⟩ | ⟨g', hg', rfl⟩
      · left
        refine ⟨MvPowerSeries.map φ g', Ideal.mem_map_of_mem _ hg', ?_⟩
        rw [map_subst hinl]
        congr 1
        funext l; exact (map_X _ _).symm
      · right
        refine ⟨MvPowerSeries.map φ g', Ideal.mem_map_of_mem _ hg', ?_⟩
        rw [map_subst hinr]
        congr 1
        funext l; exact (map_X _ _).symm
    exact key (Ideal.mem_map_of_mem _ (hmul g hg))
  · rw [← coe_substAlgHom hF', map_zero]; exact Submodule.zero_mem _
  · rw [subst_add hF']; exact Ideal.add_mem _ hf hg
  · rw [subst_mul hF']; exact Ideal.mul_mem_left _ _ hf

theorem rank_clause (h : ℕ)
    (hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h) :
    ∀ (κ : Type) [Field κ] (f : B' →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I.map (MvPowerSeries.map φ)).map (MvPowerSeries.map f)) = p ^ h := by
  intro κ _ f
  have : (I.map (MvPowerSeries.map φ)).map (MvPowerSeries.map f) = I.map (MvPowerSeries.map (f.comp φ)) := by
    rw [Ideal.map_map, ← map_comp]
  rw [this]
  exact hrank κ (f.comp φ)

end clauses

end B26Q

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries
open scoped TensorProduct

namespace B26Q

section fp

variable {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (I : Ideal (MvPowerSeries (Fin 2) B))

theorem low_sub_mem {A : Type} [CommRing A] (q : ℕ) (J : Ideal (MvPowerSeries (Fin 2) A))
    (hq : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) ^ q ∈ J) (f : MvPowerSeries (Fin 2) A) :
    f - low q f ∈ J := by
  obtain ⟨g₀, g₁, hf⟩ := exists_decomp q f
  nth_rw 1 [hf]
  rw [add_sub_cancel_right]
  exact J.add_mem (J.mul_mem_right _ (hq 0)) (J.mul_mem_right _ (hq 1))

theorem coeff_X_pow_mul_of_lt {A : Type} [CommRing A] (q : ℕ) (i : Fin 2) (g : MvPowerSeries (Fin 2) A)
    (e : Fin 2 →₀ ℕ) (he : e i < q) : coeff e (X i ^ q * g) = 0 := by
  rw [X_pow_eq, coeff_monomial_mul, if_neg]
  intro h
  have := h i
  simp at this
  omega

theorem finite_projective_clause
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I)) (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I) :
    Module.Finite B' (MvPowerSeries (Fin 2) B' ⧸ I.map (MvPowerSeries.map φ)) ∧
    Module.Projective B' (MvPowerSeries (Fin 2) B' ⧸ I.map (MvPowerSeries.map φ)) := by
  letI : Algebra B B' := φ.toAlgebra
  obtain ⟨q, hq⟩ := hnil
  set I' : Ideal (MvPowerSeries (Fin 2) B') := I.map (MvPowerSeries.map φ) with hI'
  have hq' : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B') ^ q ∈ I' := by
    intro i; have := Ideal.mem_map_of_mem (MvPowerSeries.map φ) (hq i); rwa [map_pow, map_X] at this
  haveI := hfin; haveI := hproj

  let N := MvPowerSeries (Fin 2) B ⧸ I
  let T' : MvPowerSeries (Fin 2) B' →ₗ[B'] B' ⊗[B] N :=
    ∑ e ∈ lowExp q, (LinearMap.toSpanSingleton B' (B' ⊗[B] N) ((1 : B') ⊗ₜ[B] Submodule.Quotient.mk (monomial e (1 : B)))).comp
      (coeff e)
  have hT' : ∀ f, T' f = ∑ e ∈ lowExp q, coeff e f • ((1 : B') ⊗ₜ[B] (Submodule.Quotient.mk (monomial e (1 : B)) : N)) := by
    intro f
    simp only [T', LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]

  have hTmap : ∀ g : MvPowerSeries (Fin 2) B, T' (MvPowerSeries.map φ g) = (1 : B') ⊗ₜ[B] (Submodule.Quotient.mk g : N) := by
    intro g
    rw [hT']
    have : ∀ e ∈ lowExp q, coeff e (MvPowerSeries.map φ g) • ((1 : B') ⊗ₜ[B] (Submodule.Quotient.mk (monomial e (1 : B)) : N)) =
        (1 : B') ⊗ₜ[B] (Submodule.Quotient.mk (coeff e g • monomial e (1 : B)) : N) := by
      intro e _
      rw [coeff_map, Submodule.Quotient.mk_smul, TensorProduct.tmul_smul, ← algebraMap_smul B' (coeff e g)]
      rfl
    rw [Finset.sum_congr rfl this, ← TensorProduct.tmul_sum]
    congr 1
    simp only [← Submodule.mkQ_apply]
    rw [← map_sum]
    change I.mkQ (low q g) = I.mkQ g
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]
    exact low_sub_mem q I hq g

  have hTX : ∀ (i : Fin 2) (g : MvPowerSeries (Fin 2) B'), T' (X i ^ q * g) = 0 := by
    intro i g
    rw [hT']
    refine Finset.sum_eq_zero fun e he => ?_
    have hei : e i < q := by
      rcases mem_lowExp.1 he with ⟨h0, h1⟩
      fin_cases i <;> assumption
    rw [coeff_X_pow_mul_of_lt q i g e hei, zero_smul]

  have hTI : ∀ f ∈ I', T' f = 0 := by
    have key : ∀ f ∈ I', ∀ c : MvPowerSeries (Fin 2) B', T' (c * f) = 0 := by
      refine map_induction φ I (fun g hg c => ?_) (fun c => by rw [mul_zero, map_zero])
        (fun f g hf hg c => by rw [mul_add, map_add, hf, hg, add_zero]) (fun c' f hf c => by rw [← mul_assoc]; exact hf _)
      obtain ⟨c₀, c₁, hc⟩ := exists_decomp q c
      rw [hc, add_mul, add_mul, map_add, map_add, mul_assoc, mul_assoc, hTX, hTX, zero_add, zero_add, low, Finset.sum_mul,
        map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hm : (monomial e (1 : B') : MvPowerSeries (Fin 2) B') = MvPowerSeries.map φ (monomial e 1) := by
        rw [map_monomial, RingHom.map_one]
      rw [smul_mul_assoc, map_smul, hm, ← map_mul, hTmap, (Submodule.Quotient.mk_eq_zero I).2 (I.mul_mem_left _ hg),
        TensorProduct.tmul_zero, smul_zero]
    intro f hf
    have := key f hf 1
    rwa [one_mul] at this

  have hker : I'.restrictScalars B' ≤ LinearMap.ker T' := fun f hf => (LinearMap.mem_ker).2 (hTI f hf)
  let Tbar : (MvPowerSeries (Fin 2) B' ⧸ I') →ₗ[B'] B' ⊗[B] N :=
    ((I'.restrictScalars B').liftQ T' hker).comp (Submodule.Quotient.restrictScalarsEquiv B' I').symm.toLinearMap
  have hTbar : ∀ f, Tbar (Ideal.Quotient.mk I' f) = T' f := fun f => rfl

  let mapA : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2) B' :=
    { toRingHom := MvPowerSeries.map φ
      commutes' := fun b => by
        show MvPowerSeries.map φ (algebraMap B _ b) = algebraMap B _ b
        rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_C]
        rfl }
  have hle : I ≤ I'.comap mapA := fun g hg => Ideal.mem_comap.2 (Ideal.mem_map_of_mem (MvPowerSeries.map φ) hg)
  let ι : N →ₐ[B] (MvPowerSeries (Fin 2) B' ⧸ I') := Ideal.quotientMapₐ I' mapA hle
  have hι : ∀ g, ι (Ideal.Quotient.mk I g) = Ideal.Quotient.mk I' (MvPowerSeries.map φ g) := fun g => rfl
  let S : B' ⊗[B] N →ₗ[B'] (MvPowerSeries (Fin 2) B' ⧸ I') := ι.toLinearMap.liftBaseChange B'
  have hS : ∀ (b' : B') (g : MvPowerSeries (Fin 2) B),
      S (b' ⊗ₜ[B] (Submodule.Quotient.mk g : N)) = b' • Ideal.Quotient.mk I' (MvPowerSeries.map φ g) := fun b' g => rfl

  have h1 : ∀ y, S (Tbar y) = y := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hTbar, hT', map_sum]
    have : ∀ e ∈ lowExp q, S (coeff e f • ((1 : B') ⊗ₜ[B] (Submodule.Quotient.mk (monomial e (1 : B)) : N))) =
        Ideal.Quotient.mkₐ B' I' (coeff e f • monomial e (1 : B')) := by
      intro e _
      rw [map_smul, hS, one_smul, map_monomial, RingHom.map_one, map_smul]
      rfl
    rw [Finset.sum_congr rfl this, ← map_sum]
    change Ideal.Quotient.mk I' (low q f) = Ideal.Quotient.mk I' f
    rw [eq_comm, Ideal.Quotient.eq]
    exact low_sub_mem q I' hq' f

  have h2 : ∀ z, Tbar (S z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b' n =>
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective I n
      rw [hS, map_smul]
      change b' • Tbar (Ideal.Quotient.mk I' (MvPowerSeries.map φ g)) = _
      rw [hTbar, hTmap, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let eqv : (MvPowerSeries (Fin 2) B' ⧸ I') ≃ₗ[B'] B' ⊗[B] N :=
    LinearEquiv.ofLinear Tbar S (LinearMap.ext h2) (LinearMap.ext h1)
  haveI : Module.Projective B' (B' ⊗[B] N) := inferInstance
  exact ⟨Module.Finite.equiv eqv.symm, Module.Projective.of_equiv eqv.symm⟩

end fp

end B26Q

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B)) (h : ℕ)

    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h)

    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)

    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))

    (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
    (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
    {B' : Type} [CommRing B'] (φ : B →+* B') :
    Module.Finite B' (MvPowerSeries (Fin 2) B' ⧸ I.map (MvPowerSeries.map φ)) ∧
    Module.Projective B' (MvPowerSeries (Fin 2) B' ⧸ I.map (MvPowerSeries.map φ)) ∧
    (∀ (κ : Type) [Field κ] (f : B' →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I.map (MvPowerSeries.map φ)).map (MvPowerSeries.map f)) = p ^ h) ∧
    (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B') ^ q ∈ I.map (MvPowerSeries.map φ)) ∧
    (∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.constantCoeff f = 0) ∧
    (∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst (X.map φ).F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
            (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B')) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
            (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B')))) ∧
    (∀ (a : Zp2 p), ∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst ((X.map φ).act a) f ∈ I.map (MvPowerSeries.map φ)) ∧
    (∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst (X.map φ).varpi f ∈ I.map (MvPowerSeries.map φ)) := by
  have h12 := B26Q.finite_projective_clause φ I hfin hproj hnil
  refine ⟨h12.1, h12.2, B26Q.rank_clause φ I h hrank, B26Q.nil_clause φ I hnil, B26Q.unit_clause φ I hunit,
    B26Q.mul_clause φ X I hmul, fun a => ?_, ?_⟩
  · exact B26Q.subst_clause φ I (X.act a) (X.isLawHom_act a).1 (hact a)
  · exact B26Q.subst_clause φ I X.varpi X.isLawHom_varpi.1 hvarpi

end S_CerednikDrinfeld_FormalODModule_subgroup_ideal_map
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_subgroup_ideal_map (solution)
