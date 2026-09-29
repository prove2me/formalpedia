-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.existsUnique_subst_of_invariant_of_forall_existsUnique_subst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0949bd3f-8425-530b-9277-1a20dff95b60

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_of_invariant_of_forall_existsUnique_subst

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace K2Boot

open MvPowerSeries
open scoped Classical

section Exponents

variable {α β : Type*}

theorem sumElim_ext {f f' : α →₀ ℕ} {g g' : β →₀ ℕ} :
    f.sumElim g = f'.sumElim g' ↔ f = f' ∧ g = g' := by
  constructor
  · intro h
    refine ⟨Finsupp.ext fun x => ?_, Finsupp.ext fun y => ?_⟩
    · have := congrArg (fun D => D (Sum.inl x)) h
      simpa only [Finsupp.sumElim_inl] using this
    · have := congrArg (fun D => D (Sum.inr y)) h
      simpa only [Finsupp.sumElim_inr] using this
  · rintro ⟨rfl, rfl⟩; rfl

noncomputable def fstE (D : α ⊕ β →₀ ℕ) : α →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp D).1
noncomputable def sndE (D : α ⊕ β →₀ ℕ) : β →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp D).2

theorem fstE_apply (D : α ⊕ β →₀ ℕ) (x : α) : fstE D x = D (Sum.inl x) :=
  Finsupp.fst_sumFinsuppEquivProdFinsupp D x
theorem sndE_apply (D : α ⊕ β →₀ ℕ) (y : β) : sndE D y = D (Sum.inr y) :=
  Finsupp.snd_sumFinsuppEquivProdFinsupp D y

theorem sumElim_fstE_sndE (D : α ⊕ β →₀ ℕ) : (fstE D).sumElim (sndE D) = D := by
  ext v
  rcases v with x | y
  · rw [Finsupp.sumElim_inl, fstE_apply]
  · rw [Finsupp.sumElim_inr, sndE_apply]

theorem fstE_sumElim (f : α →₀ ℕ) (g : β →₀ ℕ) : fstE (f.sumElim g) = f := by
  ext x; rw [fstE_apply, Finsupp.sumElim_inl]
theorem sndE_sumElim (f : α →₀ ℕ) (g : β →₀ ℕ) : sndE (f.sumElim g) = g := by
  ext y; rw [sndE_apply, Finsupp.sumElim_inr]

theorem sumElim_add (f f' : α →₀ ℕ) (g g' : β →₀ ℕ) :
    f.sumElim g + f'.sumElim g' = (f + f').sumElim (g + g') := by
  ext v
  rcases v with x | y
  · simp only [Finsupp.add_apply, Finsupp.sumElim_inl]
  · simp only [Finsupp.add_apply, Finsupp.sumElim_inr]

theorem sumElim_le_iff (f f' : α →₀ ℕ) (g g' : β →₀ ℕ) :
    f.sumElim g ≤ f'.sumElim g' ↔ f ≤ f' ∧ g ≤ g' := by
  simp only [Finsupp.le_iff, Finsupp.mem_support_iff, ne_eq]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have := h (Sum.inl x) (by rwa [Finsupp.sumElim_inl])
      simpa only [Finsupp.sumElim_inl] using this
    · have := h (Sum.inr y) (by rwa [Finsupp.sumElim_inr])
      simpa only [Finsupp.sumElim_inr] using this
  · rintro ⟨hf, hg⟩ v hv
    rcases v with x | y
    · simp only [Finsupp.sumElim_inl] at hv ⊢; exact hf x hv
    · simp only [Finsupp.sumElim_inr] at hv ⊢; exact hg y hv

theorem sumElim_tsub (f f' : α →₀ ℕ) (g g' : β →₀ ℕ) :
    f.sumElim g - f'.sumElim g' = (f - f').sumElim (g - g') := by
  ext v
  rcases v with x | y
  · simp only [Finsupp.tsub_apply, Finsupp.sumElim_inl]
  · simp only [Finsupp.tsub_apply, Finsupp.sumElim_inr]

theorem sumElim_zero_zero : (0 : α →₀ ℕ).sumElim (0 : β →₀ ℕ) = 0 := by
  ext v; rcases v with x | y <;> simp

theorem eq_embDomain_inr (g : β →₀ ℕ) :
    (0 : α →₀ ℕ).sumElim g = Finsupp.embDomain Function.Embedding.inr g := by
  ext v
  rcases v with x | y
  · rw [Finsupp.sumElim_inl, Finsupp.embDomain_notin_range]
    · rfl
    · rintro ⟨y, hy⟩; cases hy
  · rw [Finsupp.sumElim_inr]
    exact (Finsupp.embDomain_apply_self Function.Embedding.inr g y).symm

theorem eq_embDomain_inl (f : α →₀ ℕ) :
    f.sumElim (0 : β →₀ ℕ) = Finsupp.embDomain Function.Embedding.inl f := by
  ext v
  rcases v with x | y
  · rw [Finsupp.sumElim_inl]
    exact (Finsupp.embDomain_apply_self Function.Embedding.inl f x).symm
  · rw [Finsupp.sumElim_inr, Finsupp.embDomain_notin_range]
    · rfl
    · rintro ⟨x, hx⟩; cases hx

theorem not_mem_range_mapDomain_inr {f : α →₀ ℕ} (g : β →₀ ℕ) (hf : f ≠ 0) :
    f.sumElim g ∉ Set.range (Finsupp.mapDomain (Sum.inr : β → α ⊕ β)) := by
  rintro ⟨g', hg'⟩
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h; push Not at h; exact hf (Finsupp.ext h)
  have h1 : (Finsupp.mapDomain Sum.inr g') (Sum.inl x : α ⊕ β) = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by rintro ⟨y, hy⟩; cases hy)
  rw [hg', Finsupp.sumElim_inl] at h1
  exact hx h1

theorem not_mem_range_mapDomain_inl (f : α →₀ ℕ) {g : β →₀ ℕ} (hg : g ≠ 0) :
    f.sumElim g ∉ Set.range (Finsupp.mapDomain (Sum.inl : α → α ⊕ β)) := by
  rintro ⟨f', hf'⟩
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra h; push Not at h; exact hg (Finsupp.ext h)
  have h1 : (Finsupp.mapDomain Sum.inl f') (Sum.inr y : α ⊕ β) = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; cases hx)
  rw [hf', Finsupp.sumElim_inr] at h1
  exact hy h1

end Exponents

section Matrix

variable {B : Type*} [CommRing B] {σ τ : Type*}

noncomputable def M (a : σ → MvPowerSeries τ B) (μ : τ →₀ ℕ) (ν : σ →₀ ℕ) : B :=
  coeff μ (ν.prod fun j k => a j ^ k)

theorem M_row_finite {a : σ → MvPowerSeries τ B} (ha : HasSubst a) (μ : τ →₀ ℕ) :
    {ν : σ →₀ ℕ | M a μ ν ≠ 0}.Finite := by
  have h := coeff_subst_finite ha (fun _ => (1 : B) : MvPowerSeries σ B) μ
  refine h.subset fun ν hν => ?_
  simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq, M] at hν ⊢
  rwa [show coeff ν (fun _ => (1 : B) : MvPowerSeries σ B) = 1 from rfl, one_smul]

noncomputable def S {a : σ → MvPowerSeries τ B} (ha : HasSubst a) (μ : τ →₀ ℕ) :
    Finset (σ →₀ ℕ) := (M_row_finite ha μ).toFinset

theorem mem_S {a : σ → MvPowerSeries τ B} (ha : HasSubst a) {μ : τ →₀ ℕ} {ν : σ →₀ ℕ} :
    ν ∈ S ha μ ↔ M a μ ν ≠ 0 := by
  rw [S, Set.Finite.mem_toFinset]; rfl

theorem coeff_subst_eq_sum {a : σ → MvPowerSeries τ B} (ha : HasSubst a) (f : MvPowerSeries σ B) (μ : τ →₀ ℕ) :
    coeff μ (subst a f) = ∑ ν ∈ S ha μ, M a μ ν * coeff ν f := by
  rw [coeff_subst ha f μ]
  have hsupp : (Function.support fun ν : σ →₀ ℕ => coeff ν f • coeff μ (ν.prod fun s e => a s ^ e)) ⊆
      (S ha μ : Finset (σ →₀ ℕ)) := by
    intro ν hν
    rw [Finset.mem_coe, mem_S]
    intro h0
    apply hν
    show coeff ν f • coeff μ (ν.prod fun s e => a s ^ e) = 0
    rw [show coeff μ (ν.prod fun s e => a s ^ e) = M a μ ν from rfl, h0, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [smul_eq_mul, mul_comm]; rfl

theorem prod_X_pow_eq_monomial {σ' τ' : Type*} (ι : σ' → τ') (ε : σ' →₀ ℕ) (E : τ' →₀ ℕ)
    (hE : ∀ t, E t = ∑ s ∈ ε.support, if ι s = t then ε s else 0) :
    (ε.prod fun s k => (X (ι s) : MvPowerSeries τ' B) ^ k) = monomial E 1 := by
  have hE' : E = ∑ s ∈ ε.support, Finsupp.single (ι s) (ε s) := by
    ext t
    rw [hE, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.single_apply]
  rw [hE', Finsupp.prod]
  induction ε.support using Finset.induction_on with
  | empty => simp
  | insert s T hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs, ih, X_pow_eq, monomial_mul_monomial, one_mul]

end Matrix

section Param

variable {B : Type*} [CommRing B] {ω σ τ : Type*}

noncomputable def θF (ω : Type*) (a : σ → MvPowerSeries τ B) : σ ⊕ ω → MvPowerSeries (τ ⊕ ω) B :=
  Sum.elim (fun k => subst (fun j => (X (Sum.inl j) : MvPowerSeries (τ ⊕ ω) B)) (a k)) (fun t => X (Sum.inr t))

theorem θF_def (ω : Type*) (a : σ → MvPowerSeries τ B) :
    θF ω a = Sum.elim (fun k => subst (fun j => (X (Sum.inl j) : MvPowerSeries (τ ⊕ ω) B)) (a k))
      (fun t => X (Sum.inr t)) := rfl

theorem θF_inl (a : σ → MvPowerSeries τ B) (k : σ) :
    θF ω a (Sum.inl k) = rename (⇑(Function.Embedding.inl : τ ↪ τ ⊕ ω)) (a k) := by
  rw [θF, Sum.elim_inl, rename_eq_subst]; rfl

theorem hasSubst_θF [Finite σ] [Finite ω] {a : σ → MvPowerSeries τ B} (ha0 : ∀ k, constantCoeff (a k) = 0) :
    HasSubst (θF ω a) := by
  refine hasSubst_of_constantCoeff_zero fun v => ?_
  rcases v with k | t
  · rw [θF_inl, constantCoeff_rename, ha0]
  · rw [θF, Sum.elim_inr, constantCoeff_X]

theorem coeff_prod_θF (a : σ → MvPowerSeries τ B) (δ δ' : ω →₀ ℕ) (ν : σ →₀ ℕ) (μ : τ →₀ ℕ) :
    coeff (μ.sumElim δ') ((ν.sumElim δ).prod fun v k => θF ω a v ^ k) = if δ = δ' then M a μ ν else 0 := by
  rw [Finsupp.prod_sumElim, mul_comm]
  have h1 : (δ.prod ((fun v k => θF ω a v ^ k) ∘ Sum.inr)) = monomial ((0 : τ →₀ ℕ).sumElim δ) 1 := by
    have : ((fun v k => θF ω a v ^ k) ∘ Sum.inr) = fun t k => (X (Sum.inr t) : MvPowerSeries (τ ⊕ ω) B) ^ k := by
      funext t k; simp [θF]
    rw [this]
    refine prod_X_pow_eq_monomial Sum.inr δ _ fun t => ?_
    rcases t with j | w
    · rw [Finsupp.sumElim_inl]
      simp
    · rw [Finsupp.sumElim_inr]
      simp only [Sum.inr.injEq, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
      by_cases h : δ w = 0 <;> simp [h]
  have h2 : (ν.prod ((fun v k => θF ω a v ^ k) ∘ Sum.inl)) =
      rename (⇑(Function.Embedding.inl : τ ↪ τ ⊕ ω)) (ν.prod fun j k => a j ^ k) := by
    rw [Finsupp.prod, Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, map_pow, θF_inl]
  rw [h1, h2, coeff_monomial_mul, one_mul]
  by_cases h : δ = δ'
  · subst h
    have hle : (0 : τ →₀ ℕ).sumElim δ ≤ μ.sumElim δ := (sumElim_le_iff _ _ _ _).mpr ⟨bot_le (a := μ), le_rfl⟩
    rw [if_pos hle, if_pos rfl, sumElim_tsub, tsub_self, tsub_zero, eq_embDomain_inl, coeff_embDomain_rename]
    rfl
  · rw [if_neg h]
    by_cases hle : (0 : τ →₀ ℕ).sumElim δ ≤ μ.sumElim δ'
    · rw [if_pos hle, sumElim_tsub, tsub_zero]
      apply coeff_rename_eq_zero
      have hle' : δ ≤ δ' := ((sumElim_le_iff _ _ _ _).mp hle).2
      have hne : δ' - δ ≠ 0 := fun h0 => h (le_antisymm hle' (tsub_eq_zero_iff_le.mp h0))
      exact not_mem_range_mapDomain_inl μ hne
    · rw [if_neg hle]

def slice (w : MvPowerSeries (σ ⊕ ω) B) (β : ω →₀ ℕ) : MvPowerSeries σ B := fun α => coeff (α.sumElim β) w

theorem coeff_slice (w : MvPowerSeries (σ ⊕ ω) B) (β : ω →₀ ℕ) (α : σ →₀ ℕ) :
    coeff α (slice w β) = coeff (α.sumElim β) w := rfl

theorem slice_sub (w w' : MvPowerSeries (σ ⊕ ω) B) (β : ω →₀ ℕ) : slice (w - w') β = slice w β - slice w' β := by
  ext α; simp only [coeff_slice, map_sub]

theorem slice_sum {κ : Type*} (s : Finset κ) (w : κ → MvPowerSeries (σ ⊕ ω) B) (β : ω →₀ ℕ) :
    slice (∑ k ∈ s, w k) β = ∑ k ∈ s, slice (w k) β := by
  ext α; simp only [coeff_slice, map_sum]

theorem eq_of_slice_eq {w w' : MvPowerSeries (σ ⊕ ω) B} (h : ∀ β, slice w β = slice w' β) : w = w' := by
  ext D
  have := congrArg (coeff (fstE D)) (h (sndE D))
  rwa [coeff_slice, coeff_slice, sumElim_fstE_sndE] at this

noncomputable def ofSlices (φ : (ω →₀ ℕ) → MvPowerSeries σ B) : MvPowerSeries (σ ⊕ ω) B :=
  fun D => coeff (fstE D) (φ (sndE D))

theorem slice_ofSlices (φ : (ω →₀ ℕ) → MvPowerSeries σ B) (β : ω →₀ ℕ) : slice (ofSlices φ) β = φ β := by
  ext α
  rw [coeff_slice]
  show coeff (fstE (α.sumElim β)) (φ (sndE (α.sumElim β))) = _
  rw [fstE_sumElim, sndE_sumElim]

theorem slice_subst_θF [Finite σ] [Finite ω] {a : σ → MvPowerSeries τ B} (ha0 : ∀ k, constantCoeff (a k) = 0)
    (w : MvPowerSeries (σ ⊕ ω) B) (β : ω →₀ ℕ) :
    slice (subst (θF ω a) w) β = subst a (slice w β) := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  ext μ
  rw [coeff_slice, coeff_subst_eq_sum ha, coeff_subst (hasSubst_θF ha0) w]
  have hsupp : (Function.support fun D : σ ⊕ ω →₀ ℕ =>
      coeff D w • coeff (μ.sumElim β) (D.prod fun v k => θF ω a v ^ k)) ⊆
      ((S ha μ).image fun ν => ν.sumElim β : Finset (σ ⊕ ω →₀ ℕ)) := by
    intro D hD
    rw [Function.mem_support, ← sumElim_fstE_sndE D, coeff_prod_θF] at hD
    rw [Finset.coe_image, Set.mem_image]
    by_cases h : sndE D = β
    · refine ⟨fstE D, ?_, by rw [← h, sumElim_fstE_sndE]⟩
      rw [Finset.mem_coe, mem_S]
      rw [if_pos h] at hD
      exact fun h0 => hD (by rw [h0, smul_zero])
    · rw [if_neg h, smul_zero] at hD
      exact (hD rfl).elim
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image fun ν _ ν' _ h => (sumElim_ext.mp h).1]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_prod_θF, if_pos rfl, smul_eq_mul, mul_comm, coeff_slice]

theorem slice_mul_rename (h : MvPowerSeries (σ ⊕ ω) B) (g : MvPowerSeries σ B) (β : ω →₀ ℕ) :
    slice (h * rename (⇑(Function.Embedding.inl : σ ↪ σ ⊕ ω)) g) β = slice h β * g := by
  ext α
  rw [coeff_slice, coeff_mul, coeff_mul]
  let Φ : (σ →₀ ℕ) × (σ →₀ ℕ) → ((σ ⊕ ω →₀ ℕ) × (σ ⊕ ω →₀ ℕ)) :=
    fun c => (c.1.sumElim β, c.2.sumElim (0 : ω →₀ ℕ))
  have hΦinj : Function.Injective Φ := by
    intro c c' hcc
    simp only [Φ, Prod.mk.injEq, sumElim_ext] at hcc
    exact Prod.ext hcc.1.1 hcc.2.1
  have himage : (Finset.HasAntidiagonal.antidiagonal α).image Φ ⊆ Finset.HasAntidiagonal.antidiagonal (α.sumElim β) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc ⊢
    simp only [Φ, sumElim_add, add_zero, hc]
  have hcoeff : ∀ (e : σ →₀ ℕ) (δ : ω →₀ ℕ), coeff (e.sumElim δ) (rename (⇑(Function.Embedding.inl : σ ↪ σ ⊕ ω)) g) =
      if δ = 0 then coeff e g else 0 := by
    intro e δ
    split_ifs with hδ
    · rw [hδ, eq_embDomain_inl, coeff_embDomain_rename]
    · exact coeff_rename_eq_zero _ _ (not_mem_range_mapDomain_inl e hδ)
  rw [← Finset.sum_subset himage, Finset.sum_image fun c _ c' _ hcc => hΦinj hcc]
  · refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Φ, coeff_slice, hcoeff, if_true]
  · intro p hp hnot
    by_cases hz : sndE p.2 = 0
    · exfalso
      apply hnot
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [Finset.mem_image]
      rw [← sumElim_fstE_sndE p.1, ← sumElim_fstE_sndE p.2, sumElim_add, sumElim_ext, hz, add_zero] at hp
      refine ⟨(fstE p.1, fstE p.2), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact hp.1
      · apply Prod.ext
        · show (fstE p.1).sumElim β = p.1
          conv_rhs => rw [← sumElim_fstE_sndE p.1]
          rw [hp.2]
        · show (fstE p.2).sumElim 0 = p.2
          conv_rhs => rw [← sumElim_fstE_sndE p.2]
          rw [hz]
    · rw [← sumElim_fstE_sndE p.2, hcoeff, if_neg hz, mul_zero]

end Param

section YSlices

variable {B : Type*} [CommRing B]

theorem slice_mem_of_mem_span {n : ℕ} (I : Ideal (MvPowerSeries (Fin 2) B))
    {V : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B}
    (hV : V ∈ Ideal.span ((MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))))
    (β : Fin n →₀ ℕ) :
    slice V β ∈ Ideal.span ((MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))) := by
  obtain ⟨N, r, g, hsum⟩ := Submodule.mem_span_set'.mp hV
  rw [← hsum, slice_sum]
  refine Ideal.sum_mem _ fun k _ => ?_
  obtain ⟨i, hi, hgi⟩ := (g k).2
  have h1 : ((g k : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B)) =
      rename (⇑(Function.Embedding.inl : (Fin 2 ⊕ Fin 2) ↪ (Fin 2 ⊕ Fin 2) ⊕ Fin n))
        (rename (⇑(Function.Embedding.inr : Fin 2 ↪ Fin 2 ⊕ Fin 2)) i) := by
    rw [← hgi, rename_rename, rename_eq_subst]; rfl
  rw [smul_eq_mul, h1, slice_mul_rename]
  refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, ?_⟩)
  rw [rename_eq_subst]; rfl

end YSlices

end K2Boot

open MvPowerSeries K2Boot in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (u : Series B) (hu0 : ∀ j, MvPowerSeries.constantCoeff (u j) = 0)
    (hcoord : ∀ w : MvPowerSeries (Fin 2) B,
      MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2) B, MvPowerSeries.subst u W = w) :
    ∀ (n : ℕ) (w : MvPowerSeries (Fin 2 ⊕ Fin n) B),
      MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst
              (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
                (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
              (X.F.toPowerSeries j))
            (fun t => MvPowerSeries.X (Sum.inr t))) w -
        MvPowerSeries.subst
          (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
            (fun t => MvPowerSeries.X (Sum.inr t))) w ∈
        Ideal.span ((MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) →
      ∃! W : MvPowerSeries (Fin 2 ⊕ Fin n) B,
        MvPowerSeries.subst
          (Sum.elim
            (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin n) B)) (u j))
            (fun t => MvPowerSeries.X (Sum.inr t))) W = w := by
  classical
  intro n w hw
  have hF0 : ∀ j, constantCoeff (X.F.toPowerSeries j) = 0 := X.F.constantCoeff_eq_zero
  have hX0 : ∀ l : Fin 2, constantCoeff ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
    fun l => constantCoeff_X _

  have hA : (Sum.elim
      (fun j => MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
          (fun l => MvPowerSeries.X (Sum.inl (Sum.inr l))))
        (X.F.toPowerSeries j))
      (fun t => MvPowerSeries.X (Sum.inr t)) : Fin 2 ⊕ Fin n → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B) =
      θF (Fin n) X.F.toPowerSeries := by
    rw [θF_def]
    congr 1
    funext j
    congr 1
    funext l
    cases l with
    | inl a => rfl
    | inr b => rfl
  have hE : (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl (Sum.inl l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))
      (fun t => MvPowerSeries.X (Sum.inr t)) : Fin 2 ⊕ Fin n → MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B) =
      θF (Fin n) (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) := by
    rw [θF_def]
    congr 1
    funext l
    exact (subst_X (hasSubst_of_constantCoeff_zero fun j => constantCoeff_X _) (Sum.inl l)).symm
  have hw' : subst (θF (Fin n) X.F.toPowerSeries) w -
      subst (θF (Fin n) (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) w ∈
      Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin 2 ⊕ Fin 2) ⊕ Fin n) B))) ''
          (I : Set (MvPowerSeries (Fin 2) B))) := by
    rw [← hA, ← hE]
    exact hw

  have hslice : ∀ β : Fin n →₀ ℕ,
      MvPowerSeries.subst X.F.toPowerSeries (slice w β) -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (slice w β) ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
        (I : Set (MvPowerSeries (Fin 2) B))) := by
    intro β
    have h := slice_mem_of_mem_span I hw' β
    rwa [slice_sub, slice_subst_θF hF0, slice_subst_θF hX0] at h

  choose Wβ hWβ hWβu using fun β => hcoord (slice w β) (hslice β)
  refine ⟨ofSlices Wβ, ?_, ?_⟩
  · show subst (θF (Fin n) u) (ofSlices Wβ) = w
    refine eq_of_slice_eq fun β => ?_
    rw [slice_subst_θF hu0, slice_ofSlices, hWβ]
  · intro W' hW'
    change subst (θF (Fin n) u) W' = w at hW'
    refine eq_of_slice_eq fun β => ?_
    rw [slice_ofSlices]
    refine hWβu β (slice W' β) ?_
    show subst u (slice W' β) = slice w β
    rw [← slice_subst_θF hu0, hW']

end S_CerednikDrinfeld_FormalODModule_existsUnique_subst_of_invariant_of_forall_existsUnique_subst
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_of_invariant_of_forall_existsUnique_subst (solution)
