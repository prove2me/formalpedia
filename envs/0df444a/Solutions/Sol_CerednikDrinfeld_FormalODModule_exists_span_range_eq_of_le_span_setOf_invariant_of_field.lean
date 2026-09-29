-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_span_range_eq_of_le_span_setOf_invariant_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2f2d72f5-9fb8-5c84-b2cd-5418ddefb272

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant
import Theorems.Thm_IsLocalRing_exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_span_range_eq_of_le_span_setOf_invariant_of_field

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace QB2Top

open MvPowerSeries

variable {κ : Type} [Field κ]

theorem mem_span_X_pow {σ : Type} [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ κ, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ κ) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ κ := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ κ) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ κ) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ κ) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ κ) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ κ) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

theorem mem_span_range_X_of_constantCoeff {n : ℕ} {f : MvPowerSeries (Fin n) κ}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) κ)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

theorem constantCoeff_subst_of_constantCoeff_zero {m n : ℕ} (u : Fin m → MvPowerSeries (Fin n) κ)
    (hu0 : ∀ j, constantCoeff (u j) = 0) (W : MvPowerSeries (Fin m) κ) :
    constantCoeff (subst u W) = constantCoeff W := by
  have hu := hasSubst_of_constantCoeff_zero hu0
  have hW' : constantCoeff (W - C (constantCoeff W)) = 0 := by
    rw [map_sub, constantCoeff_C, sub_self]
  have h0 : constantCoeff (subst u (W - C (constantCoeff W))) = 0 :=
    constantCoeff_subst_eq_zero hu hu0 hW'
  have hsplit : subst u W = subst u (W - C (constantCoeff W)) + C (constantCoeff W) := by
    rw [subst_sub hu, subst_C, sub_add_cancel]
  rw [hsplit, map_add, h0, constantCoeff_C, zero_add]

end QB2Top

open MvPowerSeries QB2Top in
theorem solution
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ]
    (X : FormalODModule p κ) (I : Ideal (MvPowerSeries (Fin 2) κ))
    (hfin : Module.Finite κ (MvPowerSeries (Fin 2) κ ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
    (hgen : I ≤ Ideal.span {w : MvPowerSeries (Fin 2) κ | w ∈ I ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))) '' (I : Set (MvPowerSeries (Fin 2) κ)))}) :
    ∃ u : Series κ,
      (∀ j, MvPowerSeries.constantCoeff (u j) = 0) ∧
      (∀ j, MvPowerSeries.subst X.F.toPowerSeries (u j) - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (u j) ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))) '' (I : Set (MvPowerSeries (Fin 2) κ)))) ∧
      Ideal.span (Set.range u) = I := by
  classical

  let A := MvPowerSeries (Fin 2) κ
  let Inv : MvPowerSeries (Fin 2) κ → Prop := fun w =>
    MvPowerSeries.subst X.F.toPowerSeries w -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) w ∈
      Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))) ''
        (I : Set (MvPowerSeries (Fin 2) κ)))
  have hInv0 : Inv 0 := by
    have h1 : MvPowerSeries.subst X.F.toPowerSeries (0 : A) = 0 := by
      rw [← coe_substAlgHom X.F.hasSubst_toPowerSeries, map_zero]
    have h2 : MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (0 : A) = 0 := by
      rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero
        (a := fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))
        fun l => constantCoeff_X _), map_zero]
    show MvPowerSeries.subst X.F.toPowerSeries (0 : A) -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (0 : A) ∈ _
    rw [h1, h2, sub_self]
    exact Ideal.zero_mem _

  haveI : IsNoetherianRing A := MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing κ 2
  let S : Set A := {w : A | w ∈ I ∧ Inv w}
  have hSI : Ideal.span S = I := by
    refine le_antisymm ?_ hgen
    rw [Ideal.span_le]
    exact fun w hw => hw.1
  obtain ⟨T, hTS, hTspan⟩ : ∃ T : Finset A, (T : Set A) ⊆ S ∧ Ideal.span (T : Set A) = I := by
    obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
    have hmem : ∀ g ∈ G, ∃ Tg : Finset A, (Tg : Set A) ⊆ S ∧ g ∈ Ideal.span (Tg : Set A) := by
      intro g hg
      have : g ∈ Ideal.span S := by rw [hSI, ← hG]; exact Submodule.subset_span hg
      exact Submodule.mem_span_finite_of_mem_span this
    choose Tg hTgS hTg using hmem
    refine ⟨G.attach.biUnion fun g => Tg g.1 g.2, ?_, ?_⟩
    · intro w hw
      obtain ⟨g, -, hwg⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hw)
      exact hTgS g.1 g.2 hwg
    · refine le_antisymm ?_ ?_
      · rw [← hSI]
        refine Ideal.span_mono fun w hw => ?_
        obtain ⟨g, -, hwg⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hw)
        exact hTgS g.1 g.2 hwg
      · rw [← hG, Ideal.span_le]
        intro g hg
        refine Ideal.span_mono ?_ (hTg g hg)
        intro w hw
        exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨g, hg⟩, Finset.mem_attach _ _, hw⟩)

  let m := T.card
  let eT : (T : Set A) ≃ Fin m := T.equivFin
  let u₀ : Fin m → A := fun j => (eT.symm j : A)
  have hu₀T : ∀ j, u₀ j ∈ (T : Set A) := fun j => (eT.symm j).2
  have hu₀S : ∀ j, u₀ j ∈ S := fun j => hTS (hu₀T j)
  have hu₀0 : ∀ j, constantCoeff (u₀ j) = 0 := fun j => hunit _ (hu₀S j).1
  have hu₀inv : ∀ j, Inv (u₀ j) := fun j => (hu₀S j).2
  have hrange : Set.range u₀ = (T : Set A) := by
    ext w
    constructor
    · rintro ⟨j, rfl⟩; exact hu₀T j
    · intro hw; exact ⟨eT ⟨w, hw⟩, by simp [u₀]⟩
  have hu₀I : Ideal.span (Set.range u₀) = I := by rw [hrange, hTspan]

  haveI : Module.Finite κ (A ⧸ I) := hfin
  let bC := Module.finBasis κ (A ⧸ I)
  choose b hb using fun k => Ideal.Quotient.mk_surjective (bC k)
  obtain ⟨hexp, hind⟩ :=
    CerednikDrinfeld.FormalODModule.exists_eq_sum_subst_mul_and_subst_eq_zero_of_invariant
      p X I hnil bC b hb u₀ hu₀0 hu₀inv hu₀I

  have hu₀s : HasSubst u₀ := hasSubst_of_constantCoeff_zero hu₀0
  let θ : MvPowerSeries (Fin m) κ →ₐ[κ] A := substAlgHom hu₀s
  have hθ : ∀ c, θ c = subst u₀ c := fun c => by
    show substAlgHom hu₀s c = _
    rw [coe_substAlgHom]
  let R : Subalgebra κ A := θ.range
  let θr : MvPowerSeries (Fin m) κ →ₐ[κ] R := θ.rangeRestrict
  have hθr : ∀ c, (θr c : A) = θ c := fun c => rfl
  have hθr_surj : Function.Surjective θr := by
    rintro ⟨y, c, rfl⟩
    exact ⟨c, rfl⟩
  haveI : IsNoetherianRing (MvPowerSeries (Fin m) κ) := MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing κ m
  haveI : IsNoetherianRing R := isNoetherianRing_of_surjective _ _ θr.toRingHom hθr_surj
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h : (0 : A) = 1)⟩⟩
  haveI : IsLocalRing R := IsLocalRing.of_surjective' θr.toRingHom hθr_surj

  have hccθ : ∀ c, constantCoeff (θ c) = constantCoeff c := fun c => by
    rw [hθ]; exact constantCoeff_subst_of_constantCoeff_zero u₀ hu₀0 c
  have hunitR : ∀ r : R, IsUnit r ↔ constantCoeff (r : A) ≠ 0 := by
    intro r
    constructor
    · intro hr h0
      obtain ⟨r', hr'⟩ := hr.exists_right_inv
      have := congrArg (fun z : R => constantCoeff (z : A)) hr'
      simp only [Subalgebra.coe_mul, map_mul, h0, zero_mul, Subalgebra.coe_one, map_one] at this
      exact zero_ne_one this
    · intro h
      obtain ⟨c, rfl⟩ := hθr_surj r
      have hc : IsUnit c := by
        rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, ← hccθ]
        exact h
      exact hc.map θr
  have hmaxR : ∀ r : R, r ∈ IsLocalRing.maximalIdeal R ↔ constantCoeff (r : A) = 0 := by
    intro r
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunitR, not_not]

  have hsmul : ∀ (r : R) (a : A), r • a = (r : A) * a := fun r a => Subalgebra.smul_def r a
  have hli : LinearIndependent R b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hgc : ∀ k, ∃ c, θ c = (g k : A) := fun k => by
      obtain ⟨c, hc⟩ := hθr_surj (g k)
      exact ⟨c, by rw [← hθr, hc]⟩
    choose c hc using hgc
    have hsum : ∑ k, subst u₀ (c k) * b k = 0 := by
      rw [← hg]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsmul, ← hc, hθ]
    have := hind c hsum k
    apply Subtype.ext
    show (g k : A) = 0
    rw [← hc, hθ, this]
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := by
    rintro f -
    obtain ⟨c, hc⟩ := hexp f
    rw [hc]
    refine Submodule.sum_mem _ fun k _ => ?_
    have : subst u₀ (c k) * b k = (θr (c k)) • b k := by rw [hsmul, hθr, hθ]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bR : Module.Basis (Fin (Module.finrank κ (A ⧸ I))) R A := Module.Basis.mk hli hsp

  let s : Fin m → R := fun i => θr (MvPowerSeries.X i)
  have hsval : ∀ i, (s i : A) = u₀ i := fun i => by
    show θ (MvPowerSeries.X i) = u₀ i
    exact substAlgHom_X hu₀s i
  have hs : Ideal.span (Set.range s) = IsLocalRing.maximalIdeal R := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hmaxR, hsval]
      exact hu₀0 i
    · intro r hr
      rw [hmaxR] at hr
      obtain ⟨c, rfl⟩ := hθr_surj r
      have hc0 : constantCoeff c = 0 := by rw [← hccθ]; exact hr
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (mem_span_range_X_of_constantCoeff hc0)
      rw [← hg, map_sum]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

  obtain ⟨t, htcard, htspan⟩ :=
    IsLocalRing.exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries bR s hs
  have hIt : Ideal.span (u₀ '' (t : Set (Fin m))) = I := by
    refine le_antisymm ?_ ?_
    · rw [← hu₀I]
      exact Ideal.span_mono (Set.image_subset_range _ _)
    · rw [← hu₀I, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hsi : s i ∈ Ideal.span (s '' (t : Set (Fin m))) := by
        rw [htspan, ← hs]
        exact Ideal.subset_span ⟨i, rfl⟩
      have := Ideal.mem_map_of_mem (algebraMap R A) hsi
      rw [Ideal.map_span, ← Set.image_comp] at this
      have heq : (⇑(algebraMap R A) ∘ s) = u₀ := funext fun i => hsval i
      rw [heq] at this
      rw [SetLike.mem_coe, ← hsval i]
      exact this

  have htc : t.card ≤ 2 := htcard
  let et : (t : Set (Fin m)) ≃ Fin t.card := t.equivFin
  let u : Series κ := fun j =>
    if h : (j : ℕ) < t.card then u₀ (et.symm ⟨j, h⟩ : Fin m) else 0
  have hu_cases : ∀ j, u j = 0 ∨ ∃ i ∈ (t : Set (Fin m)), u j = u₀ i := by
    intro j
    by_cases h : (j : ℕ) < t.card
    · right
      refine ⟨(et.symm ⟨j, h⟩ : Fin m), (et.symm ⟨j, h⟩).2, ?_⟩
      simp only [u, dif_pos h]
    · left; simp only [u, dif_neg h]
  have hrange_sub : Set.range u ⊆ insert 0 (u₀ '' (t : Set (Fin m))) := by
    rintro _ ⟨j, rfl⟩
    rcases hu_cases j with h | ⟨i, hi, h⟩
    · rw [h]; exact Set.mem_insert _ _
    · rw [h]; exact Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩
  have himage_sub : u₀ '' (t : Set (Fin m)) ⊆ Set.range u := by
    rintro _ ⟨i, hi, rfl⟩
    let j : Fin t.card := et ⟨i, hi⟩
    have hj : (j : ℕ) < t.card := j.2
    refine ⟨⟨j, lt_of_lt_of_le hj htc⟩, ?_⟩
    show (if h : ((⟨j, lt_of_lt_of_le hj htc⟩ : Fin 2) : ℕ) < t.card then u₀ (et.symm ⟨_, h⟩ : Fin m) else 0) = u₀ i
    rw [dif_pos hj]
    have : et.symm ⟨(j : ℕ), hj⟩ = ⟨i, hi⟩ := by
      rw [Equiv.symm_apply_eq]
    rw [this]
  refine ⟨u, fun j => ?_, fun j => ?_, ?_⟩
  · rcases hu_cases j with h | ⟨i, -, h⟩
    · rw [h, map_zero]
    · rw [h]; exact hu₀0 i
  · rcases hu_cases j with h | ⟨i, -, h⟩
    · rw [h]; exact hInv0
    · rw [h]; exact hu₀inv i
  · refine le_antisymm ?_ ?_
    · rw [← hIt]
      refine (Ideal.span_mono hrange_sub).trans (le_of_eq ?_)
      exact Submodule.span_insert_zero
    · rw [← hIt]
      exact Ideal.span_mono himage_sub

end S_CerednikDrinfeld_FormalODModule_exists_span_range_eq_of_le_span_setOf_invariant_of_field
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_span_range_eq_of_le_span_setOf_invariant_of_field (solution)
