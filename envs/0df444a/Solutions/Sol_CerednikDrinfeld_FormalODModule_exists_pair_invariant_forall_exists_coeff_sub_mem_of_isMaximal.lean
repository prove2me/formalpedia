-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5ae0af38-cec6-5a36-a975-76de3253c685

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_span_range_eq_of_le_span_setOf_invariant_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_map_mem_setOf_invariant_of_mem
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped BigOperators TensorProduct

namespace QB3K

open MvPowerSeries

variable {R : Type} [CommRing R]

theorem mem_span_X_pow {σ : Type} [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
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
    let f₀ : MvPowerSeries σ R := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ R) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ R) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

theorem mem_span_range_X_of_constantCoeff {n : ℕ} {f : MvPowerSeries (Fin n) R}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

theorem map_surjective {σ : Type} {S : Type} [CommRing S] (π : R →+* S) (hπ : Function.Surjective π) :
    Function.Surjective (MvPowerSeries.map (σ := σ) π) := by
  intro g
  choose pre hpre using fun e : σ →₀ ℕ => hπ (coeff e g)
  refine ⟨fun e => pre e, ?_⟩
  ext e
  rw [coeff_map]
  exact hpre e

theorem exists_of_mem_span_X_mul {n : ℕ} (K : Ideal (MvPowerSeries (Fin n) R)) {z : MvPowerSeries (Fin n) R}
    (hz : z ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) * K) :
    ∃ h : Fin n → MvPowerSeries (Fin n) R, (∀ i, h i ∈ K) ∧ z = ∑ i, X i * h i := by
  classical
  refine Submodule.mul_induction_on hz (fun m hm k hk => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
    refine ⟨fun i => c i * k, fun i => K.mul_mem_left _ hk, ?_⟩
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; ring
  · obtain ⟨h, hh, rfl⟩ := hx
    obtain ⟨h', hh', rfl⟩ := hy
    refine ⟨h + h', fun i => K.add_mem (hh i) (hh' i), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]

theorem mul_sub_C_mul_mem {n : ℕ} (K : Ideal (MvPowerSeries (Fin n) R)) (g w : MvPowerSeries (Fin n) R)
    (hw : w ∈ K) :
    g * w - C (constantCoeff g) * w ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) * K := by
  rw [← sub_mul]
  refine Ideal.mul_mem_mul ?_ hw
  exact mem_span_range_X_of_constantCoeff (by rw [map_sub, constantCoeff_C, sub_self])

end QB3K

open MvPowerSeries QB3K in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R]
    (X : FormalODModule p R) (J : Ideal (MvPowerSeries (Fin 2) R))
    (hfin : Module.Finite R (MvPowerSeries (Fin 2) R ⧸ J))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ q ∈ J)
    (hunit : ∀ f ∈ J, MvPowerSeries.constantCoeff f = 0)
    (hInv : J = Ideal.span {w : MvPowerSeries (Fin 2) R | w ∈ J ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))})
    (𝔫 : Ideal R) (h𝔫 : 𝔫.IsMaximal) :
    ∃ r : Fin 2 → MvPowerSeries (Fin 2) R,
      (∀ j, r j ∈ {w : MvPowerSeries (Fin 2) R | w ∈ J ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) '' (J : Set (MvPowerSeries (Fin 2) R)))}) ∧
      ∀ f ∈ J, ∃ (a b : Fin 2 → MvPowerSeries (Fin 2) R), (∀ i, b i ∈ J) ∧
        ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (f - (∑ j, a j * r j + ∑ i, MvPowerSeries.X i * b i)) ∈ 𝔫 := by
  classical

  haveI : 𝔫.IsMaximal := h𝔫
  let κ := R ⧸ 𝔫
  letI : Field κ := Ideal.Quotient.field 𝔫
  let π : R →+* κ := Ideal.Quotient.mk 𝔫
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let A := MvPowerSeries (Fin 2) R
  let Aκ := MvPowerSeries (Fin 2) κ
  let πx : A →+* Aκ := MvPowerSeries.map π
  have hπx : Function.Surjective πx := map_surjective π hπ
  let Jκ : Ideal Aκ := J.map πx

  let Inv : Set A := {w : A | w ∈ J ∧
      MvPowerSeries.subst X.F.toPowerSeries w -
          MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) w ∈
        Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))) ''
          (J : Set A))}
  let Invκ : Set Aκ := {w : Aκ | w ∈ Jκ ∧
      MvPowerSeries.subst (X.map π).F.toPowerSeries w -
          MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) w ∈
        Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ))) ''
          (Jκ : Set Aκ))}
  have hInvJ : ∀ w ∈ Inv, w ∈ J := fun w hw => hw.1
  have hmapInv : ∀ w ∈ Inv, πx w ∈ Invκ := fun w hw =>
    CerednikDrinfeld.FormalODModule.map_mem_setOf_invariant_of_mem p X J π w hw

  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) R) := MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing R 2
  obtain ⟨k, φ, hφ0⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  have hφ : Ideal.span (Set.range φ) = J := hφ0
  have hJκ_span : Jκ = Ideal.span (Set.range fun i => MvPowerSeries.map π (φ i)) := by
    show Ideal.map πx J = _
    rw [← hφ, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨q, hq⟩ := hnil
  have hN : ∃ N : ℕ, ∀ s : Fin 2, (MvPowerSeries.X s : A) ^ N ∈ Ideal.span (Set.range φ) :=
    ⟨q, fun s => by rw [hφ]; exact hq s⟩
  have hfinκ : Module.Finite κ (Aκ ⧸ Jκ) := by
    letI : Algebra R κ := π.toAlgebra
    haveI : Module.Finite R (MvPowerSeries (Fin 2) R ⧸ Ideal.span (Set.range φ)) := by rw [hφ]; exact hfin
    obtain ⟨e, -⟩ :=
      MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ) φ hN
    haveI : Module.Finite κ (κ ⊗[R] (MvPowerSeries (Fin 2) R ⧸ Ideal.span (Set.range φ))) :=
      Module.Finite.base_change R κ (MvPowerSeries (Fin 2) R ⧸ Ideal.span (Set.range φ))
    have h1 : Module.Finite κ (Aκ ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R κ) (φ i))) :=
      Module.Finite.equiv e.toLinearEquiv
    have heq : Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R κ) (φ i)) = Jκ := by
      rw [hJκ_span]
      rfl
    exact Module.Finite.equiv (Ideal.quotientEquivAlgOfEq κ heq).toLinearEquiv
  have hnilκ : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : Aκ) ^ q ∈ Jκ :=
    ⟨q, fun i => by
      have := Ideal.mem_map_of_mem πx (hq i)
      rwa [map_pow, show πx (MvPowerSeries.X i) = MvPowerSeries.X i from map_X π i] at this⟩
  have hunitκ : ∀ f ∈ Jκ, MvPowerSeries.constantCoeff f = 0 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective πx hπx).mp hf
    show MvPowerSeries.constantCoeff (MvPowerSeries.map π g) = 0
    rw [constantCoeff_map, hunit g hg, map_zero]
  have hJInv : J = Ideal.span Inv := hInv
  have hJκInv : Jκ = Ideal.span (πx '' Inv) := by
    show Ideal.map πx J = _
    conv_lhs => rw [hJInv]
    rw [Ideal.map_span]
  have hgenκ : Jκ ≤ Ideal.span Invκ := by
    rw [hJκInv]
    refine Ideal.span_mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hmapInv w hw

  obtain ⟨u, -, -, huJ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_span_range_eq_of_le_span_setOf_invariant_of_field
      p (X.map π) Jκ hfinκ hnilκ hunitκ hgenκ

  let W₁ : Ideal Aκ := Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → Aκ)) * Jκ
  let Wκ : Submodule κ Aκ := Jκ.restrictScalars κ
  let W₁κ : Submodule κ Wκ := (W₁.restrictScalars κ).comap Wκ.subtype
  let Q := Wκ ⧸ W₁κ
  let cls : Wκ →ₗ[κ] Q := W₁κ.mkQ
  have hlin : ∀ (n : ℕ) (c : Fin n → κ) (y : Fin n → Wκ), ∑ k, c k • cls (y k) = cls (∑ k, c k • y k) := by
    intro n c y
    rw [map_sum]
    simp only [map_smul]
  have hcls0 : ∀ y : Wκ, cls y = 0 ↔ (y : Aκ) ∈ W₁ := by
    intro y
    show W₁κ.mkQ y = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [W₁κ, Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem]

  have huW : ∀ j, u j ∈ Jκ := fun j => by rw [← huJ]; exact Ideal.subset_span ⟨j, rfl⟩
  have hQu : ∀ z : Wκ, ∃ c : Fin 2 → κ, cls z = ∑ j, c j • cls ⟨u j, huW j⟩ := by
    intro z
    have hz : (z : Aκ) ∈ Ideal.span (Set.range u) := by rw [huJ]; exact z.2
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hz
    refine ⟨fun j => MvPowerSeries.constantCoeff (g j), ?_⟩
    rw [hlin, ← sub_eq_zero, ← map_sub, hcls0, Submodule.coe_sub, Submodule.coe_sum]
    have : ((z : Aκ) - ∑ j, ((MvPowerSeries.constantCoeff (g j) • (⟨u j, huW j⟩ : Wκ) : Wκ) : Aκ)) =
        ∑ j, (g j * u j - MvPowerSeries.C (MvPowerSeries.constantCoeff (g j)) * u j) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [← hg]; exact Finset.sum_congr rfl fun j _ => smul_eq_mul _ _
      · exact Finset.sum_congr rfl fun j _ => by rw [Submodule.coe_smul]; exact smul_eq_C_mul _ _
    rw [this]
    exact W₁.sum_mem fun j _ => mul_sub_C_mul_mem Jκ (g j) (u j) (huW j)
  haveI : Module.Finite κ Q := by
    refine Module.finite_def.mpr ⟨{cls ⟨u 0, huW 0⟩, cls ⟨u 1, huW 1⟩}, ?_⟩
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective W₁κ x
    obtain ⟨c, hc⟩ := hQu z
    rw [show W₁κ.mkQ z = cls z from rfl, hc, Fin.sum_univ_two]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · simp
    · simp
  have hrank : Module.finrank κ Q ≤ 2 := by
    have h := finrank_span_finset_le_card (R := κ) ({cls ⟨u 0, huW 0⟩, cls ⟨u 1, huW 1⟩} : Finset Q)
    have htop : Submodule.span κ (({cls ⟨u 0, huW 0⟩, cls ⟨u 1, huW 1⟩} : Finset Q) : Set Q) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective W₁κ x
      obtain ⟨c, hc⟩ := hQu z
      rw [show W₁κ.mkQ z = cls z from rfl, hc, Fin.sum_univ_two]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
        (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      · simp
      · simp
    unfold Set.finrank at h
    rw [htop, finrank_top] at h
    exact h.trans Finset.card_le_two

  have hπxInvW : ∀ w ∈ Inv, πx w ∈ Jκ := fun w hw => Ideal.mem_map_of_mem πx (hInvJ w hw)
  let G : Set Q := (fun w : {w // w ∈ Inv} => cls ⟨πx w.1, hπxInvW w.1 w.2⟩) '' Set.univ
  have hGspan : Submodule.span κ G = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective W₁κ x
    have hz : (z : Aκ) ∈ Ideal.span (πx '' Inv) := by rw [← hJκInv]; exact z.2
    obtain ⟨n, g, ws, hsum⟩ := Submodule.mem_span_set'.mp hz

    have hwk : ∀ k, ∃ w ∈ Inv, πx w = (ws k : Aκ) := fun k => (ws k).2
    choose w hwInv hw using hwk
    have hcls : W₁κ.mkQ z = ∑ k, MvPowerSeries.constantCoeff (g k) • cls ⟨πx (w k), hπxInvW (w k) (hwInv k)⟩ := by
      rw [hlin, show W₁κ.mkQ z = cls z from rfl, ← sub_eq_zero, ← map_sub, hcls0, Submodule.coe_sub,
        Submodule.coe_sum]
      have : ((z : Aκ) - ∑ k, ((MvPowerSeries.constantCoeff (g k) •
          (⟨πx (w k), hπxInvW (w k) (hwInv k)⟩ : Wκ) : Wκ) : Aκ)) =
          ∑ k, (g k * (ws k : Aκ) - MvPowerSeries.C (MvPowerSeries.constantCoeff (g k)) * (ws k : Aκ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        · rw [← hsum]; exact Finset.sum_congr rfl fun k _ => smul_eq_mul _ _
        · exact Finset.sum_congr rfl fun k _ => by
            rw [Submodule.coe_smul]
            show MvPowerSeries.constantCoeff (g k) • πx (w k) = _
            rw [hw k]
            exact smul_eq_C_mul _ _
      rw [this]
      refine W₁.sum_mem fun k _ => mul_sub_C_mul_mem Jκ (g k) (ws k) ?_
      rw [← hw k]
      exact hπxInvW (w k) (hwInv k)
    rw [hcls]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨w k, hwInv k⟩, Set.mem_univ _, rfl⟩

  obtain ⟨t, htG, htspan, htli⟩ := exists_linearIndependent κ G
  haveI : Finite t := htli.finite
  let tF := Fintype.ofFinite t
  have htcard : Fintype.card t ≤ 2 := (htli.fintype_card_le_finrank).trans hrank

  have hrep : ∀ x : t, ∃ w : {w // w ∈ Inv}, cls ⟨πx w.1, hπxInvW w.1 w.2⟩ = (x : Q) := by
    intro x
    obtain ⟨w, -, hx⟩ := htG x.2
    exact ⟨w, hx⟩
  choose repw hrepw using hrep
  let rep : t → A := fun x => (repw x).1
  have hrepInv : ∀ x, rep x ∈ Inv := fun x => (repw x).2
  have hrep_cls : ∀ x : t, cls ⟨πx (rep x), hπxInvW _ (hrepInv x)⟩ = (x : Q) := fun x => hrepw x
  have hInv0 : (0 : A) ∈ Inv := by
    refine ⟨J.zero_mem, ?_⟩
    have h1 : MvPowerSeries.subst X.F.toPowerSeries (0 : A) = 0 := by
      rw [← coe_substAlgHom X.F.hasSubst_toPowerSeries, map_zero]
    have h2 : MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) (0 : A) = 0 := by
      rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero
        (a := fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R))
        fun l => constantCoeff_X _), map_zero]
    show MvPowerSeries.subst X.F.toPowerSeries (0 : A) -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) (0 : A) ∈ _
    rw [h1, h2, sub_self]
    exact Ideal.zero_mem _

  let et : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let r : Fin 2 → A := fun j => if h : (j : ℕ) < Fintype.card t then rep (et.symm ⟨j, h⟩) else 0
  have hr_cases : ∀ j, r j = 0 ∨ ∃ x : t, r j = rep x := by
    intro j
    by_cases h : (j : ℕ) < Fintype.card t
    · right; exact ⟨et.symm ⟨j, h⟩, by simp only [r, dif_pos h]⟩
    · left; simp only [r, dif_neg h]
  have hrInv : ∀ j, r j ∈ Inv := by
    intro j
    rcases hr_cases j with h | ⟨x, h⟩
    · rw [h]; exact hInv0
    · rw [h]; exact hrepInv x

  have hrJκ : ∀ j, πx (r j) ∈ Jκ := fun j => hπxInvW _ (hrInv j)
  let v : Fin 2 → Q := fun j => cls ⟨πx (r j), hrJκ j⟩
  have htv : t ⊆ Set.range v := by
    intro x hx
    let j := et ⟨x, hx⟩
    have hj2 : (j : ℕ) < 2 := lt_of_lt_of_le j.2 htcard
    refine ⟨⟨j, hj2⟩, ?_⟩
    have hrj : r ⟨j, hj2⟩ = rep ⟨x, hx⟩ := by
      show (if h : ((⟨j, hj2⟩ : Fin 2) : ℕ) < Fintype.card t then rep (et.symm ⟨_, h⟩) else 0) = rep ⟨x, hx⟩
      rw [dif_pos j.2]
      congr 1
      rw [Equiv.symm_apply_eq]
    have : (⟨πx (r ⟨j, hj2⟩), hrJκ ⟨j, hj2⟩⟩ : Wκ) = ⟨πx (rep ⟨x, hx⟩), hπxInvW _ (hrepInv ⟨x, hx⟩)⟩ :=
      Subtype.ext (by show πx (r ⟨j, hj2⟩) = πx (rep ⟨x, hx⟩); rw [hrj])
    show cls ⟨πx (r ⟨j, hj2⟩), hrJκ ⟨j, hj2⟩⟩ = x
    rw [this, hrep_cls]
  have hQr : ∀ z : Wκ, ∃ c : Fin 2 → κ, cls z = ∑ j, c j • v j := by
    intro z
    have hz : cls z ∈ Submodule.span κ (Set.range v) := by
      refine Submodule.span_mono htv ?_
      rw [htspan, hGspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun κ).mp hz
    exact ⟨c, hc.symm⟩

  refine ⟨r, hrInv, fun f hf => ?_⟩
  have hfκ : πx f ∈ Jκ := Ideal.mem_map_of_mem πx hf
  obtain ⟨c, hc⟩ := hQr ⟨πx f, hfκ⟩
  have hmem : πx f - ∑ j, MvPowerSeries.C (c j) * πx (r j) ∈ W₁ := by
    have h0 : cls (⟨πx f, hfκ⟩ - ∑ j, c j • ⟨πx (r j), hrJκ j⟩) = 0 := by
      rw [map_sub, ← hlin, sub_eq_zero]
      exact hc
    rw [hcls0, Submodule.coe_sub, Submodule.coe_sum] at h0
    have : (∑ j, ((c j • (⟨πx (r j), hrJκ j⟩ : Wκ) : Wκ) : Aκ)) = ∑ j, MvPowerSeries.C (c j) * πx (r j) :=
      Finset.sum_congr rfl fun j _ => by rw [Submodule.coe_smul]; exact smul_eq_C_mul _ _
    rwa [this] at h0
  obtain ⟨h, hhJ, hh⟩ := exists_of_mem_span_X_mul Jκ hmem
  choose a₀ ha₀ using fun j => hπ (c j)
  have hbex : ∀ i, ∃ b ∈ J, πx b = h i := fun i => (Ideal.mem_map_iff_of_surjective πx hπx).mp (hhJ i)
  choose b hbJ hb using hbex
  refine ⟨fun j => MvPowerSeries.C (a₀ j), b, hbJ, fun d => ?_⟩
  have hzero : πx (f - (∑ j, MvPowerSeries.C (a₀ j) * r j + ∑ i, MvPowerSeries.X i * b i)) = 0 := by
    rw [map_sub, map_add, map_sum, map_sum]
    have h1 : ∀ j, πx (MvPowerSeries.C (a₀ j) * r j) = MvPowerSeries.C (c j) * πx (r j) := fun j => by
      rw [map_mul]
      congr 1
      show MvPowerSeries.map π (MvPowerSeries.C (a₀ j)) = _
      rw [map_C, ha₀]
    have h2 : ∀ i, πx (MvPowerSeries.X i * b i) = MvPowerSeries.X i * h i := fun i => by
      rw [map_mul, hb]
      congr 1
      exact map_X π i
    simp only [h1, h2]
    rw [← hh]
    ring
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (MvPowerSeries.coeff d) hzero
  rw [coeff_zero] at this
  rw [← this]
  exact (MvPowerSeries.coeff_map _ _ _).symm

end S_CerednikDrinfeld_FormalODModule_exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_pair_invariant_forall_exists_coeff_sub_mem_of_isMaximal (solution)
