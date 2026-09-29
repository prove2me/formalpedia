-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_span_setOf_invariant_of_subgroup_ideal_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/64770b1f-79fb-5633-b48c-a80e0180a597

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_levelCoaction_of_subgroup_ideal_of_ne_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_sub_mem_and_firstOrder_invariant
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_mem_pow_and_invariant_succ
import Theorems.Thm_MvPowerSeries_mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_span_setOf_invariant_of_subgroup_ideal_of_free

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

noncomputable section

namespace FgPowSpanX

open MvPowerSeries (coeff)

variable {σ : Type} [Fintype σ] [DecidableEq σ] {B : Type} [CommRing B]

theorem mem_span_X_pow_of_coeff_eq_zero (N : ℕ) (s : Finset σ) :
    ∀ G : MvPowerSeries σ B, (∀ d : σ →₀ ℕ, (∀ j ∈ s, d j < N) → coeff d G = 0) →
      G ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ B) ^ N) := by
  induction s using Finset.induction_on with
  | empty =>
    intro G hG
    have : G = 0 := MvPowerSeries.ext fun d => by
      rw [hG d (fun j hj => absurd hj (Finset.notMem_empty j)), map_zero]
    rw [this]; exact Ideal.zero_mem _
  | insert j s hjs ih =>
    intro G hG
    let G₁ : MvPowerSeries σ B := fun d => if d j < N then coeff d G else 0
    have hG₁ : ∀ d, coeff d G₁ = if d j < N then coeff d G else 0 := fun d => rfl
    have h1 : G₁ ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ B) ^ N) := by
      apply ih
      intro d hd
      rw [hG₁]
      split_ifs with hdj
      · exact hG d (fun j' hj' => by
          rcases Finset.mem_insert.mp hj' with rfl | hj'
          · exact hdj
          · exact hd j' hj')
      · rfl
    have h2 : G - G₁ ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ B) ^ N) := by
      have hdvd : (MvPowerSeries.X j : MvPowerSeries σ B) ^ N ∣ G - G₁ := by
        rw [MvPowerSeries.X_pow_dvd_iff]
        intro m hm
        rw [map_sub, hG₁, if_pos hm, sub_self]
      obtain ⟨q, hq⟩ := hdvd
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : G = G₁ + (G - G₁) := by abel
    rw [this]
    exact Ideal.add_mem _ h1 h2

theorem sub_trunc_mem_span_X_pow (q : ℕ) (G : MvPowerSeries σ B) :
    G - ↑(MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm (fun _ : σ => q)) G) ∈
      Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ B) ^ (q + 1)) := by
  refine mem_span_X_pow_of_coeff_eq_zero (q + 1) Finset.univ _ fun d hd => ?_
  have hle : d ≤ Finsupp.equivFunOnFinite.symm (fun _ : σ => q) := fun j => by
    have := hd j (Finset.mem_univ j); simp; omega
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]

theorem coeff_trunc'_ne_zero_le (q : ℕ) (G : MvPowerSeries σ B) (d : σ →₀ ℕ)
    (hd : d ∈ (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm (fun _ : σ => q)) G).support) :
    ∀ j, d j ≤ q := by
  rw [MvPolynomial.mem_support_iff, MvPowerSeries.coeff_trunc'] at hd
  split_ifs at hd with h
  · intro j; have := h j; simpa using this
  · exact absurd rfl hd

theorem moduleFinite_quotient_of_X_pow_mem (J : Ideal (MvPowerSeries σ B)) (q : ℕ)
    (hJ : ∀ j : σ, (MvPowerSeries.X j : MvPowerSeries σ B) ^ (q + 1) ∈ J) :
    Module.Finite B (MvPowerSeries σ B ⧸ J) := by
  classical
  have h𝔫J : Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ B) ^ (q + 1)) ≤ J := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩; exact hJ j
  let n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => q)
  let T : Finset (σ →₀ ℕ) :=
    Finset.univ.image (fun e : σ → Fin (q + 1) => Finsupp.equivFunOnFinite.symm (fun s => (e s : ℕ)))
  have hT : ∀ d : σ →₀ ℕ, (∀ s, d s ≤ q) → d ∈ T := by
    intro d hd
    refine Finset.mem_image.mpr ⟨fun s => ⟨d s, Nat.lt_succ_of_le (hd s)⟩, Finset.mem_univ _, ?_⟩
    ext s; simp
  let gens : Finset (MvPowerSeries σ B ⧸ J) :=
    T.image (fun d => Ideal.Quotient.mk J (↑(MvPolynomial.monomial d (1 : B)) : MvPowerSeries σ B))
  refine Module.Finite.of_fg_top ⟨gens, ?_⟩
  rw [Submodule.eq_top_iff']
  intro y
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective y
  set P : MvPolynomial σ B := MvPowerSeries.trunc' B n G with hP_def
  have hGP : Ideal.Quotient.mk J G = Ideal.Quotient.mk J (↑P : MvPowerSeries σ B) :=
    (Ideal.Quotient.eq).mpr (h𝔫J (sub_trunc_mem_span_X_pow q G))
  rw [hGP, MvPolynomial.as_sum P, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum, map_sum]
  refine Submodule.sum_mem _ fun v hv => ?_
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    show MvPolynomial.monomial v (MvPolynomial.coeff v P) = MvPolynomial.coeff v P • MvPolynomial.monomial v (1 : B)
      from by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    MvPolynomial.coe_smul, ← Ideal.Quotient.mkₐ_eq_mk B, map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hT v (coeff_trunc'_ne_zero_le q G v hv), rfl⟩)

theorem fg_of_pow_span_X_le_gen [IsNoetherianRing B] (I : Ideal (MvPowerSeries σ B)) (N : ℕ)
    (h : (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ B))) ^ N ≤ I) : I.FG := by
  classical
  set 𝔪 : Ideal (MvPowerSeries σ B) := Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ B)) with h𝔪

  have h𝔪fg : (𝔪 ^ N).FG := Submodule.FG.pow ⟨Finset.univ.image (MvPowerSeries.X : σ → MvPowerSeries σ B), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩ N
  haveI hfin : Module.Finite B (MvPowerSeries σ B ⧸ 𝔪 ^ N) :=
    moduleFinite_quotient_of_X_pow_mem (𝔪 ^ N) N fun j => by
      have hX : (MvPowerSeries.X j : MvPowerSeries σ B) ^ N ∈ 𝔪 ^ N :=
        Ideal.pow_mem_pow (show (MvPowerSeries.X j : MvPowerSeries σ B) ∈ 𝔪 from
          Ideal.subset_span (Set.mem_range_self j)) N
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ hX
  haveI : IsNoetherian B (MvPowerSeries σ B ⧸ 𝔪 ^ N) := isNoetherian_of_isNoetherianRing_of_finite B _

  let mkl : MvPowerSeries σ B →ₗ[B] MvPowerSeries σ B ⧸ 𝔪 ^ N := (Ideal.Quotient.mkₐ B (𝔪 ^ N)).toLinearMap
  have hmkl : ∀ x, mkl x = Ideal.Quotient.mk (𝔪 ^ N) x := fun _ => rfl
  let Ibar : Submodule B (MvPowerSeries σ B ⧸ 𝔪 ^ N) := Submodule.map mkl (I.restrictScalars B)
  obtain ⟨T, hT⟩ : Ibar.FG := IsNoetherian.noetherian Ibar
  have hex : ∀ t ∈ T, ∃ y, y ∈ I ∧ mkl y = t := by
    intro t ht
    have : t ∈ Ibar := by rw [← hT]; exact Submodule.subset_span ht
    obtain ⟨y, hy, hyt⟩ := Submodule.mem_map.mp this
    exact ⟨y, hy, hyt⟩
  choose! lf hlfI hlf using hex
  obtain ⟨G𝔪, hG𝔪⟩ := h𝔪fg
  refine ⟨T.image lf ∪ G𝔪, le_antisymm ?_ ?_⟩
  ·
    rw [Finset.coe_union, Finset.coe_image]
    refine Ideal.span_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨t, ht, rfl⟩; exact hlfI t ht
    · intro g hg; exact h (hG𝔪 ▸ Ideal.subset_span hg)
  ·
    intro x hx
    have hmx : mkl x ∈ Submodule.span B (T : Set (MvPowerSeries σ B ⧸ 𝔪 ^ N)) := by
      rw [hT]; exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hmx
    set y : MvPowerSeries σ B := ∑ t ∈ T, c t • lf t with hy_def
    have hyspan : y ∈ Ideal.span ((T.image lf ∪ G𝔪 : Finset _) : Set (MvPowerSeries σ B)) := by
      refine Submodule.sum_mem _ fun t ht => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by
        rw [Finset.coe_union, Finset.coe_image]; exact Or.inl ⟨t, ht, rfl⟩))
    have hxy : x - y ∈ 𝔪 ^ N := by
      rw [← Ideal.Quotient.eq, ← hmkl, ← hmkl, hy_def, map_sum]
      rw [← hc]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_smul, hlf t ht]
    have hxy' : x - y ∈ Ideal.span ((T.image lf ∪ G𝔪 : Finset _) : Set (MvPowerSeries σ B)) := by
      rw [← hG𝔪] at hxy
      refine Ideal.span_mono ?_ hxy
      rw [Finset.coe_union]; exact Set.subset_union_right
    have : x = y + (x - y) := by abel
    rw [this]
    exact Ideal.add_mem _ hyspan hxy'

end FgPowSpanX

namespace Ideal p2m_export "Ideal" "Quotient.eq_zero_iff_mem mul_mem_right Quotient.mkₐ Quotient.eq pow_le_pow_right span_mono mem_jacobson_bot radical sum_mem mem_bot span span_singleton_pow Quotient.mk mul_mem_left mul_mono_right map span_singleton_le_iff_mem FG mul_top ext jacobson span_le FG.pow pow_le_self mul_mono_left pow_mem_pow pow_right_mono Quotient.mk_eq_mk_iff_sub_mem span_union sup_pow_add_le_pow_sup_pow Quotient.mkₐ_eq_mk subset_span Quotient.factorₐ Quotient.mk_surjective" end Ideal
p2m_open_scoped "Ideal" in

theorem Ideal.fg_of_pow_span_X_le {B : Type} [CommRing B] [IsNoetherianRing B]
    (I : Ideal (MvPowerSeries (Fin 2) B)) (N : ℕ)
    (h : (Ideal.span (Set.range MvPowerSeries.X)) ^ N ≤ I) : I.FG :=
  FgPowSpanX.fg_of_pow_span_X_le_gen I N h

namespace InvGen

theorem eq_adicEval_of_X_pow_mem_ker {B : Type} [CommRing B] {S : Type} [CommRing S] [Algebra B S]
    (θ : MvPowerSeries (Fin 2) B →ₐ[B] S) (hθ : ∃ N : ℕ, ∀ i, (MvPowerSeries.X i) ^ N ∈ RingHom.ker θ)
    (G : MvPowerSeries (Fin 2) B) :
    θ G = MvFormalGroup.adicEval (⊥ : Ideal S) (fun i => θ (MvPowerSeries.X i)) G := by
  obtain ⟨N, hN⟩ := hθ
  exact MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal S) θ
    (fun s => ⟨N, by simpa [RingHom.mem_ker, map_pow] using hN s⟩) G

section Calculus

variable {B : Type} [CommRing B]

theorem mem_radical_bot_of_isNilpotent {S : Type} [CommRing S] {s : S} (h : IsNilpotent s) :
    s ∈ (⊥ : Ideal S).radical := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simp [hn]⟩

theorem isNilpotent_of_mem_radical_bot {S : Type} [CommRing S] {s : S} (h : s ∈ (⊥ : Ideal S).radical) :
    IsNilpotent s := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simpa using hn⟩

abbrev wpt {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    (a : Fin 2 → S) (b : Fin 2 → L) : Fin 2 ⊕ Fin 2 → S ⊗[B] L :=
  Sum.elim (fun j => a j ⊗ₜ[B] (1 : L)) (fun j => (1 : S) ⊗ₜ[B] b j)

theorem wpt_nil {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ s, wpt a b s ∈ (⊥ : Ideal (S ⊗[B] L)).radical := by
  rintro (j | j)
  · obtain ⟨n, hn⟩ := ha j
    refine ⟨n, ?_⟩
    simp [wpt, Algebra.TensorProduct.tmul_pow, hn]
  · obtain ⟨n, hn⟩ := hb j
    refine ⟨n, ?_⟩
    simp [wpt, Algebra.TensorProduct.tmul_pow, hn]

abbrev ptF (F : MvFormalGroup 2 B) {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    (a : Fin 2 → S) (b : Fin 2 → L) : Fin 2 → S ⊗[B] L :=
  fun i => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) (F.toPowerSeries i)

theorem ptF_nil (F : MvFormalGroup 2 B) {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i, ptF F a b i ∈ (⊥ : Ideal (S ⊗[B] L)).radical :=
  fun i => MvFormalGroup.adicEval_mem_radical (⊥ : Ideal (S ⊗[B] L)) (wpt_nil ha hb) (F.constantCoeff_eq_zero i)

theorem map_comp_wpt {S S' L : Type} [CommRing S] [Algebra B S] [CommRing S'] [Algebra B S']
    [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') (a : Fin 2 → S) (b : Fin 2 → L) :
    (fun s => Algebra.TensorProduct.map φ (AlgHom.id B L) (wpt a b s)) = wpt (fun j => φ (a j)) b := by
  funext s
  rcases s with j | j <;> simp [wpt]

theorem map_adicEval_wpt {S S' L : Type} [CommRing S] [Algebra B S] [CommRing S'] [Algebra B S']
    [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') {a : Fin 2 → S} {b : Fin 2 → L}
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) (G : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    Algebra.TensorProduct.map φ (AlgHom.id B L) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) G) =
      MvFormalGroup.adicEval (⊥ : Ideal (S' ⊗[B] L)) (wpt (fun j => φ (a j)) b) G := by
  rw [MvFormalGroup.map_adicEval (⊥ : Ideal (S ⊗[B] L)) (⊥ : Ideal (S' ⊗[B] L))
      (Algebra.TensorProduct.map φ (AlgHom.id B L)) Submodule.fg_bot
      (fun s hs => by rw [Ideal.mem_bot] at hs; simp [hs]) (wpt_nil ha hb), map_comp_wpt]

theorem map_ptF (F : MvFormalGroup 2 B) {S S' L : Type} [CommRing S] [Algebra B S] [CommRing S'] [Algebra B S']
    [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') {a : Fin 2 → S} {b : Fin 2 → L}
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    (fun i => Algebra.TensorProduct.map φ (AlgHom.id B L) (ptF F a b i)) = ptF F (fun j => φ (a j)) b := by
  funext i
  exact map_adicEval_wpt φ ha hb _

theorem map_adicEval_ptF (F : MvFormalGroup 2 B) {S S' L : Type} [CommRing S] [Algebra B S]
    [CommRing S'] [Algebra B S'] [CommRing L] [Algebra B L] (φ : S →ₐ[B] S') {a : Fin 2 → S} {b : Fin 2 → L}
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) (G : MvPowerSeries (Fin 2) B) :
    Algebra.TensorProduct.map φ (AlgHom.id B L) (MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (ptF F a b) G) =
      MvFormalGroup.adicEval (⊥ : Ideal (S' ⊗[B] L)) (ptF F (fun j => φ (a j)) b) G := by
  rw [MvFormalGroup.map_adicEval (⊥ : Ideal (S ⊗[B] L)) (⊥ : Ideal (S' ⊗[B] L))
      (Algebra.TensorProduct.map φ (AlgHom.id B L)) Submodule.fg_bot
      (fun s hs => by rw [Ideal.mem_bot] at hs; simp [hs]) (ptF_nil F ha hb), map_ptF F φ ha hb]

theorem adicEval_sub {σ : Type} [Finite σ] {S : Type} [CommRing S] [Algebra B S] {x : σ → S}
    (hx : ∀ s, x s ∈ (⊥ : Ideal S).radical) (f g : MvPowerSeries σ B) :
    MvFormalGroup.adicEval (⊥ : Ideal S) x (f - g) =
      MvFormalGroup.adicEval (⊥ : Ideal S) x f - MvFormalGroup.adicEval (⊥ : Ideal S) x g := by
  rw [← MvFormalGroup.coe_adicEvalAlgHom (⊥ : Ideal S) hx, map_sub]

theorem adicEval_wpt_sub {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i))
    (f g : MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
    MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) (f - g) =
      MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) f -
        MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) g :=
  adicEval_sub (x := wpt a b) (wpt_nil ha hb) f g

theorem adicEval_wpt_subst_F (F : MvFormalGroup 2 B) {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i))
    (g : MvPowerSeries (Fin 2) B) :
    MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b) (MvPowerSeries.subst F.toPowerSeries g) =
      MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (ptF F a b) g :=
  MvFormalGroup.adicEval_subst (⊥ : Ideal (S ⊗[B] L)) (wpt_nil ha hb) F.hasSubst_toPowerSeries g

theorem adicEval_wpt_subst_inl {S L : Type} [CommRing S] [Algebra B S] [CommRing L] [Algebra B L]
    {a : Fin 2 → S} {b : Fin 2 → L} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i))
    (g : MvPowerSeries (Fin 2) B) :
    MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b)
        (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) g) =
      (MvFormalGroup.adicEval (⊥ : Ideal S) a g) ⊗ₜ[B] (1 : L) := by
  have hX : MvPowerSeries.HasSubst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun l => MvPowerSeries.constantCoeff_X _)
  rw [MvFormalGroup.adicEval_subst (⊥ : Ideal (S ⊗[B] L)) (wpt_nil ha hb) hX]
  have : (fun l => MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B] L)) (wpt a b)
      (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = fun l => a l ⊗ₜ[B] (1 : L) := by
    funext l; rw [MvFormalGroup.adicEval_X]; rfl
  rw [this]
  have hφ := MvFormalGroup.map_adicEval (⊥ : Ideal S) (⊥ : Ideal (S ⊗[B] L))
    (Algebra.TensorProduct.includeLeft : S →ₐ[B] S ⊗[B] L) Submodule.fg_bot
    (fun s hs => by rw [Ideal.mem_bot] at hs; simp [hs]) (fun i => mem_radical_bot_of_isNilpotent (ha i)) g
  simp only [Algebra.TensorProduct.includeLeft_apply] at hφ
  exact hφ.symm

end Calculus

def augX (B : Type) [CommRing B] : Ideal (MvPowerSeries (Fin 2) B) :=
  Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))

section Assembly

variable {B : Type} [CommRing B]

theorem augX_pow_le_of_X_pow_mem (I : Ideal (MvPowerSeries (Fin 2) B)) {q : ℕ}
    (hq : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I) : augX B ^ (q + q) ≤ I := by
  have hXeq : augX B = Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) B)} ⊔ Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) B)} := by
    show Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) = _
    rw [← Ideal.span_union]
    congr 1
    ext f
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [hXeq]
  refine (Ideal.sup_pow_add_le_pow_sup_pow).trans ?_
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
  refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem] <;> exact hq _

theorem nil_mk_pow (I : Ideal (MvPowerSeries (Fin 2) B)) {q : ℕ} (hq : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (M : ℕ) (i : Fin 2) : IsNilpotent (Ideal.Quotient.mk (I ^ M) (MvPowerSeries.X i : MvPowerSeries (Fin 2) B)) := by
  refine ⟨q * M, ?_⟩
  rw [← map_pow, pow_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (hq i) M

theorem inv_of_inv_of_le (p : ℕ) [Fact p.Prime] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    {q : ℕ} (hq : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    {L : Type} [CommRing L] [HopfAlgebra B L] (π : MvPowerSeries (Fin 2) B →ₐ[B] L)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (δ : ∀ N : ℕ, N ≠ 0 → (MvPowerSeries (Fin 2) B ⧸ I ^ N) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L)
    (hδf : ∀ (N : ℕ) (hN : N ≠ 0) (G : MvPowerSeries (Fin 2) B), δ N hN (Ideal.Quotient.mk (I ^ N) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ N) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (N M : ℕ) (hN : N ≠ 0) (hM : M ≠ 0) (hNM : N ≤ M) (g : MvPowerSeries (Fin 2) B)
    (hg : δ M hM (Ideal.Quotient.mk (I ^ M) g) = Ideal.Quotient.mk (I ^ M) g ⊗ₜ[B] (1 : L)) :
    δ N hN (Ideal.Quotient.mk (I ^ N) g) = Ideal.Quotient.mk (I ^ N) g ⊗ₜ[B] (1 : L) := by
  have hle : I ^ M ≤ I ^ N := Ideal.pow_le_pow_right hNM
  let pr : (MvPowerSeries (Fin 2) B ⧸ I ^ M) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) := Ideal.Quotient.factorₐ B hle
  have hpr : ∀ a, pr (Ideal.Quotient.mk (I ^ M) a) = Ideal.Quotient.mk (I ^ N) a := fun a => rfl
  have key := congrArg (Algebra.TensorProduct.map pr (AlgHom.id B L)) hg
  rw [hδf M hM] at key
  erw [map_adicEval_ptF X.F pr (nil_mk_pow I hq M) hπnil] at key
  simp only [Algebra.TensorProduct.map_tmul, hpr, map_one] at key
  rw [hδf N hN]
  exact key

theorem clause_of_forall_inv (p : ℕ) [Fact p.Prime] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hIfg : I.FG) (hIX : I ≤ augX B)
    {q : ℕ} (hq : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    {L : Type} [CommRing L] [HopfAlgebra B L] (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (δ : ∀ N : ℕ, N ≠ 0 → (MvPowerSeries (Fin 2) B ⧸ I ^ N) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L)
    (hδf : ∀ (N : ℕ) (hN : N ≠ 0) (G : MvPowerSeries (Fin 2) B), δ N hN (Ideal.Quotient.mk (I ^ N) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ N) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (g : MvPowerSeries (Fin 2) B)
    (hinv : ∀ (N : ℕ) (hN : N ≠ 0), δ N hN (Ideal.Quotient.mk (I ^ N) g) = Ideal.Quotient.mk (I ^ N) g ⊗ₜ[B] (1 : L)) :
    MvPowerSeries.subst X.F.toPowerSeries g - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) g ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))) := by
  apply MvPowerSeries.mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective I hIfg π hπ hker hπnil hev
  intro n
  have hle : I ^ (n + 1) ≤ augX B ^ (n + 1) := Ideal.pow_right_mono hIX _
  let ρ : (MvPowerSeries (Fin 2) B ⧸ I ^ (n + 1)) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ augX B ^ (n + 1)) := Ideal.Quotient.factorₐ B hle
  have hρ : ∀ a, ρ (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (augX B ^ (n + 1)) a := fun a => rfl
  have nilT : ∀ i : Fin 2, IsNilpotent (Ideal.Quotient.mk (augX B ^ (n + 1)) (MvPowerSeries.X i : MvPowerSeries (Fin 2) B)) := by
    intro i
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
  show MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ augX B ^ (n + 1)) ⊗[B] L))
      (wpt (fun j => Ideal.Quotient.mk (augX B ^ (n + 1)) (MvPowerSeries.X j)) (fun j => π (MvPowerSeries.X j)))
      (MvPowerSeries.subst X.F.toPowerSeries g -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) g) = 0
  rw [adicEval_wpt_sub nilT hπnil, adicEval_wpt_subst_F X.F nilT hπnil,
    adicEval_wpt_subst_inl nilT hπnil, sub_eq_zero]
  have key := congrArg (Algebra.TensorProduct.map ρ (AlgHom.id B L)) (hinv (n + 1) (Nat.succ_ne_zero n))
  rw [hδf (n + 1) (Nat.succ_ne_zero n)] at key
  erw [map_adicEval_ptF X.F ρ (nil_mk_pow I hq (n + 1)) hπnil] at key
  simp only [Algebra.TensorProduct.map_tmul, hρ, map_one] at key
  have e1 := eq_adicEval_of_X_pow_mem_ker (Ideal.Quotient.mkₐ B (augX B ^ (n + 1)))
    ⟨n + 1, fun i => by
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mkₐ B (augX B ^ (n + 1)) (MvPowerSeries.X i ^ (n + 1)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _⟩ g
  simp only [Ideal.Quotient.mkₐ_eq_mk] at e1
  rw [← e1]
  exact key

theorem exists_sub_mem_and_forall_inv (p : ℕ) [Fact p.Prime] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hIX : I ≤ augX B) {q : ℕ} (hq : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    {L : Type} [CommRing L] [HopfAlgebra B L] [Module.Free B L] [Module.Finite B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hcomul : ∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i))
    (hcounit : ∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G)
    (δ : ∀ N : ℕ, N ≠ 0 → (MvPowerSeries (Fin 2) B ⧸ I ^ N) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L)
    (hδf : ∀ (N : ℕ) (hN : N ≠ 0) (G : MvPowerSeries (Fin 2) B), δ N hN (Ideal.Quotient.mk (I ^ N) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ N) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (f : MvPowerSeries (Fin 2) B) (hf : f ∈ I) :
    ∃ g : MvPowerSeries (Fin 2) B, g ∈ I ∧ f - g ∈ augX B * I ∧
      ∀ (N : ℕ) (hN : N ≠ 0), δ N hN (Ideal.Quotient.mk (I ^ N) g) = Ideal.Quotient.mk (I ^ N) g ⊗ₜ[B] (1 : L) := by
  classical
  have hXI : augX B ^ (q + q) ≤ I := augX_pow_le_of_X_pow_mem I hq

  let Inv : ℕ → MvPowerSeries (Fin 2) B → Prop := fun N g =>
    ∀ hN : N ≠ 0, δ N hN (Ideal.Quotient.mk (I ^ N) g) = Ideal.Quotient.mk (I ^ N) g ⊗ₜ[B] (1 : L)

  obtain ⟨g0, hg0I, hfg0, hg0inv⟩ := CerednikDrinfeld.FormalODModule.exists_sub_mem_and_firstOrder_invariant p X I ⟨q, hq⟩ hmul π hπ hker hπnil hev
    hcomul hcounit (δ 2 two_ne_zero) (hδf 2 two_ne_zero) f hf
  have hInv0 : Inv 2 g0 := fun hN => hg0inv

  have step : ∀ (k : ℕ) (g : MvPowerSeries (Fin 2) B), g ∈ I → Inv (k + 2) g →
      ∃ g', g' ∈ I ∧ g - g' ∈ I ^ (k + 2) ∧ Inv (k + 1 + 2) g' := by
    intro k g hg hinv
    obtain ⟨s, hs, hs'⟩ := CerednikDrinfeld.FormalODModule.exists_mem_pow_and_invariant_succ p X I ⟨q, hq⟩ hmul π hπ hker hπnil hev hcomul hcounit
      (k + 2) (Nat.succ_ne_zero _) (δ (k + 2) (Nat.succ_ne_zero _)) (hδf (k + 2) (Nat.succ_ne_zero _))
      (δ (k + 2 + 1) (Nat.succ_ne_zero _)) (hδf (k + 2 + 1) (Nat.succ_ne_zero _)) g hg (hinv _)
    refine ⟨g - s, I.sub_mem hg (Ideal.pow_le_self (Nat.succ_ne_zero _) hs), by simpa using hs, ?_⟩
    have hidx : k + 2 + 1 = k + 1 + 2 := by omega
    have : Inv (k + 2 + 1) (g - s) := fun hN => hs'
    exact hidx ▸ this

  have step' : ∀ (k : ℕ) (g : MvPowerSeries (Fin 2) B), ∃ g' : MvPowerSeries (Fin 2) B,
      (g ∈ I ∧ Inv (k + 2) g) → (g' ∈ I ∧ g - g' ∈ I ^ (k + 2) ∧ Inv (k + 1 + 2) g') := by
    intro k g
    by_cases h : g ∈ I ∧ Inv (k + 2) g
    · obtain ⟨g', h1, h2, h3⟩ := step k g h.1 h.2
      exact ⟨g', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨g, fun h' => (h h').elim⟩
  choose next hnext using step'
  let seq : ℕ → MvPowerSeries (Fin 2) B := fun k => Nat.rec g0 (fun k gk => next k gk) k
  have hseq0 : seq 0 = g0 := rfl
  have hseqS : ∀ k, seq (k + 1) = next k (seq k) := fun k => rfl
  have hseq : ∀ k, seq k ∈ I ∧ Inv (k + 2) (seq k) := by
    intro k
    induction k with
    | zero => exact ⟨hg0I, hInv0⟩
    | succ k ih =>
      rw [hseqS]
      obtain ⟨h1, -, h3⟩ := hnext k (seq k) ih
      exact ⟨h1, h3⟩
  have hseqd : ∀ k, seq k - seq (k + 1) ∈ I ^ (k + 2) := by
    intro k
    rw [hseqS]
    exact (hnext k (seq k) (hseq k)).2.1
  have hIXpow : ∀ m, I ^ m ≤ augX B ^ m := fun m => Ideal.pow_right_mono hIX m
  have hdiff : ∀ m k, m ≤ k → seq m - seq k ∈ augX B ^ m := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have : seq m - seq (k + 1) = (seq m - seq k) + (seq k - seq (k + 1)) := by ring
      rw [this]
      refine Ideal.add_mem _ ih ?_
      exact Ideal.pow_le_pow_right (by omega) (hIXpow _ (hseqd k))
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      seq m ≡ seq n [SMOD (augX B ^ m • ⊤ : Submodule (MvPowerSeries (Fin 2) B) (MvPowerSeries (Fin 2) B))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hdiff m n hmn
  have hpre : IsPrecomplete (augX B) (MvPowerSeries (Fin 2) B) := by
    unfold augX; infer_instance
  obtain ⟨gInf, hgInf⟩ := IsPrecomplete.prec hpre hcauchy
  have hlim : ∀ n, seq n - gInf ∈ augX B ^ n := by
    intro n
    have := hgInf n
    rw [SModEq.sub_mem] at this
    simpa [Ideal.smul_eq_mul, Ideal.mul_top] using this
  have hXI' : ∀ k, q + q ≤ k → augX B ^ k ≤ I := fun k hk => (Ideal.pow_le_pow_right hk).trans hXI
  have hgInfI : gInf ∈ I := by
    have : gInf = seq (q + q) - (seq (q + q) - gInf) := by ring
    rw [this]
    exact I.sub_mem (hseq _).1 (hXI' _ le_rfl (hlim _))
  have hInvAll : ∀ (N : ℕ), N ≠ 0 → Inv N gInf := by
    intro N hN hN'
    set k := (q + q + 1) * N with hk
    have hkN : N ≤ k + 2 := by rw [hk]; nlinarith
    have hXk : augX B ^ k ≤ I ^ N := by
      rw [hk, pow_mul]
      exact Ideal.pow_right_mono (hXI' _ (by omega)) N
    have hmk : Ideal.Quotient.mk (I ^ N) gInf = Ideal.Quotient.mk (I ^ N) (seq k) := by
      rw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hXk (hlim k)
    rw [hmk]
    exact inv_of_inv_of_le p X I hq π hπnil δ hδf N (k + 2) hN' (Nat.succ_ne_zero _) hkN (seq k) ((hseq k).2 _)
  refine ⟨gInf, hgInfI, ?_, fun N hN => hInvAll N hN hN⟩
  have hd0 : ∀ k, seq 0 - seq k ∈ I ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : seq 0 - seq (k + 1) = (seq 0 - seq k) + (seq k - seq (k + 1)) := by ring
      rw [this]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right (by omega) (hseqd k))
  have e : f - gInf = (f - g0) + (seq 0 - seq (q + q + 1)) + (seq (q + q + 1) - gInf) := by
    rw [hseq0]; ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.add_mem _ hfg0 ?_) ?_
  · have : I ^ 2 ≤ augX B * I := by rw [pow_two]; exact Ideal.mul_mono_left hIX
    exact this (hd0 (q + q + 1))
  · have : augX B ^ (q + q + 1) ≤ augX B * I := by rw [pow_succ']; exact Ideal.mul_mono_right hXI
    exact this (hlim _)

end Assembly

end InvGen

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hfree : Module.Free B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))) :
    I = Ideal.span {w : MvPowerSeries (Fin 2) B | w ∈ I ∧
          MvPowerSeries.subst X.F.toPowerSeries w - MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) w ∈
          Ideal.span ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))} := by
  classical
  refine le_antisymm ?_ (Ideal.span_le.mpr (fun w hw => hw.1))
  have hIX : I ≤ InvGen.augX B := by
    intro f hf
    show f ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker]
    exact hunit f hf
  obtain ⟨q, hq⟩ := hnil
  have hIfg : (I : Submodule (MvPowerSeries (Fin 2) B) (MvPowerSeries (Fin 2) B)).FG :=
    Ideal.fg_of_pow_span_X_le I (q + q) (InvGen.augX_pow_le_of_X_pow_mem I hq)
  have hXjac : InvGen.augX B ≤ Ideal.jacobson ⊥ := by
    intro a ha
    rw [Ideal.mem_jacobson_bot]
    intro y
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have ha0 : MvPowerSeries.constantCoeff a = 0 := by
      have : a ∈ RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) B →+* B) := by
        rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff]; exact ha
      exact this
    simp [ha0]

  obtain ⟨L, instCR, instH, instCC, instFree, instFin, π, hπ, hker, hπnil, hev, hcomul, hcounitX, hcounit⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_of_subgroup_ideal p X I hfin hfree ⟨q, hq⟩ hunit hmul
  have hlev := fun (N : ℕ) (hN : N ≠ 0) =>
    CerednikDrinfeld.FormalODModule.exists_levelCoaction_of_subgroup_ideal_of_ne_zero p X I ⟨q, hq⟩ hmul π hπ hker hπnil hev hcomul hcounit N hN
  choose δ hδf hδ2 hδ3 hδ4 hδ5 using hlev

  refine Submodule.le_of_le_smul_of_le_jacobson_bot hIfg hXjac ?_
  intro f hf
  obtain ⟨g, hgI, hfg, hinv⟩ := InvGen.exists_sub_mem_and_forall_inv p X I hIX hq hmul π hπ hker hπnil hev hcomul hcounit
    δ hδf f hf
  have hcl := InvGen.clause_of_forall_inv p X I hIfg hIX hq π hπ hker hπnil hev δ hδf g hinv
  have : f = g + (f - g) := by ring
  rw [this]
  refine Submodule.add_mem_sup (Ideal.subset_span ⟨hgI, hcl⟩) ?_
  simpa [Ideal.smul_eq_mul] using hfg

end

end S_CerednikDrinfeld_FormalODModule_eq_span_setOf_invariant_of_subgroup_ideal_of_free
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_span_setOf_invariant_of_subgroup_ideal_of_free (solution)
