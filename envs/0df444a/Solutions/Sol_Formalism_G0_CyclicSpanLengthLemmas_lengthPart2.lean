-- Prove2me | solution 1 for Formalism.G0.CyclicSpanLengthLemmas.lengthPart2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.510868+00:00
-- url     : https://prove2.me/submissions/7fb5d425-43f5-4b69-bb40-cccb8bfb6072

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbitsRefined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.G0
namespace CyclicSpanLengthLemmas
open ManyOrbitsP
private theorem length_eq_length_add_length_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z]
    (W : Submodule R Z) : Module.length R Z = Module.length R W + Module.length R (Z ⧸ W) :=
  Module.length_eq_add_of_exact W.subtype W.mkQ Subtype.val_injective W.mkQ_surjective
    (LinearMap.exact_subtype_mkQ W)
private theorem length_le_one_of_cyclic_smul_eq_zero {R Q : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup Q] [Module R Q] (π : R) (hπ : Irreducible π) (x : Q)
    (hx : Submodule.span R {x} = ⊤) (h0 : π • x = 0) : Module.length R Q ≤ 1 := by
  have hm : IsLocalRing.maximalIdeal R ≤ LinearMap.ker (LinearMap.toSpanSingleton R Q x) := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact h0
  have hsurj : Function.Surjective
      ((IsLocalRing.maximalIdeal R).liftQ (LinearMap.toSpanSingleton R Q x) hm) := by
    rw [← LinearMap.range_eq_top, Submodule.range_liftQ, ← LinearMap.span_singleton_eq_range, hx]
  have hs : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal R).out
  calc Module.length R Q ≤ Module.length R (R ⧸ IsLocalRing.maximalIdeal R) :=
        Module.length_le_of_surjective _ hsurj
    _ = 1 := Module.length_eq_one_iff.mpr hs
private theorem span_range_map_eq_univ_of_surjective {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {n : ℕ} (F : A →ₗ[R] B) (hF : Function.Surjective F)
    (g : Fin n → A) (hg : Submodule.span R (Set.range g) = ⊤) :
    Submodule.span R (Set.range (fun i => F (g i))) = ⊤ := by
  have e : (Set.range fun i => F (g i)) = F '' Set.range g := by
    rw [← Set.range_comp]
    rfl
  rw [e, ← Submodule.map_span, hg, Submodule.map_top, LinearMap.range_eq_top.mpr hF]
private theorem span_singleton_self_subtype_eq_univ {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (y : Q) :
    Submodule.span R {(⟨y, Submodule.mem_span_singleton_self y⟩ : Submodule.span R {y})} = ⊤ := by
  apply Submodule.map_injective_of_injective (f := (Submodule.span R {y}).subtype)
    Subtype.val_injective
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_subtype_top]
  rfl
private theorem length_le_of_cyclic_pow_smul_eq_zero {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) : ∀ (Q : Type) [AddCommGroup Q] [Module R Q] (x : Q),
    Submodule.span R {x} = ⊤ → π ^ k • x = 0 → Module.length R Q ≤ k := by
  induction k with
  | zero =>
    intro Q _ _ x hx h0
    rw [pow_zero, one_smul] at h0
    subst h0
    rw [Submodule.span_singleton_eq_bot.mpr rfl] at hx
    have h0 : ∀ z : Q, z = 0 := by
      intro z
      have hz : z ∈ (⊥ : Submodule R Q) := by
        rw [hx]
        exact Submodule.mem_top
      exact (Submodule.mem_bot R).mp hz
    have : Subsingleton Q := ⟨fun a b => (h0 a).trans (h0 b).symm⟩
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ k ih =>
    intro Q _ _ x hx h0
    have hW : Module.length R (Submodule.span R {π • x}) ≤ k := by
      refine ih (Submodule.span R {π • x}) ⟨π • x, Submodule.mem_span_singleton_self _⟩
        (span_singleton_self_subtype_eq_univ _) ?_
      apply Subtype.ext
      show π ^ k • π • x = 0
      rw [smul_smul, ← pow_succ]
      exact h0
    have hq : Module.length R (Q ⧸ Submodule.span R {π • x}) ≤ 1 := by
      refine length_le_one_of_cyclic_smul_eq_zero π hπ (Submodule.mkQ _ x) ?_ ?_
      · have e : ({(Submodule.span R {π • x}).mkQ x} : Set (Q ⧸ Submodule.span R {π • x})) =
            (Submodule.span R {π • x}).mkQ '' {x} := Set.image_singleton.symm
        rw [e, ← Submodule.map_span, hx, Submodule.map_top, Submodule.range_mkQ]
      · rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_span_singleton_self _
    rw [length_eq_length_add_length_quot (Submodule.span R {π • x})]
    calc _ ≤ (k : ℕ∞) + 1 := add_le_add hW hq
      _ = ((k + 1 : ℕ) : ℕ∞) := (Nat.cast_succ k).symm
private theorem length_le_mul_of_span_fin_pow_smul_eq_zero {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q]
    (g : Fin n → Q), Submodule.span R (Set.range g) = ⊤ → (∀ q : Q, π ^ k • q = 0) →
    Module.length R Q ≤ ((k * n : ℕ) : ℕ∞) := by
  intro n
  induction n with
  | zero =>
    intro Q _ _ g hg _
    rw [Set.range_eq_empty g, Submodule.span_empty] at hg
    have h0 : ∀ z : Q, z = 0 := by
      intro z
      have hz : z ∈ (⊥ : Submodule R Q) := by
        rw [hg]
        exact Submodule.mem_top
      exact (Submodule.mem_bot R).mp hz
    have : Subsingleton Q := ⟨fun a b => (h0 a).trans (h0 b).symm⟩
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ n ih =>
    intro Q _ _ g hg hk
    have hW : Module.length R (Submodule.span R {g 0}) ≤ k :=
      length_le_of_cyclic_pow_smul_eq_zero π hπ k (Submodule.span R {g 0}) ⟨g 0, Submodule.mem_span_singleton_self _⟩
        (span_singleton_self_subtype_eq_univ _) (Subtype.ext (hk (g 0)))
    have hq : Module.length R (Q ⧸ Submodule.span R {g 0}) ≤ ((k * n : ℕ) : ℕ∞) := by
      refine ih (Q ⧸ Submodule.span R {g 0}) (fun i => (Submodule.span R {g 0}).mkQ (g i.succ))
        ?_ ?_
      · have htop := span_range_map_eq_univ_of_surjective (Submodule.span R {g 0}).mkQ
          (Submodule.span R {g 0}).mkQ_surjective g hg
        rw [eq_top_iff, ← htop, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        induction i using Fin.cases with
        | zero =>
          show (Submodule.span R {g 0}).mkQ (g 0) ∈ _
          rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
            (Submodule.mem_span_singleton_self _)]
          exact Submodule.zero_mem _
        | succ j => exact Submodule.subset_span ⟨j, rfl⟩
      · intro q
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [← Submodule.Quotient.mk_smul, hk z, Submodule.Quotient.mk_zero]
    rw [length_eq_length_add_length_quot (Submodule.span R {g 0})]
    calc _ ≤ (k : ℕ∞) + ((k * n : ℕ) : ℕ∞) := add_le_add hW hq
      _ = ((k * (n + 1) : ℕ) : ℕ∞) := by push_cast; ring
private theorem length_le_sum_of_antitone_chain_quot_le {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] :
    ∀ (V : ℕ) (E : ℕ → Submodule R Z) (b : ℕ → ℕ), E V = ⊥ → (∀ j, E (j + 1) ≤ E j) →
    (∀ j < V, Module.length R (E j ⧸ (E (j + 1)).comap (E j).subtype) ≤ (b j : ℕ∞)) →
    Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, b j : ℕ) : ℕ∞) := by
  intro V
  induction V with
  | zero =>
    intro E b hV _ _
    have h0 : ∀ z ∈ E 0, z = 0 := by
      rw [hV]
      intro z hz
      exact (Submodule.mem_bot R).mp hz
    have : Subsingleton (E 0) := ⟨fun a c => Subtype.ext ((h0 _ a.2).trans (h0 _ c.2).symm)⟩
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ V ih =>
    intro E b hV hE hb
    have h1 := ih (fun j => E (j + 1)) (fun j => b (j + 1)) hV (fun j => hE (j + 1))
      (fun j hj => hb (j + 1) (by omega))
    have h2 : Module.length R ((E 1).comap (E 0).subtype) ≤ Module.length R (E 1) :=
      Module.length_le_of_injective (Submodule.comapSubtypeEquivOfLe (hE 0)).toLinearMap
        (Submodule.comapSubtypeEquivOfLe (hE 0)).injective
    have h3 := hb 0 (by omega)
    rw [length_eq_length_add_length_quot ((E 1).comap (E 0).subtype), Finset.sum_range_succ', Nat.cast_add]
    exact add_le_add (h2.trans h1) h3
private theorem length_quot_comap_le_mul_of_pow_smul_mem {R Z : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup Z] [Module R Z] (π : R) (hπ : Irreducible π) (S n : ℕ) (E E' : Submodule R Z)
    (hEE : ∀ z ∈ E, π ^ S • z ∈ E') (g : Fin n → Z) (hg : E ≤ Submodule.span R (Set.range g)) :
    Module.length R (E ⧸ E'.comap E.subtype) ≤ ((S * n : ℕ) : ℕ∞) := by
  set ψ : (Fin n → R) →ₗ[R] Z :=
    ∑ i, (LinearMap.proj i : (Fin n → R) →ₗ[R] R).smulRight (g i) with hψdef
  have hψ : ∀ i, ψ (Pi.single i 1) = g i := by
    intro i
    simp [hψdef, Pi.single_apply]
  have hrange : E ≤ LinearMap.range ψ := by
    refine hg.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, hψ i⟩
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (E.comap ψ)
  have hm : m ≤ n := by
    have h1 := Submodule.finrank_le (E.comap ψ)
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] at h1
    exact h1
  set Ψ : (E.comap ψ) →ₗ[R] E := LinearMap.codRestrict E (ψ ∘ₗ (E.comap ψ).subtype)
    (fun p => p.2) with hΨdef
  have hΨ : Function.Surjective Ψ := by
    intro e
    obtain ⟨r, hr⟩ := hrange e.2
    refine ⟨⟨r, ?_⟩, Subtype.ext hr⟩
    show ψ r ∈ E
    rw [hr]
    exact e.2
  have hF : Function.Surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ) :=
    (Submodule.mkQ_surjective _).comp hΨ
  have hsp := span_range_map_eq_univ_of_surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ) hF b b.span_eq
  have hkill : ∀ q : (E ⧸ E'.comap E.subtype), π ^ S • q = 0 := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hEE z.1 z.2
  calc Module.length R (E ⧸ E'.comap E.subtype) ≤ ((S * m : ℕ) : ℕ∞) :=
        length_le_mul_of_span_fin_pow_smul_eq_zero π hπ S m _ _ hsp hkill
    _ ≤ ((S * n : ℕ) : ℕ∞) := by exact_mod_cast Nat.mul_le_mul_left S hm
end CyclicSpanLengthLemmas
end Formalism.G0
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.CyclicSpanLengthLemmas
open ManyOrbitsP
namespace Formalism.G0.CyclicSpanLengthLemmas
theorem _root_.solution {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β < V, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ d * s ^ (β + 1) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * ((τ : ℝ) + 2 * S * s) := by
  classical
  set K : Submodule R M := Submodule.comap M.subtype (N ⊓ (Ideal.span {π ^ τ}) • M) with hKdef
  choose! C hCM hCcard hCx using h1
  set A0 : Submodule R (M ⧸ K) :=
    LinearMap.range ((π ^ τ) • (LinearMap.id : (M ⧸ K) →ₗ[R] (M ⧸ K))) with hA0def
  set bas := Module.finBasisOfFinrankEq R M hd with hbas
  have hQ : Module.length R ((M ⧸ K) ⧸ A0) ≤ ((τ * d : ℕ) : ℕ∞) := by
    refine length_le_mul_of_span_fin_pow_smul_eq_zero π hπ τ d ((M ⧸ K) ⧸ A0) (fun i => (A0.mkQ ∘ₗ K.mkQ) (bas i)) ?_ ?_
    · exact span_range_map_eq_univ_of_surjective (A0.mkQ ∘ₗ K.mkQ)
        ((Submodule.mkQ_surjective A0).comp (Submodule.mkQ_surjective K)) bas bas.span_eq
    · intro q
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective A0 q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨z, rfl⟩
  have hKθ : K ≤ LinearMap.ker (N.mkQ ∘ₗ M.subtype) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_inf.mp (Submodule.mem_comap.mp hx)).1
  set θ : (M ⧸ K) →ₗ[R] X ⧸ N := K.liftQ (N.mkQ ∘ₗ M.subtype) hKθ with hθdef
  have hθmk : ∀ x : M, θ (Submodule.Quotient.mk x) = N.mkQ (x : X) := fun x => rfl
  set E : ℕ → Submodule R (X ⧸ N) := fun j => Submodule.map (N.mkQ ∘ₗ M.subtype)
    (LinearMap.range ((π ^ (τ + j * S)) • (LinearMap.id : M →ₗ[R] M))) with hEdef
  have hEmem : ∀ j (x : M), N.mkQ (π ^ (τ + j * S) • (x : X)) ∈ E j := fun j x =>
    Submodule.mem_map.mpr ⟨π ^ (τ + j * S) • x, LinearMap.mem_range.mpr ⟨x, rfl⟩, rfl⟩
  have hEcases : ∀ j, ∀ w ∈ E j, ∃ x : M, w = N.mkQ (π ^ (τ + j * S) • (x : X)) := by
    intro j w hw
    simp only [hEdef] at hw
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact ⟨x, rfl⟩
  have hAx : ∀ a : M ⧸ K, a ∈ A0 → ∃ x : M, a = Submodule.Quotient.mk (π ^ τ • x) := by
    intro a ha
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ha
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K w
    exact ⟨x, by rw [← hw, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_smul]⟩
  have hθA : ∀ a : A0, (θ ∘ₗ A0.subtype) a ∈ E 0 := by
    intro a
    obtain ⟨x, hx⟩ := hAx a a.2
    rw [LinearMap.comp_apply, Submodule.subtype_apply, hx, hθmk, Submodule.coe_smul]
    simpa using hEmem 0 x
  set θA : A0 →ₗ[R] E 0 := LinearMap.codRestrict (E 0) (θ ∘ₗ A0.subtype) hθA with hθAdef
  have hθinj : Function.Injective θA := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have ha' : θ (a : M ⧸ K) = 0 := congrArg Subtype.val ha
    obtain ⟨x, hx⟩ := hAx a a.2
    rw [hx, hθmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha'
    apply Subtype.ext
    rw [hx, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr
      ⟨ha', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) x.2⟩)
  obtain ⟨C0, -, hC0card, hC0⟩ := h2
  have hC0e : C0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hC0card)
  have hEV : E V = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := hEcases V w hw
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hx' : π ^ (V * S) • (π ^ τ • (x : X)) ∈ N := by
      have h := hC0 (π ^ τ • (x : X)) (M.smul_mem _ x.2)
      rwa [hC0e, Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at h
    rwa [smul_smul, ← pow_add, add_comm (V * S) τ] at hx'
  have hEmono : ∀ j, E (j + 1) ≤ E j := by
    intro j w hw
    obtain ⟨x, rfl⟩ := hEcases (j + 1) w hw
    have e : π ^ (τ + (j + 1) * S) • (x : X) = π ^ (τ + j * S) • ((π ^ S • x : M) : X) := by
      rw [Submodule.coe_smul, smul_smul, ← pow_add]
      ring_nf
    rw [e]
    exact hEmem j _
  have hEstep : ∀ j, ∀ z ∈ E j, π ^ S • z ∈ E (j + 1) := by
    intro j z hz
    obtain ⟨x, rfl⟩ := hEcases j z hz
    have e : π ^ S • N.mkQ (π ^ (τ + j * S) • (x : X)) =
        N.mkQ (π ^ (τ + (j + 1) * S) • (x : X)) := by
      rw [← map_smul, smul_smul, ← pow_add]
      ring_nf
    rw [e]
    exact hEmem (j + 1) x
  have hEspan : ∀ j < V, E j ≤ Submodule.span R
      (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X))) := by
    intro j hj w hw
    obtain ⟨x, rfl⟩ := hEcases j w hw
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp (hCx j hj x x.2)
    have hmk : N.mkQ (π ^ (τ + j * S) • (x : X)) = N.mkQ c := by
      rw [← hnc, map_add, Submodule.mkQ_apply N n, (Submodule.Quotient.mk_eq_zero N).mpr hn,
        zero_add]
    rw [hmk]
    have hle : Submodule.map N.mkQ (Submodule.span R (↑(C j) : Set X)) ≤ Submodule.span R
        (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X))) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨(C j).equivFin ⟨y, hy⟩, by simp⟩
    exact hle ⟨c, hc, rfl⟩
  have hE0 : Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞) :=
    length_le_sum_of_antitone_chain_quot_le V E (fun j => S * (C j).card) hEV hEmono
      (fun j hj => length_quot_comap_le_mul_of_pow_smul_mem π hπ S _ (E j) (E (j + 1)) (hEstep j) _ (hEspan j hj))
  have hA0 : Module.length R A0 ≤ Module.length R (E 0) :=
    Module.length_le_of_injective θA hθinj
  have hL : Module.length R (M ⧸ K) ≤
      ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞) := by
    rw [length_eq_length_add_length_quot A0, Nat.cast_add]
    exact (add_le_add (hA0.trans hE0) hQ).trans (le_of_eq (add_comm _ _))
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hL)
  refine ⟨ℓ, hℓ.symm, ?_⟩
  have hℓT : ℓ ≤ τ * d + ∑ j ∈ Finset.range V, S * (C j).card := by
    rw [← hℓ] at hL
    exact_mod_cast hL
  have hgeom : ∀ W : ℕ, ∑ j ∈ Finset.range W, s ^ (j + 1) ≤ 2 * s - 2 * s ^ (W + 1) := by
    intro W
    induction W with
    | zero => simp
    | succ W ih =>
      rw [Finset.sum_range_succ]
      have h3 : 0 ≤ s ^ (W + 1) * (1 - 2 * s) := mul_nonneg (pow_nonneg hs0 _) (by linarith)
      have h4 : s ^ (W + 1 + 1) = s ^ (W + 1) * s := pow_succ s (W + 1)
      nlinarith [h3, h4]
  have hsumC : ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) ≤
      ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hCcard j (Finset.mem_range.mp hj)) (Nat.cast_nonneg _)
  have e1 : ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) =
      ((S : ℝ) * d) * ∑ j ∈ Finset.range V, s ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSd : (0 : ℝ) ≤ (S : ℝ) * d := by positivity
  have hg2 : ∑ j ∈ Finset.range V, s ^ (j + 1) ≤ 2 * s := by
    have h5 := hgeom V
    have h6 := pow_nonneg hs0 (V + 1)
    linarith
  have hfin := mul_le_mul_of_nonneg_left hg2 hSd
  have hcast : (ℓ : ℝ) ≤ (τ : ℝ) * d + ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) := by
    have h7 : ((ℓ : ℕ) : ℝ) ≤ ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℝ) := by
      exact_mod_cast hℓT
    push_cast at h7
    exact h7
  nlinarith [hcast, hsumC, e1, hfin]
end Formalism.G0.CyclicSpanLengthLemmas
