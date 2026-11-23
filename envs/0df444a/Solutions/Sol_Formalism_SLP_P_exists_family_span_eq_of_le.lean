-- Prove2me | solution 1 for Formalism.SLP.P.exists_family_span_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:37.096302+00:00
-- url     : https://prove2.me/submissions/6e28c439-e7f8-4b48-897f-801fb06883b9

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
noncomputable section
namespace Formalism.SLP.P
private theorem exists_span_singleton_eq_of_le_span_singleton {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] (v : M) (N : Submodule R M)
    (hN : N ≤ R ∙ v) : ∃ t : M, (R ∙ t) = N := by
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M v
  let I : Ideal R := N.comap f
  let J : Ideal R := LinearMap.ker f
  have hJI : J ≤ I := fun r hr => by
    show f r ∈ N
    rw [LinearMap.mem_ker.1 hr]
    exact N.zero_mem
  have key : ∃ x, J ⊔ Ideal.span {x} = I := by
    by_cases hJ : J = ⊥
    ·
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hJ
      haveI : Finite R := Finite.of_injective f hinj
      have hF : IsField R := Finite.isField_of_domain R
      by_cases hI : I = ⊥
      · exact ⟨0, by rw [hJ, hI]; simp⟩
      · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
        obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
        have hIt : I = ⊤ := (Ideal.eq_top_iff_one I).2 (by rw [← hb]; exact I.mul_mem_right b ha)
        exact ⟨1, by rw [hIt, Ideal.span_singleton_one, sup_top_eq]⟩
    · exact IsDedekindDomain.exists_sup_span_eq hJI hJ
  obtain ⟨x, hx⟩ := key
  refine ⟨x • v, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    have hxI : x ∈ I := hx ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hfx : f x ∈ N := hxI
    simpa [f] using hfx
  · intro n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 (hN hn)
    have hr : r ∈ I := by
      show f r ∈ N
      simpa [f] using hn
    rw [← hx, Submodule.mem_sup] at hr
    obtain ⟨j, hj, y, hy, rfl⟩ := hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hjv : j • v = 0 := by simpa [f] using LinearMap.mem_ker.1 hj
    rw [Submodule.mem_span_singleton]
    exact ⟨s, by rw [add_smul, hjv, zero_add, mul_smul]⟩
end Formalism.SLP.P
end
end

set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
namespace Formalism.SLP.P
theorem _root_.solution {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] :
    ∀ (e : ℕ) (v : Fin e → M) (N : Submodule R M), N ≤ Submodule.span R (Set.range v) →
      ∃ t : Fin e → M, Submodule.span R (Set.range t) = N := by
  intro e
  induction e with
  | zero =>
    intro v N hN
    refine ⟨v, ?_⟩
    rw [Set.range_eq_empty v, Submodule.span_empty] at hN ⊢
    exact (le_bot_iff.1 hN).symm
  | succ e ih =>
    intro v N hN
    set S' : Submodule R M := Submodule.span R (Set.range (Fin.tail v)) with hS'
    have hv : Submodule.span R (Set.range v) = (R ∙ v 0) ⊔ S' := by
      conv_lhs => rw [← Fin.cons_self_tail v]
      rw [Fin.range_cons, Submodule.span_insert]
    haveI : Finite (M ⧸ S') := Finite.of_surjective _ (Submodule.mkQ_surjective S')

    have hπ : N.map S'.mkQ ≤ R ∙ S'.mkQ (v 0) := by
      rw [Submodule.map_le_iff_le_comap]
      intro n hn
      have h := hN hn
      rw [hv, Submodule.mem_sup] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 ha
      rw [Submodule.mem_comap, map_add, map_smul]
      have hb0 : S'.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero S').2 hb
      rw [hb0, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨t', ht'⟩ := exists_span_singleton_eq_of_le_span_singleton (S'.mkQ (v 0)) (N.map S'.mkQ) hπ
    have ht'm : t' ∈ N.map S'.mkQ := ht' ▸ Submodule.mem_span_singleton_self t'
    obtain ⟨n0, hn0, hn0t⟩ := ht'm
    obtain ⟨u, hu⟩ := ih (Fin.tail v) (N ⊓ S') inf_le_right
    refine ⟨Fin.cons n0 u, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, hu]
    apply le_antisymm
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hn0) inf_le_left
    · intro n hn
      have hπn : S'.mkQ n ∈ R ∙ S'.mkQ n0 := by
        rw [hn0t, ht']
        exact Submodule.mem_map_of_mem hn
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hπn
      have hd : n - r • n0 ∈ S' := by
        have h0 : S'.mkQ (n - r • n0) = 0 := by rw [map_sub, map_smul, hr, sub_self]
        exact (Submodule.Quotient.mk_eq_zero S').1 h0
      rw [Submodule.mem_sup]
      exact ⟨r • n0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), n - r • n0,
        ⟨N.sub_mem hn (N.smul_mem _ hn0), hd⟩, by abel⟩
end Formalism.SLP.P
