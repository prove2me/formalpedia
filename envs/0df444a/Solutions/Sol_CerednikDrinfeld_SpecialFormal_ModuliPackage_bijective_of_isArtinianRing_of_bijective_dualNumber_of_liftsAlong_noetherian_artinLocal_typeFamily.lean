-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b63100c1-51e3-5505-a5ee-76a8a03822a7

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem
import Theorems.Thm_IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_ringEquiv_noetherian_typeFamily
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily

set_option autoImplicit false

universe u v

open CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (k : Type) [Field k] [CharP k p]

    (Gobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type u)
    (Gmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Gobj B ψ hB → Gobj B' ψ' hB')
    (Gmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Gobj B ψ hB),
      Gmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Gmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Gobj B ψ hB),
      Gmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Gmap hB' hB'' g hg (Gmap hB hB' f hf x))
    (Hobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type v)
    (Hmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Hobj B ψ hB → Hobj B' ψ' hB')
    (Hmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Hobj B ψ hB),
      Hmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Hmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Hobj B ψ hB),
      Hmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Hmap hB' hB'' g hg (Hmap hB hB' f hf x))
    (ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Gobj B ψ hB → Hobj B ψ hB)
    (hξ : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (f : B →+* B') (hf : f.comp ψ = ψ') (x : Gobj B ψ hB),
      ξ B' ψ' hB' (Gmap hB hB' f hf x) = Hmap hB hB' f hf (ξ B ψ hB x))

    (hG : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Gobj B' ψ' hB') (x'' : Gobj B'' ψ'' hB''),
        Gmap hB' hB φ' hφ' x' = Gmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Gobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Gmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Gmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hH : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Hobj B' ψ' hB') (x'' : Hobj B'' ψ'' hB''),
        Hmap hB' hB φ' hφ' x' = Hmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Hobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Hmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Hmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hlift : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_hφs : Function.Surjective φ)
      (_hφ2 : RingHom.ker φ * RingHom.ker φ = ⊥) (x : Gobj B ψ hB),
      (∃ y' : Hobj B' ψ' hB', Hmap hB' hB φ hφ y' = ξ B ψ hB x) → ∃ x' : Gobj B' ψ' hB', Gmap hB' hB φ hφ x' = x)

    (hpt : ∀ (ψk : O →+* k) (hk : IsNilpotent (p : k)), Function.Bijective (ξ k ψk hk))

    (htan : ∀ (ψk : O →+* k) (hkε : IsNilpotent (p : DualNumber k)),
      Function.Bijective (ξ (DualNumber k) ((algebraMap k (DualNumber k)).comp ψk) hkε))

    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (ρ : B →+* k) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = IsLocalRing.maximalIdeal B) :
    Function.Bijective (ξ B ψ hB) := by
  classical

  have nilmap : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S), IsNilpotent (p : R) → IsNilpotent (p : S) := by
    intro R S _ _ f h; obtain ⟨n, hn⟩ := h; exact ⟨n, by rw [← map_natCast f, ← map_pow, hn, map_zero]⟩

  have nilsub : ∀ {R S : Type} [CommRing R] [CommRing S] (P : Subring (R × S)), IsNilpotent (p : R) → IsNilpotent (p : S) →
      IsNilpotent (p : P) := by
    intro R S _ _ P hR hS
    obtain ⟨a, ha⟩ := hR; obtain ⟨b, hb⟩ := hS
    refine ⟨a + b, Subtype.ext ?_⟩
    show ((p : P) ^ (a + b)).1 = 0
    rw [SubmonoidClass.coe_pow]
    show ((p : R × S)) ^ (a + b) = 0
    ext
    · show (p : R) ^ (a + b) = 0
      rw [pow_add, ha, zero_mul]
    · show (p : S) ^ (a + b) = 0
      rw [pow_add, hb, mul_zero]

  suffices main : ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
      (ρ : B →+* k), Function.Surjective ρ → RingHom.ker ρ = IsLocalRing.maximalIdeal B → Module.length B B ≤ n →
      Function.Bijective (ξ B ψ hB) by
    refine main (Module.length B B).toNat B ψ hB ρ hρ hρker ?_
    rw [ENat.coe_toNat (Module.length_ne_top (R := B) (M := B))]
  intro n
  induction n with
  | zero =>
    intro B _ _ _ ψ hB ρ hρ hρker hlen
    exfalso
    have h0 : Module.length B B = 0 := nonpos_iff_eq_zero.mp (by exact_mod_cast hlen)
    rw [Module.length_eq_zero_iff] at h0
    exact false_of_nontrivial_of_subsingleton B
  | succ n ih =>
    intro B _ _ _ ψ hB ρ hρ hρker hlen
    have hk : IsNilpotent (p : k) := nilmap ρ hB
    by_cases hm : IsLocalRing.maximalIdeal B = ⊥
    ·
      have hinj : Function.Injective ρ := by
        rw [RingHom.injective_iff_ker_eq_bot, hρker, hm]
      let e : B ≃+* k := RingEquiv.ofBijective ρ ⟨hinj, hρ⟩
      exact CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_ringEquiv_noetherian_typeFamily Gobj Gmap Gmap_id Gmap_comp Hobj Hmap Hmap_id Hmap_comp ξ hξ ψ hB hk e (hpt (e.toRingHom.comp ψ) hk)
    ·
      obtain ⟨t, ht0, htm, hann⟩ := IsArtinianRing.exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero B hm
      let I : Ideal B := Ideal.span {t}
      have hIt : I ≤ IsLocalRing.maximalIdeal B := by
        rw [Ideal.span_le]; rintro _ rfl; exact htm
      have hIne : I ≠ ⊤ := fun h => IsLocalRing.maximalIdeal.isMaximal B |>.ne_top (top_le_iff.mp (h ▸ hIt))
      have hI0 : I ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact ht0
      haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
      haveI : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      let φ : B →+* B ⧸ I := Ideal.Quotient.mk I
      have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
      have hkerφ : RingHom.ker φ = Ideal.span {t} := Ideal.mk_ker
      have hB₂ : IsNilpotent (p : B ⧸ I) := nilmap φ hB

      have hIρ : ∀ a ∈ I, ρ a = 0 := fun a ha => by
        have : a ∈ RingHom.ker ρ := hρker ▸ hIt ha
        exact this
      let ρ₂ : B ⧸ I →+* k := Ideal.Quotient.lift I ρ hIρ
      have hρ₂ : Function.Surjective ρ₂ := by
        intro y; obtain ⟨b, rfl⟩ := hρ y; exact ⟨φ b, rfl⟩
      have hρ₂ker : RingHom.ker ρ₂ = IsLocalRing.maximalIdeal (B ⧸ I) :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ρ₂ hρ₂)

      have hlen₂ : Module.length (B ⧸ I) (B ⧸ I) ≤ n := by
        have h1 : Module.length B (B ⧸ I) < Module.length B B := Submodule.length_quotient_lt (I.restrictScalars B) (by simpa using hI0)
        rw [Module.length_eq_of_surjective (S := B) (R := B ⧸ I) (M := B ⧸ I) Ideal.Quotient.mk_surjective] at h1
        have h2 : Module.length (B ⧸ I) (B ⧸ I) < (n : ℕ∞) + 1 := lt_of_lt_of_le h1 (by exact_mod_cast hlen)
        exact (ENat.lt_add_one_iff (ENat.coe_ne_top n)).mp h2

      have hξ₂ : Function.Bijective (ξ (B ⧸ I) (φ.comp ψ) hB₂) := ih (B ⧸ I) (φ.comp ψ) hB₂ ρ₂ hρ₂ hρ₂ker hlen₂

      have hfst : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp (ρ.comp ψ)) = ρ.comp ψ := by
        ext x; simp
      have htker : t ∈ RingHom.ker ρ := hρker ▸ htm
      have hann' : ∀ m ∈ RingHom.ker ρ, m * t = 0 := fun m hm' => hann m (hρker ▸ hm')
      obtain ⟨e, he₁, heStr, hsnd⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem ψ φ hφ ρ hρ t ht0 hkerφ htker hann' hfst

      have hkε : IsNilpotent (p : DualNumber k) := nilmap (algebraMap k (DualNumber k)) hk
      have hφnil : IsNilpotent (RingHom.ker φ) := by
        refine ⟨2, ?_⟩
        rw [hkerφ, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact hann t htm
      have hφsq : RingHom.ker φ * RingHom.ker φ = ⊥ := by
        rw [hkerφ, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_bot]; exact hann t htm
      have hρnil : IsNilpotent (RingHom.ker ρ) := by
        rw [hρker]
        obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
        rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
        exact ⟨N, hN⟩
      have hP : IsNilpotent (p : pullbackRing ρ (TrivSqZeroExt.fstHom k k k).toRingHom) := nilsub _ hB hkε
      have hQ : IsNilpotent (p : pullbackRing φ φ) := nilsub _ hB hB

      exact CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily p Gobj Gmap Gmap_id Gmap_comp Hobj Hmap Hmap_id Hmap_comp ξ hξ hG hH hlift k ψ hB φ hφ hφnil hφsq hB₂ ρ hρ hρnil hk hkε hfst hP hQ e he₁ heStr hsnd
        hξ₂ (hpt (ρ.comp ψ) hk) (htan (ρ.comp ψ) hkε)

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily (solution)
