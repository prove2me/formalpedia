-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b48a734c-1d45-5aaa-b2ba-85ed607158e3

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily

set_option autoImplicit false

universe u v

open CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
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
    (k : Type) [Field k]
    {B B' : Type} [CommRing B] [CommRing B'] [IsLocalRing B'] [IsArtinianRing B'] [IsLocalRing B] [IsArtinianRing B]
    [IsNoetherianRing B] [IsNoetherianRing B']
    (ψ' : O →+* B') (hB' : IsNilpotent (p : B'))
    (φ : B' →+* B) (hφ : Function.Surjective φ) (hφnil : IsNilpotent (RingHom.ker φ))
    (hφsq : RingHom.ker φ * RingHom.ker φ = ⊥) (hB : IsNilpotent (p : B))
    (ρ' : B' →+* k) (hρ' : Function.Surjective ρ') (hρ'nil : IsNilpotent (RingHom.ker ρ'))
    (hk : IsNilpotent (p : k)) (hkε : IsNilpotent (p : DualNumber k))
    (hfst : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) = ρ'.comp ψ')
    (hP : IsNilpotent (p : pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hQ : IsNilpotent (p : pullbackRing φ φ))
    (e : pullbackRing φ φ ≃+* pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
    (he₁ : (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom).comp e.toRingHom = pullbackFst φ φ)
    (heStr : e.toRingHom.comp (pullbackStr φ φ ψ' ψ' rfl) =
      pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm)
    (hsnd : ((pullbackSnd φ φ).comp e.symm.toRingHom).comp
      (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) = ψ')

    (hξB : Function.Bijective (ξ B (φ.comp ψ') hB))
    (hξk : Function.Bijective (ξ k (ρ'.comp ψ') hk))
    (hξε : Function.Bijective (ξ (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε)) :
    Function.Bijective (ξ B' ψ' hB') := by
  classical

  haveI noethP : IsNoetherianRing (pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    let δ : B' →+* pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom :=
      pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom (RingHom.id B') ((algebraMap k (DualNumber k)).comp ρ') (by ext b; simp)
    letI : Algebra B' (pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) := δ.toAlgebra
    let ε' : pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom := ⟨(0, TrivSqZeroExt.inr 1), by
      show ρ' 0 = (TrivSqZeroExt.fstHom k k k).toRingHom (TrivSqZeroExt.inr 1); simp⟩
    haveI : Module.Finite B' (pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      refine ⟨⟨{1, ε'}, ?_⟩⟩
      rw [eq_top_iff]
      rintro x -
      obtain ⟨c, hc⟩ := hρ' x.1.2.snd
      have hx : x = x.1.1 • (1 : pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) + c • ε' := by
        apply Subtype.ext
        show x.1 = (δ x.1.1 * 1 + δ c * ε').1
        rw [mul_one]
        apply Prod.ext
        · show x.1.1 = x.1.1 + c * 0; simp
        · show x.1.2 = algebraMap k (DualNumber k) (ρ' x.1.1) + algebraMap k (DualNumber k) (ρ' c) * TrivSqZeroExt.inr 1
          apply TrivSqZeroExt.ext
          · simp [TrivSqZeroExt.algebraMap_eq_inl]; exact x.2.symm
          · simp [TrivSqZeroExt.algebraMap_eq_inl, hc]
      rw [hx]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
    exact Algebra.FiniteType.isNoetherianRing B' (pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)

  have TG := fun x₀' => CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
    p Gobj Gmap Gmap_id Gmap_comp hG k ψ' hB' φ hφ hφnil hB ρ' hρ' hρ'nil hk hkε hfst hP hQ e he₁ heStr hsnd x₀'
  have TH := fun y₀' => CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
    p Hobj Hmap Hmap_id Hmap_comp hH k ψ' hB' φ hφ hφnil hB ρ' hρ' hρ'nil hk hkε hfst hP hQ e he₁ heStr hsnd y₀'

  have nat := fun {C C' : Type} [CommRing C] [CommRing C'] [IsNoetherianRing C] [IsNoetherianRing C'] {ψC : O →+* C} {ψC' : O →+* C'} (hC : IsNilpotent (p : C))
    (hC' : IsNilpotent (p : C')) (f : C →+* C') (hf : f.comp ψC = ψC') (x : Gobj C ψC hC) => hξ C C' ψC ψC' hC hC' f hf x

  have relξ : ∀ (x₀' x' : Gobj B' ψ' hB') (τ : Gobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε),
      (∃ w : Gobj (pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) hP,
        Gmap hP hB' (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) (pullbackFst_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = x₀' ∧
        Gmap hP hB' ((pullbackSnd φ φ).comp e.symm.toRingHom) hsnd w = x' ∧
        Gmap hP hkε (pullbackSnd ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) (pullbackSnd_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = τ) →
      (∃ w : Hobj (pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) hP,
        Hmap hP hB' (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) (pullbackFst_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = ξ B' ψ' hB' x₀' ∧
        Hmap hP hB' ((pullbackSnd φ φ).comp e.symm.toRingHom) hsnd w = ξ B' ψ' hB' x' ∧
        Hmap hP hkε (pullbackSnd ρ' (TrivSqZeroExt.fstHom k k k).toRingHom) (pullbackSnd_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = ξ _ _ hkε τ) := by
    rintro x₀' x' τ ⟨w, h1, h2, h3⟩
    exact ⟨ξ _ _ hP w, by rw [← nat, h1], by rw [← nat, h2], by rw [← nat, h3]⟩
  constructor
  ·
    intro x₁' x₂' h12
    have hx : Gmap hB' hB φ rfl x₂' = Gmap hB' hB φ rfl x₁' := by
      apply hξB.1
      rw [nat, nat, h12]
    obtain ⟨T1, T2⟩ := TG x₁'
    obtain ⟨τ₁, ⟨hτ₁, hR₁⟩, -⟩ := T1 x₁' rfl
    obtain ⟨τ₂, ⟨hτ₂, hR₂⟩, -⟩ := T1 x₂' hx

    obtain ⟨U1, -⟩ := TH (ξ B' ψ' hB' x₁')
    have hσ := U1 (ξ B' ψ' hB' x₁') rfl
    have e12 : ξ _ _ hkε τ₁ = ξ _ _ hkε τ₂ := by
      apply hσ.unique
      · exact ⟨by rw [← nat hkε hk _ hfst τ₁, hτ₁, nat], relξ _ _ _ hR₁⟩
      · refine ⟨by rw [← nat hkε hk _ hfst τ₂, hτ₂, nat], ?_⟩
        have := relξ x₁' x₂' τ₂ hR₂
        rw [← h12] at this
        exact this
    have hτ : τ₁ = τ₂ := hξε.1 e12
    obtain ⟨x', -, huniq⟩ := T2 τ₁ hτ₁
    have e1 := huniq x₁' ⟨rfl, hR₁⟩
    have e2 := huniq x₂' ⟨hx, hτ ▸ hR₂⟩
    rw [e1, e2]
  ·
    intro y'
    obtain ⟨x, hx⟩ := hξB.2 (Hmap hB' hB φ rfl y')

    obtain ⟨x₀', hx₀'⟩ := hlift B B' (φ.comp ψ') ψ' hB hB' φ rfl hφ hφsq x ⟨y', by show Hmap hB' hB φ rfl y' = _; rw [hx]⟩
    have hx₀ : Gmap hB' hB φ rfl x₀' = x := hx₀'

    obtain ⟨U1, U2⟩ := TH (ξ B' ψ' hB' x₀')
    have hy'over : Hmap hB' hB φ rfl y' = Hmap hB' hB φ rfl (ξ B' ψ' hB' x₀') := by
      rw [← nat, hx₀, hx]
    obtain ⟨σ, ⟨hσ, hRσ⟩, -⟩ := U1 y' hy'over

    obtain ⟨τ, rfl⟩ := hξε.2 σ
    have hτ : Gmap hkε hk (TrivSqZeroExt.fstHom k k k).toRingHom hfst τ = Gmap hB' hk ρ' rfl x₀' := by
      apply hξk.1
      rw [nat, nat, hσ]
    obtain ⟨T1, T2⟩ := TG x₀'
    obtain ⟨x', ⟨hx', hRx'⟩, -⟩ := T2 τ hτ
    refine ⟨x', ?_⟩

    have hU := U2 (ξ _ _ hkε τ) hσ
    apply hU.unique
    · exact ⟨by rw [← nat hB' hB φ rfl x', hx', nat], relξ _ _ _ hRx'⟩
    · exact ⟨hy'over, hRσ⟩

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily (solution)
