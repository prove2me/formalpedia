-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.exists_forall_map_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/90f536a3-f927-5152-a620-8bd88829d019

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_Localization_Away_existsUnique_forall_algebraMap_eq_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_exists_forall_map_eq_of_span_eq_top

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace GPointGlueAux

open CerednikDrinfeld.SpecialFormal.ModuliPackage

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {M : ModuliPackage.{0, 0} p O}

theorem map_heq_map {B B' : Type} [CommRing B] [CommRing B'] {χ₁ χ₂ : O →+* B} {χ'₁ χ'₂ : O →+* B'}
    (n₁ : IsNilpotent (p : B)) (n₂ : IsNilpotent (p : B)) (n'₁ n'₂ : IsNilpotent (p : B'))
    (f₁ f₂ : B →+* B') (h₁ : f₁.comp χ₁ = χ'₁) (h₂ : f₂.comp χ₂ = χ'₂)
    (m₁ : M.obj B χ₁ n₁) (m₂ : M.obj B χ₂ n₂) (ef : f₁ = f₂) (e : χ₁ = χ₂) (hm : HEq m₁ m₂) :
    HEq (M.map n₁ n'₁ f₁ h₁ m₁) (M.map n₂ n'₂ f₂ h₂ m₂) := by
  subst ef e
  have e' : χ'₁ = χ'₂ := h₁.symm.trans h₂
  subst e'
  have hm' : m₁ = m₂ := eq_of_heq hm
  subst hm'
  rfl

theorem map_id_heq {B : Type} [CommRing B] {χ χ' : O →+* B} (hB hB' : IsNilpotent (p : B))
    (h : (RingHom.id B).comp χ = χ') (m : M.obj B χ hB) :
    HEq (M.map hB hB' (RingHom.id B) h m) m := by
  have e : χ' = χ := h.symm.trans (RingHom.id_comp χ)
  subst e
  exact heq_of_eq (M.map_id hB m)

theorem pt_heq_of_eq {𝒪 : Type} [CommRing 𝒪] [Algebra 𝒪 O] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {x y : GPoint 𝒪 M B} (h : x = y) : HEq x.pt y.pt := by
  cases h; rfl

end GPointGlueAux

open GPointGlueAux in
theorem solution
    {p : ℕ} [Fact p.Prime] {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]
    {M : ModuliPackage.{0, 0} p O} (hM : M.IsZariskiSheaf)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (p : B))
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra 𝒪 (L i)] [∀ i, Algebra B (L i)] [∀ i, IsScalarTower 𝒪 B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)]
    (L₂ : Fin n → Fin n → Type) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra 𝒪 (L₂ i j)] [∀ i j, Algebra B (L₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (L₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (l : ∀ i j, L i →ₐ[𝒪] L₂ i j) (r : ∀ i j, L j →ₐ[𝒪] L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b)
    (x : ∀ i, ModuliPackage.GPoint 𝒪 M (L i))
    (hx : ∀ i j, (x i).map (l i j) = (x j).map (r i j)) :
    ∃ y : ModuliPackage.GPoint 𝒪 M B, ∀ i, y.map (IsScalarTower.toAlgHom 𝒪 B (L i)) = x i := by
  classical

  have hL : ∀ i, IsNilpotent (p : L i) := fun i => by
    simpa only [map_natCast] using hB.map (algebraMap B (L i))
  have hL₂ : ∀ i j, IsNilpotent (p : L₂ i j) := fun i j => by
    simpa only [map_natCast] using hB.map (algebraMap B (L₂ i j))

  have hleg : ∀ b₁ b₂ : B, (∀ i, algebraMap B (L i) b₁ = algebraMap B (L i) b₂) → b₁ = b₂ := by
    intro b₁ b₂ hb
    suffices hs : Module.eqIdeal B b₁ b₂ = ⊤ by
      simpa [Module.eqIdeal] using (Ideal.eq_top_iff_one _).mp hs
    by_contra hne
    obtain ⟨s, hrs, disj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top _ hf _ hne
    obtain ⟨i, rfl⟩ := hrs
    obtain ⟨⟨c, n', hn'⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f i)) (L i)).mp (hb i)
    refine Set.disjoint_left.mp disj ?_ ⟨n', hn'⟩
    show c • b₁ = c • b₂
    simpa [smul_eq_mul] using hc

  have glue : ∀ z : ∀ i, L i, (∀ i j, l i j (z i) = r i j (z j)) → ∃ b : B, ∀ i, algebraMap B (L i) b = z i := by
    intro z hz
    let e : ∀ i, Localization.Away (f i) ≃ₐ[B] L i :=
      fun i => Localization.algEquiv (Submonoid.powers (f i)) (L i)
    let e₂ : ∀ i j, Localization.Away (f i * f j) ≃ₐ[B] L₂ i j :=
      fun i j => Localization.algEquiv (Submonoid.powers (f i * f j)) (L₂ i j)
    have kR : ∀ i j,
        (IsLocalization.Away.awayToAwayRight (f i) (f j) :
            Localization.Away (f i) →+* Localization.Away (f i * f j)) =
          ((e₂ i j).symm : L₂ i j →+* Localization.Away (f i * f j)).comp
            ((l i j : L i →+* L₂ i j).comp (e i : Localization.Away (f i) →+* L i)) := by
      intro i j
      apply IsLocalization.ringHom_ext (Submonoid.powers (f i))
      ext b
      simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq]
      rw [show ((e i : Localization.Away (f i) →+* L i)) (algebraMap B (Localization.Away (f i)) b) =
          algebraMap B (L i) b from (e i).commutes b]
      rw [show ((l i j : L i →+* L₂ i j)) (algebraMap B (L i) b) = algebraMap B (L₂ i j) b from hl i j b]
      exact ((e₂ i j).symm.commutes b).symm
    have kL : ∀ i j,
        (IsLocalization.Away.awayToAwayLeft (f j) (f i) :
            Localization.Away (f j) →+* Localization.Away (f i * f j)) =
          ((e₂ i j).symm : L₂ i j →+* Localization.Away (f i * f j)).comp
            ((r i j : L j →+* L₂ i j).comp (e j : Localization.Away (f j) →+* L j)) := by
      intro i j
      apply IsLocalization.ringHom_ext (Submonoid.powers (f j))
      ext b
      simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayLeft_eq]
      rw [show ((e j : Localization.Away (f j) →+* L j)) (algebraMap B (Localization.Away (f j)) b) =
          algebraMap B (L j) b from (e j).commutes b]
      rw [show ((r i j : L j →+* L₂ i j)) (algebraMap B (L j) b) = algebraMap B (L₂ i j) b from hr i j b]
      exact ((e₂ i j).symm.commutes b).symm
    obtain ⟨b, hb, -⟩ :=
      Localization.Away.existsUnique_forall_algebraMap_eq_of_span_eq_top f hf (fun i => (e i).symm (z i)) (by
        intro i j
        have h1 := congrArg (fun g : Localization.Away (f i) →+* Localization.Away (f i * f j) => g ((e i).symm (z i))) (kR i j)
        have h2 := congrArg (fun g : Localization.Away (f j) →+* Localization.Away (f i * f j) => g ((e j).symm (z j))) (kL i j)
        simp only [RingHom.comp_apply] at h1 h2
        rw [h1, h2]
        show (e₂ i j).symm (l i j (e i ((e i).symm (z i)))) = (e₂ i j).symm (r i j (e j ((e j).symm (z j))))
        rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hz i j])
    refine ⟨b, fun i => ?_⟩
    apply (e i).symm.injective
    rw [← hb i]
    exact (e i).symm.commutes b

  have hψc : ∀ (o : O) i j, l i j ((x i).ψ o) = r i j ((x j).ψ o) := by
    intro o i j
    have h := congrArg ModuliPackage.GPoint.ψ (hx i j)
    simp only [ModuliPackage.GPoint.map_ψ] at h
    exact congrArg (fun g : O →ₐ[𝒪] L₂ i j => g o) h
  choose g hg using fun o => glue (fun i => (x i).ψ o) (hψc o)
  let ψ : O →ₐ[𝒪] B :=
    { toFun := g
      map_one' := hleg _ _ fun i => by rw [hg, map_one, map_one]
      map_mul' := fun a c => hleg _ _ fun i => by rw [hg, map_mul, map_mul, hg, hg]
      map_zero' := hleg _ _ fun i => by rw [hg, map_zero, map_zero]
      map_add' := fun a c => hleg _ _ fun i => by rw [hg, map_add, map_add, hg, hg]
      commutes' := fun c => hleg _ _ fun i => by
        rw [hg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  have hψapp : ∀ o, ψ o = g o := fun _ => rfl
  have hψi : ∀ i, (IsScalarTower.toAlgHom 𝒪 B (L i)).comp ψ = (x i).ψ := fun i =>
    AlgHom.ext fun o => by
      show algebraMap B (L i) (ψ o) = (x i).ψ o
      rw [hψapp, hg]
  have hψi' : ∀ i, (algebraMap B (L i)).comp (ψ : O →+* B) = ((x i).ψ : O →+* L i) := fun i =>
    RingHom.ext fun o => by
      show algebraMap B (L i) (ψ o) = (x i).ψ o
      rw [hψapp, hg]

  let m : ∀ i, M.obj (L i) ((algebraMap B (L i)).comp (ψ : O →+* B)) (hL i) := fun i =>
    M.map (x i).nilp (hL i) (RingHom.id (L i)) ((RingHom.id_comp _).trans (hψi' i).symm) (x i).pt
  have hm : ∀ i, HEq (m i) (x i).pt := fun i => map_id_heq _ _ _ _

  have H1 : ∀ i j, (l i j : L i →+* L₂ i j).comp ((algebraMap B (L i)).comp (ψ : O →+* B)) =
      (algebraMap B (L₂ i j)).comp (ψ : O →+* B) := fun i j =>
    RingHom.ext fun o => hl i j (ψ o)
  have H2 : ∀ i j, (r i j : L j →+* L₂ i j).comp ((algebraMap B (L j)).comp (ψ : O →+* B)) =
      (algebraMap B (L₂ i j)).comp (ψ : O →+* B) := fun i j =>
    RingHom.ext fun o => hr i j (ψ o)
  have hcompat : ∀ i j,
      M.map (ψ' := (algebraMap B (L₂ i j)).comp (ψ : O →+* B)) (hL i) (hL₂ i j) (l i j : L i →+* L₂ i j)
          (RingHom.ext fun b => hl i j (ψ b)) (m i) =
        M.map (ψ' := (algebraMap B (L₂ i j)).comp (ψ : O →+* B)) (hL j) (hL₂ i j) (r i j : L j →+* L₂ i j)
          (RingHom.ext fun b => hr i j (ψ b)) (m j) := by
    intro i j
    apply eq_of_heq
    have k1 : HEq (M.map (ψ' := (algebraMap B (L₂ i j)).comp (ψ : O →+* B)) (hL i) (hL₂ i j) (l i j : L i →+* L₂ i j)
          (RingHom.ext fun b => hl i j (ψ b)) (m i)) ((x i).map (l i j)).pt := by
      rw [ModuliPackage.GPoint.map_pt]
      exact map_heq_map _ _ _ _ _ _ _ _ _ _ rfl (hψi' i) (hm i)
    have k2 : HEq (M.map (ψ' := (algebraMap B (L₂ i j)).comp (ψ : O →+* B)) (hL j) (hL₂ i j) (r i j : L j →+* L₂ i j)
          (RingHom.ext fun b => hr i j (ψ b)) (m j)) ((x j).map (r i j)).pt := by
      rw [ModuliPackage.GPoint.map_pt]
      exact map_heq_map _ _ _ _ _ _ _ _ _ _ rfl (hψi' j) (hm j)
    exact k1.trans ((pt_heq_of_eq (hx i j)).trans k2.symm)

  obtain ⟨mB, hmB⟩ := (hM B (ψ : O →+* B) hB n f hf L hL L₂ hL₂
      (fun i j => (l i j : L i →+* L₂ i j)) (fun i j => (r i j : L j →+* L₂ i j))
      (fun i j b => hl i j b) (fun i j b => hr i j b)).2 m hcompat
  refine ⟨⟨ψ, hB, mB⟩, fun i => ?_⟩
  apply ModuliPackage.GPoint.ext'
  · rw [ModuliPackage.GPoint.map_ψ]
    exact hψi i
  · rw [ModuliPackage.GPoint.map_pt]
    refine HEq.trans ?_ (hm i)
    rw [← hmB i]
    exact map_heq_map _ _ _ _ _ _ _ _ _ _ (IsScalarTower.coe_toAlgHom (R := 𝒪) (S := B) (A := L i)) rfl HEq.rfl

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_exists_forall_map_eq_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_exists_forall_map_eq_of_span_eq_top (solution)
