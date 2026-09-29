-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6c17a188-c76a-5f0a-80d1-6ea68f5cde82

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_isLocalization_away_pullbackRing_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_isNoetherianRing_pullbackRing_of_surjective
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open CerednikDrinfeld.SpecialFormal.ModuliPackage

namespace FpnAux

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (F : ModuliPackage.{0, 0} p O)

theorem map_congr {R S : Type} [CommRing R] [CommRing S] {ψR : O →+* R} {ψS : O →+* S}
    (hR : IsNilpotent (p : R)) (hS : IsNilpotent (p : S)) (g g' : R →+* S) (hg : g.comp ψR = ψS) (hg' : g'.comp ψR = ψS)
    (h : g = g') (z : F.obj R ψR hR) : F.map hR hS g hg z = F.map hR hS g' hg' z := by
  subst h; rfl

theorem map_map {R S T : Type} [CommRing R] [CommRing S] [CommRing T] {ψR : O →+* R} {ψS : O →+* S} {ψT : O →+* T}
    (hR : IsNilpotent (p : R)) (hS : IsNilpotent (p : S)) (hT : IsNilpotent (p : T))
    (f : R →+* S) (g : S →+* T) (g' : R →+* T) (hf : f.comp ψR = ψS) (hg : g.comp ψS = ψT) (hg' : g'.comp ψR = ψT)
    (h : g.comp f = g') (z : F.obj R ψR hR) : F.map hS hT g hg (F.map hR hS f hf z) = F.map hR hT g' hg' z := by
  rw [← F.map_comp hR hS hT g f hf hg z]
  exact map_congr F hR hT _ _ _ _ h z

omit F in
omit [Fact p.Prime] in
theorem nilmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : IsNilpotent (p : R)) :
    IsNilpotent (p : S) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n, by rw [← map_natCast f, ← map_pow, hn, map_zero]⟩

omit F in

theorem span_prod_eq_top {R : Type} [CommSemiring R] {n₁ n₂ : ℕ} (f₁ : Fin n₁ → R) (f₂ : Fin n₂ → R)
    (h₁ : Ideal.span (Set.range f₁) = ⊤) (h₂ : Ideal.span (Set.range f₂) = ⊤) :
    Ideal.span (Set.range (fun k : Fin (n₁ * n₂) => f₁ (finProdFinEquiv.symm k).1 * f₂ (finProdFinEquiv.symm k).2)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : R) ∈ Ideal.span (Set.range f₁) * Ideal.span (Set.range f₂) := by
    rw [h₁, h₂, Ideal.top_mul]; trivial
  rw [Ideal.span_mul_span'] at h
  refine Ideal.span_mono ?_ h
  rintro x ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
  exact ⟨finProdFinEquiv (i, j), by simp⟩

end FpnAux

namespace FpnModel

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  (φ' : B' →+* B) (φ'' : B'' →+* B) (g : pullbackRing φ' φ'')

abbrev Bl : Type := Localization.Away (φ' g.1.1)

abbrev B'l : Type := Localization.Away g.1.1

abbrev B''l : Type := Localization.Away g.1.2

noncomputable def φ'l : B'l φ' φ'' g →+* Bl φ' φ'' g := IsLocalization.Away.map _ _ φ' g.1.1

theorem powers_le : Submonoid.powers g.1.2 ≤ (Submonoid.powers (φ' g.1.1)).comap φ'' := by
  rintro x ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  simp only [map_pow]
  rw [show φ' g.1.1 = φ'' g.1.2 from g.2]

noncomputable def φ''l : B''l φ' φ'' g →+* Bl φ' φ'' g :=
  IsLocalization.map (M := Submonoid.powers g.1.2) (T := Submonoid.powers (φ' g.1.1)) _ φ'' (powers_le φ' φ'' g)

theorem φ'l_comp : (φ'l φ' φ'' g).comp (algebraMap B' (B'l φ' φ'' g)) = (algebraMap B (Bl φ' φ'' g)).comp φ' := by
  unfold φ'l IsLocalization.Away.map
  exact IsLocalization.map_comp (M := Submonoid.powers g.1.1) _

theorem φ''l_comp : (φ''l φ' φ'' g).comp (algebraMap B'' (B''l φ' φ'' g)) = (algebraMap B (Bl φ' φ'' g)).comp φ'' := by
  unfold φ''l
  exact IsLocalization.map_comp (M := Submonoid.powers g.1.2) _

abbrev L : Type := pullbackRing (φ'l φ' φ'' g) (φ''l φ' φ'' g)

noncomputable def δ : pullbackRing φ' φ'' →+* L φ' φ'' g :=
  (RingHom.prod ((algebraMap B' (B'l φ' φ'' g)).comp (pullbackFst φ' φ''))
      ((algebraMap B'' (B''l φ' φ'' g)).comp (pullbackSnd φ' φ''))).codRestrict
    (pullbackRing (φ'l φ' φ'' g) (φ''l φ' φ'' g)) (fun z => by
      show φ'l φ' φ'' g (algebraMap B' (B'l φ' φ'' g) z.1.1) = φ''l φ' φ'' g (algebraMap B'' (B''l φ' φ'' g) z.1.2)
      rw [← RingHom.comp_apply, φ'l_comp, ← RingHom.comp_apply, φ''l_comp, RingHom.comp_apply, RingHom.comp_apply,
        show φ' z.1.1 = φ'' z.1.2 from z.2])

theorem δ_fst : (pullbackFst (φ'l φ' φ'' g) (φ''l φ' φ'' g)).comp (δ φ' φ'' g) =
    (algebraMap B' (B'l φ' φ'' g)).comp (pullbackFst φ' φ'') := RingHom.ext fun _ => rfl

theorem δ_snd : (pullbackSnd (φ'l φ' φ'' g) (φ''l φ' φ'' g)).comp (δ φ' φ'' g) =
    (algebraMap B'' (B''l φ' φ'' g)).comp (pullbackSnd φ' φ'') := RingHom.ext fun _ => rfl

noncomputable scoped instance alg : Algebra (pullbackRing φ' φ'') (L φ' φ'' g) := (δ φ' φ'' g).toAlgebra

theorem algebraMap_eq : algebraMap (pullbackRing φ' φ'') (L φ' φ'' g) = δ φ' φ'' g := rfl

theorem locCart :
    IsLocalization.Away g (L φ' φ'' g) ∧
    (Function.Surjective φ' → Function.Surjective (φ'l φ' φ'' g)) ∧
    (Function.Surjective φ'' → Function.Surjective (φ''l φ' φ'' g)) ∧
    (IsNilpotent (RingHom.ker φ') → IsNilpotent (RingHom.ker (φ'l φ' φ'' g))) ∧
    (IsNilpotent (RingHom.ker φ'') → IsNilpotent (RingHom.ker (φ''l φ' φ'' g))) :=
  CerednikDrinfeld.SpecialFormal.ModuliPackage.isLocalization_away_pullbackRing_of_comp_eq φ' φ'' g
    (Bl φ' φ'' g) (B'l φ' φ'' g) (B''l φ' φ'' g) (φ'l φ' φ'' g) (φ''l φ' φ'' g) (φ'l_comp φ' φ'' g) (φ''l_comp φ' φ'' g)
    (δ φ' φ'' g) (δ_fst φ' φ'' g) (δ_snd φ' φ'' g)

scoped instance loc : IsLocalization.Away g (L φ' φ'' g) := (locCart φ' φ'' g).1

theorem φ'l_surjective (h : Function.Surjective φ') : Function.Surjective (φ'l φ' φ'' g) := (locCart φ' φ'' g).2.1 h
theorem φ''l_surjective (h : Function.Surjective φ'') : Function.Surjective (φ''l φ' φ'' g) := (locCart φ' φ'' g).2.2.1 h
theorem φ'l_ker (h : IsNilpotent (RingHom.ker φ')) : IsNilpotent (RingHom.ker (φ'l φ' φ'' g)) := (locCart φ' φ'' g).2.2.2.1 h
theorem φ''l_ker (h : IsNilpotent (RingHom.ker φ'')) : IsNilpotent (RingHom.ker (φ''l φ' φ'' g)) := (locCart φ' φ'' g).2.2.2.2 h

theorem isNoetherianRing_L [IsNoetherianRing B'] [IsNoetherianRing B''] (hs' : Function.Surjective φ')
    (hs'' : Function.Surjective φ'') : IsNoetherianRing (L φ' φ'' g) :=
  CerednikDrinfeld.SpecialFormal.ModuliPackage.isNoetherianRing_pullbackRing_of_surjective _ _
    (φ'l_surjective φ' φ'' g hs') (φ''l_surjective φ' φ'' g hs'')

end FpnModel
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf.FpnModel"

namespace FpnAux2
open CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem span_eq_top_of_surjective_of_isNilpotent_ker {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hn : IsNilpotent (RingHom.ker f)) (s : Set R)
    (h : Ideal.span (f '' s) = ⊤) : Ideal.span s = ⊤ := by
  have h1 : (1 : S) ∈ Ideal.map f (Ideal.span s) := by rw [Ideal.map_span, h]; trivial
  obtain ⟨x, hx, hfx⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp h1
  have hker : x - 1 ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_sub, hfx, map_one, sub_self]
  obtain ⟨N, hN⟩ := hn
  have hnil : IsNilpotent (x - 1) := ⟨N, by
    have := Ideal.pow_mem_pow hker N
    rw [hN] at this
    exact this⟩
  have hu : IsUnit x := by
    have := hnil.isUnit_add_one
    rwa [sub_add_cancel] at this
  exact Ideal.eq_top_of_isUnit_mem _ hx hu

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] (φ' : B' →+* B) (φ'' : B'' →+* B)

theorem pullbackFst_surjective (hs'' : Function.Surjective φ'') : Function.Surjective (pullbackFst φ' φ'') := by
  intro b'
  obtain ⟨b'', hb''⟩ := hs'' (φ' b')
  exact ⟨⟨(b', b''), hb''.symm⟩, rfl⟩

theorem pullbackSnd_surjective (hs' : Function.Surjective φ') : Function.Surjective (pullbackSnd φ' φ'') := by
  intro b''
  obtain ⟨b', hb'⟩ := hs' (φ'' b'')
  exact ⟨⟨(b', b''), hb'⟩, rfl⟩

theorem isNilpotent_ker_pullbackFst (hn'' : IsNilpotent (RingHom.ker φ'')) :
    IsNilpotent (RingHom.ker (pullbackFst φ' φ'')) := by
  obtain ⟨N, hN⟩ := hn''
  refine ⟨N + 1, ?_⟩
  rw [Submodule.zero_eq_bot] at hN ⊢
  rw [eq_bot_iff]
  have h1 : RingHom.ker (pullbackFst φ' φ'') ≤ Ideal.comap (pullbackSnd φ' φ'') (RingHom.ker φ'') := by
    intro z hz
    rw [RingHom.mem_ker] at hz
    show φ'' z.1.2 = 0
    rw [← show φ' z.1.1 = φ'' z.1.2 from z.2, show z.1.1 = 0 from hz, map_zero]
  intro z hz
  have hz1 : z ∈ RingHom.ker (pullbackFst φ' φ'') := Ideal.pow_le_self (Nat.succ_ne_zero N) hz
  have hz2 : z ∈ Ideal.comap (pullbackSnd φ' φ'') (RingHom.ker φ'' ^ (N + 1)) :=
    Ideal.le_comap_pow _ (N + 1) (Ideal.pow_right_mono h1 (N + 1) hz)
  rw [Ideal.mem_comap] at hz2
  have hz2' : pullbackSnd φ' φ'' z ∈ RingHom.ker φ'' ^ N := Ideal.pow_le_pow_right (Nat.le_succ N) hz2
  rw [hN, Submodule.mem_bot] at hz2'
  rw [Submodule.mem_bot]
  exact Subtype.ext (Prod.ext hz1 hz2')

theorem isNilpotent_ker_pullbackSnd (hn' : IsNilpotent (RingHom.ker φ')) :
    IsNilpotent (RingHom.ker (pullbackSnd φ' φ'')) := by
  obtain ⟨N, hN⟩ := hn'
  refine ⟨N + 1, ?_⟩
  rw [Submodule.zero_eq_bot] at hN ⊢
  rw [eq_bot_iff]
  have h1 : RingHom.ker (pullbackSnd φ' φ'') ≤ Ideal.comap (pullbackFst φ' φ'') (RingHom.ker φ') := by
    intro z hz
    rw [RingHom.mem_ker] at hz
    show φ' z.1.1 = 0
    rw [show φ' z.1.1 = φ'' z.1.2 from z.2, show z.1.2 = 0 from hz, map_zero]
  intro z hz
  have hz1 : z ∈ RingHom.ker (pullbackSnd φ' φ'') := Ideal.pow_le_self (Nat.succ_ne_zero N) hz
  have hz2 : z ∈ Ideal.comap (pullbackFst φ' φ'') (RingHom.ker φ' ^ (N + 1)) :=
    Ideal.le_comap_pow _ (N + 1) (Ideal.pow_right_mono h1 (N + 1) hz)
  rw [Ideal.mem_comap] at hz2
  have hz2' : pullbackFst φ' φ'' z ∈ RingHom.ker φ' ^ N := Ideal.pow_le_pow_right (Nat.le_succ N) hz2
  rw [hN, Submodule.mem_bot] at hz2'
  rw [Submodule.mem_bot]
  exact Subtype.ext (Prod.ext hz2' hz1)

end FpnAux2
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf.FpnModel"

set_option maxHeartbeats 3200000 in
theorem ex_piece
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} p (WittVector p k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB)
    (hηi : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
      (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hηn : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
      η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (ψ'' : WittVector p k →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
    (hn' : IsNilpotent (RingHom.ker φ')) (hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : pullbackRing φ' φ''))
    (ψP : WittVector p k →+* pullbackRing φ' φ'')
    (hψP' : (pullbackFst φ' φ'').comp ψP = ψ')
    (hψP'' : (pullbackSnd φ' φ'').comp ψP = ψ'')
    (x' : M.obj B' ψ' hB') (x'' : M.obj B'' ψ'' hB'')
    (hx : M.map hB' hB φ' hφ' x' = M.map hB'' hB φ'' hφ'' x'')
    (g : pullbackRing φ' φ'') (a' : B') (b'' : B'') (hda : a' ∣ g.1.1) (hdb : b'' ∣ g.1.2)
    (Ha : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra B' R] [IsLocalization.Away a' R]
      (hR : IsNilpotent (p : R)), ∃ t : Rigidified p Φ R,
        t.IsAdmissible ι ((algebraMap B' R).comp ψ') ∧
        η R ((algebraMap B' R).comp ψ') hR t = M.map (ψ' := (algebraMap B' R).comp ψ') hB' hR (algebraMap B' R) rfl x')
    (Hb : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra B'' R] [IsLocalization.Away b'' R]
      (hR : IsNilpotent (p : R)), ∃ t : Rigidified p Φ R,
        t.IsAdmissible ι ((algebraMap B'' R).comp ψ'') ∧
        η R ((algebraMap B'' R).comp ψ'') hR t = M.map (ψ' := (algebraMap B'' R).comp ψ'') hB'' hR (algebraMap B'' R) rfl x'')
    (hL : IsNilpotent (p : FpnModel.L φ' φ'' g))
    (hB'l : IsNilpotent (p : FpnModel.B'l φ' φ'' g))
    (hB''l : IsNilpotent (p : FpnModel.B''l φ' φ'' g))
    (ef : (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)).comp
      ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
      (algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ')
    (es : (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)).comp
      ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
      (algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'') :
    ∃ zL : M.obj (FpnModel.L φ' φ'' g) ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) hL,
      M.map hL hB'l (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)) ef zL =
        M.map hB' hB'l (algebraMap B' (FpnModel.B'l φ' φ'' g)) rfl x' ∧
      M.map hL hB''l (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)) es zL =
        M.map hB'' hB''l (algebraMap B'' (FpnModel.B''l φ' φ'' g)) rfl x'' := by
  classical
  haveI : IsNoetherianRing (pullbackRing φ' φ'') :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.isNoetherianRing_pullbackRing_of_surjective φ' φ'' hs' hs''
  haveI : IsNoetherianRing (FpnModel.L φ' φ'' g) := FpnModel.isNoetherianRing_L φ' φ'' g hs' hs''
  have hBl : IsNilpotent (p : FpnModel.Bl φ' φ'' g) := FpnAux.nilmap (algebraMap B _) hB
  have hRa : IsNilpotent (p : Localization.Away a') := FpnAux.nilmap (algebraMap B' _) hB'
  have hRb : IsNilpotent (p : Localization.Away b'') := FpnAux.nilmap (algebraMap B'' _) hB''
  obtain ⟨ta, hta, hηa⟩ := Ha (Localization.Away a') hRa
  obtain ⟨tb, htb, hηb⟩ := Hb (Localization.Away b'') hRb

  have hua : IsUnit (algebraMap B' (FpnModel.B'l φ' φ'' g) a') := IsLocalization.Away.isUnit_of_dvd (g.1.1) hda
  have hub : IsUnit (algebraMap B'' (FpnModel.B''l φ' φ'' g) b'') := IsLocalization.Away.isUnit_of_dvd (g.1.2) hdb
  let La : Localization.Away a' →+* FpnModel.B'l φ' φ'' g := IsLocalization.Away.lift a' hua
  let Lb : Localization.Away b'' →+* FpnModel.B''l φ' φ'' g := IsLocalization.Away.lift b'' hub
  have hLa : La.comp (algebraMap B' (Localization.Away a')) = algebraMap B' (FpnModel.B'l φ' φ'' g) :=
    IsLocalization.Away.lift_comp _ hua
  have hLb : Lb.comp (algebraMap B'' (Localization.Away b'')) = algebraMap B'' (FpnModel.B''l φ' φ'' g) :=
    IsLocalization.Away.lift_comp _ hub
  have ea : La.comp ((algebraMap B' (Localization.Away a')).comp ψ') =
      (algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ' := by rw [← RingHom.comp_assoc, hLa]
  have eb : Lb.comp ((algebraMap B'' (Localization.Away b'')).comp ψ'') =
      (algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'' := by rw [← RingHom.comp_assoc, hLb]

  have adm' : (ta.map La).IsAdmissible ι ((algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ') := by
    rw [← ea]; exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ La ta hta
  have adm'' : (tb.map Lb).IsAdmissible ι ((algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'') := by
    rw [← eb]; exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ Lb tb htb
  have η' : η _ ((algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ') hB'l (ta.map La) =
      M.map hB' hB'l (algebraMap B' (FpnModel.B'l φ' φ'' g)) rfl x' := by
    rw [hηn _ _ _ _ hRa hB'l La ea ta hta, hηa]
    exact FpnAux.map_map M hB' hRa hB'l _ La _ rfl ea rfl hLa x'
  have η'' : η _ ((algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'') hB''l (tb.map Lb) =
      M.map hB'' hB''l (algebraMap B'' (FpnModel.B''l φ' φ'' g)) rfl x'' := by
    rw [hηn _ _ _ _ hRb hB''l Lb eb tb htb, hηb]
    exact FpnAux.map_map M hB'' hRb hB''l _ Lb _ rfl eb rfl hLb x''

  have eφ' : (FpnModel.φ'l φ' φ'' g).comp ((algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ') =
      (algebraMap B (FpnModel.Bl φ' φ'' g)).comp ψ := by
    rw [← RingHom.comp_assoc, FpnModel.φ'l_comp, RingHom.comp_assoc, hφ']
  have eφ'' : (FpnModel.φ''l φ' φ'' g).comp ((algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'') =
      (algebraMap B (FpnModel.Bl φ' φ'' g)).comp ψ := by
    rw [← RingHom.comp_assoc, FpnModel.φ''l_comp, RingHom.comp_assoc, hφ'']
  have admB' : ((ta.map La).map (FpnModel.φ'l φ' φ'' g)).IsAdmissible ι
      ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp ψ) := by
    rw [← eφ']; exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ _ _ adm'
  have admB'' : ((tb.map Lb).map (FpnModel.φ''l φ' φ'' g)).IsAdmissible ι
      ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp ψ) := by
    rw [← eφ'']; exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ _ _ adm''
  have ηB' : η _ ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp ψ) hBl ((ta.map La).map (FpnModel.φ'l φ' φ'' g)) =
      M.map hB hBl (algebraMap B (FpnModel.Bl φ' φ'' g)) rfl (M.map hB' hB φ' hφ' x') := by
    rw [hηn _ _ _ _ hB'l hBl _ eφ' _ adm', η',
      FpnAux.map_map M hB' hB'l hBl _ _ ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp φ') rfl eφ'
        (by rw [RingHom.comp_assoc, hφ']) (FpnModel.φ'l_comp φ' φ'' g) x',
      FpnAux.map_map M hB' hB hBl φ' _ ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp φ') hφ' rfl
        (by rw [RingHom.comp_assoc, hφ']) rfl x']
  have ηB'' : η _ ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp ψ) hBl ((tb.map Lb).map (FpnModel.φ''l φ' φ'' g)) =
      M.map hB hBl (algebraMap B (FpnModel.Bl φ' φ'' g)) rfl (M.map hB'' hB φ'' hφ'' x'') := by
    rw [hηn _ _ _ _ hB''l hBl _ eφ'' _ adm'', η'',
      FpnAux.map_map M hB'' hB''l hBl _ _ ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp φ'') rfl eφ''
        (by rw [RingHom.comp_assoc, hφ'']) (FpnModel.φ''l_comp φ' φ'' g) x'',
      FpnAux.map_map M hB'' hB hBl φ'' _ ((algebraMap B (FpnModel.Bl φ' φ'' g)).comp φ'') hφ'' rfl
        (by rw [RingHom.comp_assoc, hφ'']) rfl x'']
  have iso0 : ((ta.map La).map (FpnModel.φ'l φ' φ'' g)).IsIsomorphic ((tb.map Lb).map (FpnModel.φ''l φ' φ'' g)) :=
    (hηi _ _ hBl _ _ admB' admB'').mp (by rw [ηB', ηB'', hx])

  obtain ⟨t, ht, hiso', hiso''⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
      p ι Φ hΦ hΦ4 _ _ _ hBl hB'l hB''l (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g) eφ' eφ''
      (FpnModel.φ'l_surjective φ' φ'' g hs') (FpnModel.φ''l_surjective φ' φ'' g hs'')
      (FpnModel.φ'l_ker φ' φ'' g hn') (FpnModel.φ''l_ker φ' φ'' g hn'') hL _ ef es
      (ta.map La) (tb.map Lb) adm' adm'' iso0
  refine ⟨η _ _ hL t, ?_, ?_⟩
  · have admf : (t.map (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g))).IsAdmissible ι
        ((algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ') := by
      rw [← ef]; exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ _ _ ht
    rw [← hηn _ _ _ _ hL hB'l _ ef t ht, ← η']
    exact (hηi _ _ hB'l _ _ admf adm').mpr hiso'
  · have adms : (t.map (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g))).IsAdmissible ι
        ((algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'') := by
      rw [← es]; exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ _ _ ht
    rw [← hηn _ _ _ _ hL hB''l _ es t ht, ← η'']
    exact (hηi _ _ hB''l _ _ adms adm'').mpr hiso''

set_option maxHeartbeats 3200000 in
theorem overlap_piece
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
      (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
      η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
      ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (p : L)),
      ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
      η L ((algebraMap B L).comp ψ) hL t =
      M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (ψ'' : WittVector p k →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
    (hn' : IsNilpotent (RingHom.ker φ')) (hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : pullbackRing φ' φ''))
    (ψP : WittVector p k →+* pullbackRing φ' φ'')
    (hψP' : (pullbackFst φ' φ'').comp ψP = ψ')
    (hψP'' : (pullbackSnd φ' φ'').comp ψP = ψ'')
    (x' : M.obj B' ψ' hB') (x'' : M.obj B'' ψ'' hB'')

    (hLg : ∀ g : pullbackRing φ' φ'', IsNilpotent (p : FpnModel.L φ' φ'' g))
    (hB'lg : ∀ g : pullbackRing φ' φ'', IsNilpotent (p : FpnModel.B'l φ' φ'' g))
    (hB''lg : ∀ g : pullbackRing φ' φ'', IsNilpotent (p : FpnModel.B''l φ' φ'' g))
    (ef : ∀ g : pullbackRing φ' φ'', (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)).comp
      ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
      (algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ')
    (es : ∀ g : pullbackRing φ' φ'', (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)).comp
      ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
      (algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'')
    (g₁ g₂ : pullbackRing φ' φ'')
    (zL₁ : M.obj (FpnModel.L φ' φ'' g₁) ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g₁)).comp ψP) (hLg g₁))
    (zL₂ : M.obj (FpnModel.L φ' φ'' g₂) ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g₂)).comp ψP) (hLg g₂))
    (E1₁ : M.map (hLg g₁) (hB'lg g₁) (pullbackFst (FpnModel.φ'l φ' φ'' g₁) (FpnModel.φ''l φ' φ'' g₁)) (ef g₁) zL₁ =
        M.map hB' (hB'lg g₁) (algebraMap B' (FpnModel.B'l φ' φ'' g₁)) rfl x')
    (E2₁ : M.map (hLg g₁) (hB''lg g₁) (pullbackSnd (FpnModel.φ'l φ' φ'' g₁) (FpnModel.φ''l φ' φ'' g₁)) (es g₁) zL₁ =
        M.map hB'' (hB''lg g₁) (algebraMap B'' (FpnModel.B''l φ' φ'' g₁)) rfl x'')
    (E1₂ : M.map (hLg g₂) (hB'lg g₂) (pullbackFst (FpnModel.φ'l φ' φ'' g₂) (FpnModel.φ''l φ' φ'' g₂)) (ef g₂) zL₂ =
        M.map hB' (hB'lg g₂) (algebraMap B' (FpnModel.B'l φ' φ'' g₂)) rfl x')
    (E2₂ : M.map (hLg g₂) (hB''lg g₂) (pullbackSnd (FpnModel.φ'l φ' φ'' g₂) (FpnModel.φ''l φ' φ'' g₂)) (es g₂) zL₂ =
        M.map hB'' (hB''lg g₂) (algebraMap B'' (FpnModel.B''l φ' φ'' g₂)) rfl x'')
    (hl : (IsLocalization.Away.awayToAwayRight (S := FpnModel.L φ' φ'' g₁) (P := FpnModel.L φ' φ'' (g₁ * g₂)) g₁ g₂).comp
        ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g₁)).comp ψP) =
      (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂))).comp ψP)
    (hr : (IsLocalization.Away.awayToAwayLeft (S := FpnModel.L φ' φ'' g₂) (P := FpnModel.L φ' φ'' (g₁ * g₂)) g₂ g₁).comp
        ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g₂)).comp ψP) =
      (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂))).comp ψP) :
    M.map (hLg g₁) (hLg (g₁ * g₂))
        (IsLocalization.Away.awayToAwayRight (S := FpnModel.L φ' φ'' g₁) (P := FpnModel.L φ' φ'' (g₁ * g₂)) g₁ g₂) hl zL₁ =
      M.map (hLg g₂) (hLg (g₁ * g₂))
        (IsLocalization.Away.awayToAwayLeft (S := FpnModel.L φ' φ'' g₂) (P := FpnModel.L φ' φ'' (g₁ * g₂)) g₂ g₁) hr zL₂ := by
  classical
  haveI : IsNoetherianRing (pullbackRing φ' φ'') :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.isNoetherianRing_pullbackRing_of_surjective φ' φ'' hs' hs''

  have hG := hLg (g₁ * g₂)
  have hBlG : IsNilpotent (p : FpnModel.Bl φ' φ'' (g₁ * g₂)) := FpnAux.nilmap (algebraMap B _) hB
  have eφ' : (FpnModel.φ'l φ' φ'' (g₁ * g₂)).comp ((algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))).comp ψ') =
      (algebraMap B (FpnModel.Bl φ' φ'' (g₁ * g₂))).comp ψ := by
    rw [← RingHom.comp_assoc, FpnModel.φ'l_comp, RingHom.comp_assoc, hφ']
  have eφ'' : (FpnModel.φ''l φ' φ'' (g₁ * g₂)).comp ((algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))).comp ψ'') =
      (algebraMap B (FpnModel.Bl φ' φ'' (g₁ * g₂))).comp ψ := by
    rw [← RingHom.comp_assoc, FpnModel.φ''l_comp, RingHom.comp_assoc, hφ'']

  have key' : ∀ (g : pullbackRing φ' φ'') (hdvd : g.1.1 ∣ (g₁ * g₂).1.1)
      (zL : M.obj (FpnModel.L φ' φ'' g) ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) (hLg g))
      (E1 : M.map (hLg g) (hB'lg g) (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)) (ef g) zL =
        M.map hB' (hB'lg g) (algebraMap B' (FpnModel.B'l φ' φ'' g)) rfl x')
      (lam : FpnModel.L φ' φ'' g →+* FpnModel.L φ' φ'' (g₁ * g₂))
      (hlam : lam.comp (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)) =
        algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂)))
      (hlamψ : lam.comp ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
        (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂))).comp ψP),
      M.map (hLg (g₁ * g₂)) (hB'lg (g₁ * g₂))
          (pullbackFst (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))) (ef (g₁ * g₂))
          (M.map (hLg g) (hLg (g₁ * g₂)) lam hlamψ zL) =
        M.map hB' (hB'lg (g₁ * g₂)) (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))) rfl x' := by
    intro g hdvd zL E1 lam hlam hlamψ
    have hu : IsUnit (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂)) g.1.1) :=
      IsLocalization.Away.isUnit_of_dvd ((g₁ * g₂).1.1) hdvd
    let μ : FpnModel.B'l φ' φ'' g →+* FpnModel.B'l φ' φ'' (g₁ * g₂) := IsLocalization.Away.lift g.1.1 hu
    have hμ : μ.comp (algebraMap B' (FpnModel.B'l φ' φ'' g)) = algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂)) :=
      IsLocalization.Away.lift_comp _ hu
    have heq : (pullbackFst (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))).comp lam =
        μ.comp (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      have l1 : ((pullbackFst (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))).comp lam).comp
          (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)) =
          (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))).comp (pullbackFst φ' φ'') := by
        rw [RingHom.comp_assoc, hlam, FpnModel.algebraMap_eq, FpnModel.δ_fst]
      have l2 : (μ.comp (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g))).comp
          (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)) =
          (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))).comp (pullbackFst φ' φ'') := by
        rw [RingHom.comp_assoc, FpnModel.algebraMap_eq, FpnModel.δ_fst, ← RingHom.comp_assoc, hμ]
      exact l1.trans l2.symm
    have p1 : ((pullbackFst (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))).comp lam).comp
        ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
        (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))).comp ψ' := by
      rw [RingHom.comp_assoc, hlamψ, ef]
    have p2 : (μ.comp (pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g))).comp
        ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
        (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))).comp ψ' := by
      rw [RingHom.comp_assoc, ef, ← RingHom.comp_assoc, hμ]
    have p3 : μ.comp ((algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ') =
        (algebraMap B' (FpnModel.B'l φ' φ'' (g₁ * g₂))).comp ψ' := by
      rw [← RingHom.comp_assoc, hμ]
    rw [FpnAux.map_map M (hLg g) (hLg (g₁ * g₂)) (hB'lg (g₁ * g₂)) lam _ _ hlamψ (ef (g₁ * g₂)) p1 rfl zL,
      FpnAux.map_congr M (hLg g) (hB'lg (g₁ * g₂)) _ _ p1 p2 heq zL,
      ← FpnAux.map_map M (hLg g) (hB'lg g) (hB'lg (g₁ * g₂)) _ μ _ (ef g) p3 p2 rfl zL, E1,
      FpnAux.map_map M hB' (hB'lg g) (hB'lg (g₁ * g₂)) _ μ _ rfl p3 rfl hμ x']
  have key'' : ∀ (g : pullbackRing φ' φ'') (hdvd : g.1.2 ∣ (g₁ * g₂).1.2)
      (zL : M.obj (FpnModel.L φ' φ'' g) ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) (hLg g))
      (E2 : M.map (hLg g) (hB''lg g) (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)) (es g) zL =
        M.map hB'' (hB''lg g) (algebraMap B'' (FpnModel.B''l φ' φ'' g)) rfl x'')
      (lam : FpnModel.L φ' φ'' g →+* FpnModel.L φ' φ'' (g₁ * g₂))
      (hlam : lam.comp (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)) =
        algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂)))
      (hlamψ : lam.comp ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
        (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂))).comp ψP),
      M.map (hLg (g₁ * g₂)) (hB''lg (g₁ * g₂))
          (pullbackSnd (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))) (es (g₁ * g₂))
          (M.map (hLg g) (hLg (g₁ * g₂)) lam hlamψ zL) =
        M.map hB'' (hB''lg (g₁ * g₂)) (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))) rfl x'' := by
    intro g hdvd zL E2 lam hlam hlamψ
    have hu : IsUnit (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂)) g.1.2) :=
      IsLocalization.Away.isUnit_of_dvd ((g₁ * g₂).1.2) hdvd
    let μ : FpnModel.B''l φ' φ'' g →+* FpnModel.B''l φ' φ'' (g₁ * g₂) := IsLocalization.Away.lift g.1.2 hu
    have hμ : μ.comp (algebraMap B'' (FpnModel.B''l φ' φ'' g)) = algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂)) :=
      IsLocalization.Away.lift_comp _ hu
    have heq : (pullbackSnd (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))).comp lam =
        μ.comp (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      have l1 : ((pullbackSnd (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))).comp lam).comp
          (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)) =
          (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))).comp (pullbackSnd φ' φ'') := by
        rw [RingHom.comp_assoc, hlam, FpnModel.algebraMap_eq, FpnModel.δ_snd]
      have l2 : (μ.comp (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g))).comp
          (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)) =
          (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))).comp (pullbackSnd φ' φ'') := by
        rw [RingHom.comp_assoc, FpnModel.algebraMap_eq, FpnModel.δ_snd, ← RingHom.comp_assoc, hμ]
      exact l1.trans l2.symm
    have p1 : ((pullbackSnd (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂))).comp lam).comp
        ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
        (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))).comp ψ'' := by
      rw [RingHom.comp_assoc, hlamψ, es]
    have p2 : (μ.comp (pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g))).comp
        ((algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
        (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))).comp ψ'' := by
      rw [RingHom.comp_assoc, es, ← RingHom.comp_assoc, hμ]
    have p3 : μ.comp ((algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'') =
        (algebraMap B'' (FpnModel.B''l φ' φ'' (g₁ * g₂))).comp ψ'' := by
      rw [← RingHom.comp_assoc, hμ]
    rw [FpnAux.map_map M (hLg g) (hLg (g₁ * g₂)) (hB''lg (g₁ * g₂)) lam _ _ hlamψ (es (g₁ * g₂)) p1 rfl zL,
      FpnAux.map_congr M (hLg g) (hB''lg (g₁ * g₂)) _ _ p1 p2 heq zL,
      ← FpnAux.map_map M (hLg g) (hB''lg g) (hB''lg (g₁ * g₂)) _ μ _ (es g) p3 p2 rfl zL, E2,
      FpnAux.map_map M hB'' (hB''lg g) (hB''lg (g₁ * g₂)) _ μ _ rfl p3 rfl hμ x'']
  have hl0 : (IsLocalization.Away.awayToAwayRight (S := FpnModel.L φ' φ'' g₁) (P := FpnModel.L φ' φ'' (g₁ * g₂)) g₁ g₂).comp
      (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g₁)) = algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂)) :=
    RingHom.ext fun z => IsLocalization.Away.awayToAwayRight_eq (S := FpnModel.L φ' φ'' g₁) g₁ g₂ z
  have hr0 : (IsLocalization.Away.awayToAwayLeft (S := FpnModel.L φ' φ'' g₂) (P := FpnModel.L φ' φ'' (g₁ * g₂)) g₂ g₁).comp
      (algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' g₂)) = algebraMap (pullbackRing φ' φ'') (FpnModel.L φ' φ'' (g₁ * g₂)) :=
    RingHom.ext fun z => IsLocalization.Away.awayToAwayLeft_eq (S := FpnModel.L φ' φ'' g₂) g₂ g₁ z
  exact CerednikDrinfeld.SpecialFormal.ModuliPackage.eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
    p k ι Φ hΦ hΦ4 M hM η hη _ _ _ hBlG (hB'lg (g₁ * g₂)) (hB''lg (g₁ * g₂))
    (FpnModel.φ'l φ' φ'' (g₁ * g₂)) (FpnModel.φ''l φ' φ'' (g₁ * g₂)) eφ' eφ''
    (FpnModel.φ'l_surjective φ' φ'' _ hs') (FpnModel.φ''l_surjective φ' φ'' _ hs'')
    (FpnModel.φ'l_ker φ' φ'' _ hn') (FpnModel.φ''l_ker φ' φ'' _ hn'') (hLg (g₁ * g₂)) _ (ef (g₁ * g₂)) (es (g₁ * g₂)) _ _
    ((key' g₁ (Dvd.intro _ rfl) zL₁ E1₁ _ hl0 hl).trans (key' g₂ (dvd_mul_left _ _) zL₂ E1₂ _ hr0 hr).symm)
    ((key'' g₁ (Dvd.intro _ rfl) zL₁ E2₁ _ hl0 hl).trans (key'' g₂ (dvd_mul_left _ _) zL₂ E2₂ _ hr0 hr).symm)

set_option maxHeartbeats 3200000 in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (ψ'' : WittVector p k →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
    (hn' : IsNilpotent (RingHom.ker φ')) (hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))

    (ψP : WittVector p k →+* ModuliPackage.pullbackRing φ' φ'')
    (hψP' : (ModuliPackage.pullbackFst φ' φ'').comp ψP = ψ')
    (hψP'' : (ModuliPackage.pullbackSnd φ' φ'').comp ψP = ψ'')
    (x' : M.obj B' ψ' hB') (x'' : M.obj B'' ψ'' hB'')
    (hx : M.map hB' hB φ' hφ' x' = M.map hB'' hB φ'' hφ'' x'') :
    ∃ z : M.obj (ModuliPackage.pullbackRing φ' φ'') ψP hP,
      M.map hP hB' (ModuliPackage.pullbackFst φ' φ'') hψP' z = x' ∧
      M.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'') hψP'' z = x'' := by
  classical
  haveI : IsNoetherianRing (ModuliPackage.pullbackRing φ' φ'') :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.isNoetherianRing_pullbackRing_of_surjective φ' φ'' hs' hs''
  have hfstS := FpnAux2.pullbackFst_surjective φ' φ'' hs''
  have hsndS := FpnAux2.pullbackSnd_surjective φ' φ'' hs'
  have hfstN := FpnAux2.isNilpotent_ker_pullbackFst φ' φ'' hn''
  have hsndN := FpnAux2.isNilpotent_ker_pullbackSnd φ' φ'' hn'

  have hLg : ∀ g : ModuliPackage.pullbackRing φ' φ'', IsNilpotent (p : FpnModel.L φ' φ'' g) :=
    fun g => FpnAux.nilmap (algebraMap (ModuliPackage.pullbackRing φ' φ'') _) hP
  have hB'lg : ∀ g : ModuliPackage.pullbackRing φ' φ'', IsNilpotent (p : FpnModel.B'l φ' φ'' g) :=
    fun g => FpnAux.nilmap (algebraMap B' _) hB'
  have hB''lg : ∀ g : ModuliPackage.pullbackRing φ' φ'', IsNilpotent (p : FpnModel.B''l φ' φ'' g) :=
    fun g => FpnAux.nilmap (algebraMap B'' _) hB''
  have ef : ∀ g : ModuliPackage.pullbackRing φ' φ'',
      (ModuliPackage.pullbackFst (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)).comp
        ((algebraMap (ModuliPackage.pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
      (algebraMap B' (FpnModel.B'l φ' φ'' g)).comp ψ' := fun g => by
    rw [← RingHom.comp_assoc, FpnModel.algebraMap_eq, FpnModel.δ_fst, RingHom.comp_assoc, hψP']
  have es : ∀ g : ModuliPackage.pullbackRing φ' φ'',
      (ModuliPackage.pullbackSnd (FpnModel.φ'l φ' φ'' g) (FpnModel.φ''l φ' φ'' g)).comp
        ((algebraMap (ModuliPackage.pullbackRing φ' φ'') (FpnModel.L φ' φ'' g)).comp ψP) =
      (algebraMap B'' (FpnModel.B''l φ' φ'' g)).comp ψ'' := fun g => by
    rw [← RingHom.comp_assoc, FpnModel.algebraMap_eq, FpnModel.δ_snd, RingHom.comp_assoc, hψP'']

  obtain ⟨n₁, f₁, hf₁, H₁⟩ := hη.2.2 B' ψ' hB' x'
  obtain ⟨n₂, f₂, hf₂, H₂⟩ := hη.2.2 B'' ψ'' hB'' x''

  obtain ⟨N, G, hGa, hGb, hG⟩ : ∃ (N : ℕ) (G : Fin N → ModuliPackage.pullbackRing φ' φ''),
      (∀ j, ∃ i, f₁ i ∣ (G j).1.1) ∧ (∀ j, ∃ i, f₂ i ∣ (G j).1.2) ∧ Ideal.span (Set.range G) = ⊤ := by
    choose ca hca using fun i => hs'' (φ' (f₁ i))
    choose cb hcb using fun j => hs' (φ'' (f₂ j))
    let a : Fin n₁ → ModuliPackage.pullbackRing φ' φ'' := fun i => ⟨(f₁ i, ca i), (hca i).symm⟩
    let b : Fin n₂ → ModuliPackage.pullbackRing φ' φ'' := fun j => ⟨(cb j, f₂ j), hcb j⟩
    have hA : Ideal.span (Set.range a) = ⊤ := by
      apply FpnAux2.span_eq_top_of_surjective_of_isNilpotent_ker _ hfstS hfstN
      rw [← Set.range_comp]
      exact hf₁
    have hB : Ideal.span (Set.range b) = ⊤ := by
      apply FpnAux2.span_eq_top_of_surjective_of_isNilpotent_ker _ hsndS hsndN
      rw [← Set.range_comp]
      exact hf₂
    exact ⟨n₁ * n₂, fun j => a (finProdFinEquiv.symm j).1 * b (finProdFinEquiv.symm j).2,
      fun j => ⟨(finProdFinEquiv.symm j).1, Dvd.intro _ rfl⟩,
      fun j => ⟨(finProdFinEquiv.symm j).2, dvd_mul_left _ _⟩,
      FpnAux.span_prod_eq_top a b hA hB⟩

  have hex : ∀ j, ∃ zL : M.obj (FpnModel.L φ' φ'' (G j))
      ((algebraMap (ModuliPackage.pullbackRing φ' φ'') (FpnModel.L φ' φ'' (G j))).comp ψP) (hLg (G j)),
      M.map (hLg (G j)) (hB'lg (G j)) (ModuliPackage.pullbackFst (FpnModel.φ'l φ' φ'' (G j)) (FpnModel.φ''l φ' φ'' (G j)))
        (ef (G j)) zL = M.map hB' (hB'lg (G j)) (algebraMap B' (FpnModel.B'l φ' φ'' (G j))) rfl x' ∧
      M.map (hLg (G j)) (hB''lg (G j)) (ModuliPackage.pullbackSnd (FpnModel.φ'l φ' φ'' (G j)) (FpnModel.φ''l φ' φ'' (G j)))
        (es (G j)) zL = M.map hB'' (hB''lg (G j)) (algebraMap B'' (FpnModel.B''l φ' φ'' (G j))) rfl x'' := by
    intro j
    obtain ⟨i₁, hi₁⟩ := hGa j
    obtain ⟨i₂, hi₂⟩ := hGb j
    exact ex_piece p k ι Φ hΦ hΦ4 M η hη.1 hη.2.1 ψ ψ' ψ'' hB hB' hB'' φ' φ'' hφ' hφ'' hs' hs'' hn' hn'' hP ψP hψP' hψP''
      x' x'' hx (G j) (f₁ i₁) (f₂ i₂) hi₁ hi₂ (H₁ i₁) (H₂ i₂) (hLg (G j)) (hB'lg (G j)) (hB''lg (G j)) (ef (G j)) (es (G j))
  choose x hx using hex

  obtain ⟨z, hz⟩ := (hM (ModuliPackage.pullbackRing φ' φ'') ψP hP N G hG
    (fun j => FpnModel.L φ' φ'' (G j)) (fun j => hLg (G j))
    (fun j j' => FpnModel.L φ' φ'' (G j * G j')) (fun j j' => hLg (G j * G j'))
    (fun j j' => IsLocalization.Away.awayToAwayRight (G j) (G j'))
    (fun j j' => IsLocalization.Away.awayToAwayLeft (G j') (G j))
    (fun j j' w => IsLocalization.Away.awayToAwayRight_eq _ _ w)
    (fun j j' w => IsLocalization.Away.awayToAwayLeft_eq _ _ w)).2 x (fun j j' =>
      overlap_piece p k ι Φ hΦ hΦ4 M hM η hη ψ ψ' ψ'' hB hB' hB'' φ' φ'' hφ' hφ'' hs' hs'' hn' hn'' hP ψP hψP' hψP''
        x' x'' hLg hB'lg hB''lg ef es (G j) (G j') (x j) (x j') (hx j).1 (hx j).2 (hx j').1 (hx j').2 _ _)
  refine ⟨z, ?_, ?_⟩
  ·
    have hG' : Ideal.span (Set.range (fun j => (G j).1.1)) = ⊤ := by
      rw [show (fun j => (G j).1.1) = (ModuliPackage.pullbackFst φ' φ'') ∘ G from rfl, Set.range_comp,
        ← Ideal.map_span, hG, Ideal.map_top]
    refine (hM B' ψ' hB' N (fun j => (G j).1.1) hG'
      (fun j => FpnModel.B'l φ' φ'' (G j)) (fun j => hB'lg (G j))
      (fun j j' => Localization.Away ((G j).1.1 * (G j').1.1)) (fun j j' => FpnAux.nilmap (algebraMap B' _) hB')
      (fun j j' => IsLocalization.Away.awayToAwayRight (G j).1.1 (G j').1.1)
      (fun j j' => IsLocalization.Away.awayToAwayLeft (G j').1.1 (G j).1.1)
      (fun j j' w => IsLocalization.Away.awayToAwayRight_eq _ _ w)
      (fun j j' w => IsLocalization.Away.awayToAwayLeft_eq _ _ w)).1 _ _ (fun j => ?_)
    rw [FpnAux.map_map M hP hB' (hB'lg (G j)) (ModuliPackage.pullbackFst φ' φ'') (algebraMap B' _)
        ((algebraMap B' (FpnModel.B'l φ' φ'' (G j))).comp (ModuliPackage.pullbackFst φ' φ'')) hψP' rfl
        (by rw [RingHom.comp_assoc, hψP']) rfl z,
      ← FpnAux.map_map M hP (hLg (G j)) (hB'lg (G j)) (algebraMap _ (FpnModel.L φ' φ'' (G j)))
        (ModuliPackage.pullbackFst (FpnModel.φ'l φ' φ'' (G j)) (FpnModel.φ''l φ' φ'' (G j)))
        ((algebraMap B' (FpnModel.B'l φ' φ'' (G j))).comp (ModuliPackage.pullbackFst φ' φ'')) rfl (ef (G j))
        (by rw [RingHom.comp_assoc, hψP']) (by rw [FpnModel.algebraMap_eq, FpnModel.δ_fst]) z,
      hz j, (hx j).1]
  ·
    have hG'' : Ideal.span (Set.range (fun j => (G j).1.2)) = ⊤ := by
      rw [show (fun j => (G j).1.2) = (ModuliPackage.pullbackSnd φ' φ'') ∘ G from rfl, Set.range_comp,
        ← Ideal.map_span, hG, Ideal.map_top]
    refine (hM B'' ψ'' hB'' N (fun j => (G j).1.2) hG''
      (fun j => FpnModel.B''l φ' φ'' (G j)) (fun j => hB''lg (G j))
      (fun j j' => Localization.Away ((G j).1.2 * (G j').1.2)) (fun j j' => FpnAux.nilmap (algebraMap B'' _) hB'')
      (fun j j' => IsLocalization.Away.awayToAwayRight (G j).1.2 (G j').1.2)
      (fun j j' => IsLocalization.Away.awayToAwayLeft (G j').1.2 (G j).1.2)
      (fun j j' w => IsLocalization.Away.awayToAwayRight_eq _ _ w)
      (fun j j' w => IsLocalization.Away.awayToAwayLeft_eq _ _ w)).1 _ _ (fun j => ?_)
    rw [FpnAux.map_map M hP hB'' (hB''lg (G j)) (ModuliPackage.pullbackSnd φ' φ'') (algebraMap B'' _)
        ((algebraMap B'' (FpnModel.B''l φ' φ'' (G j))).comp (ModuliPackage.pullbackSnd φ' φ'')) hψP'' rfl
        (by rw [RingHom.comp_assoc, hψP'']) rfl z,
      ← FpnAux.map_map M hP (hLg (G j)) (hB''lg (G j)) (algebraMap _ (FpnModel.L φ' φ'' (G j)))
        (ModuliPackage.pullbackSnd (FpnModel.φ'l φ' φ'' (G j)) (FpnModel.φ''l φ' φ'' (G j)))
        ((algebraMap B'' (FpnModel.B''l φ' φ'' (G j))).comp (ModuliPackage.pullbackSnd φ' φ'')) rfl (es (G j))
        (by rw [RingHom.comp_assoc, hψP'']) (by rw [FpnModel.algebraMap_eq, FpnModel.δ_snd]) z,
      hz j, (hx j).2]

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf (solution)
