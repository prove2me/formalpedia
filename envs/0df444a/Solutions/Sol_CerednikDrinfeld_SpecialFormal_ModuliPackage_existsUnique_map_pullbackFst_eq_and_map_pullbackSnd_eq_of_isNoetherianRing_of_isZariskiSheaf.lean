-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a6e2fd8d-0f8d-56f9-9716-772546e53aa2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

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
    :
    (∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (ψ'' : WittVector p k →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : M.obj B' ψ' hB') (x'' : M.obj B'' ψ'' hB''),
      M.map hB' hB φ' hφ' x' = M.map hB'' hB φ'' hφ'' x'' →
      ∃! z : M.obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        M.map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        M.map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'') := by
  intro B B' B'' _ _ _ _ _ _ ψ ψ' ψ'' hB hB' hB'' φ' φ'' hφ' hφ'' hs' hs'' hn' hn'' hP x' x'' hx
  have hψP' := ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)
  have hψP'' := ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)
  obtain ⟨z, hz', hz''⟩ := CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf p k ι Φ hΦ hΦ4 M hM η hη ψ ψ' ψ'' hB hB' hB'' φ' φ'' hφ' hφ'' hs' hs'' hn' hn'' hP
    (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hψP' hψP'' x' x'' hx
  refine ⟨z, ⟨hz', hz''⟩, ?_⟩
  rintro z₂ ⟨hz₂', hz₂''⟩
  exact (CerednikDrinfeld.SpecialFormal.ModuliPackage.eq_of_map_pullbackFst_eq_of_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf p k ι Φ hΦ hΦ4 M hM η hη ψ ψ' ψ'' hB hB' hB'' φ' φ'' hφ' hφ'' hs' hs'' hn' hn'' hP
    (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hψP' hψP'' z₂ z
    (hz₂'.trans hz'.symm) (hz₂''.trans hz''.symm))

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing_of_isZariskiSheaf (solution)
