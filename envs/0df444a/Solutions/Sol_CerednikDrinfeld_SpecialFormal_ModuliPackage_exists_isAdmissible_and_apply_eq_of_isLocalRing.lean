-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_and_apply_eq_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/94113d5b-dab3-517b-9f3b-a120c4ef3cd5

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_and_apply_eq_of_isLocalRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{0, 0} p O)
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB)

    (hη₃ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)

    (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) :
    ∃ t : Rigidified p Φ B, t.IsAdmissible ι ψ ∧ η B ψ hB t = m := by
  classical
  obtain ⟨n, f, hspan, hloc⟩ := hη₃ B ψ hB m
  have hunit : ∃ i, IsUnit (f i) := by
    by_contra h
    push_neg at h
    have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal B := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (h i)
    rw [hspan, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top hle
  obtain ⟨i, hi⟩ := hunit
  haveI : IsLocalization.Away (f i) B := IsLocalization.away_of_isUnit_of_bijective (S := B) hi Function.bijective_id
  obtain ⟨t, hta, hteq⟩ := hloc i B hB
  exact ⟨t, hta, hteq.trans (M.map_id hB m)⟩

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_and_apply_eq_of_isLocalRing
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_and_apply_eq_of_isLocalRing (solution)
