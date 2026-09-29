-- Prove2me | solution 1 for CerednikDrinfeld.exists_torsionFree_surjective_comp_eq_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9953ee7a-299b-5004-9a7a-d1881a0677ac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit

set_option autoImplicit false

theorem solution
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B]
    (q : S →+* B) (hq : Function.Surjective q) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (S' : Type) (_ : CommRing S') (ι : S →+* S') (q' : S' →+* B),
      (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q' ∧ q'.comp ι = q ∧
      ∀ s : S', IsUnit (q' s) → IsUnit s := by
  classical
  let M : Submonoid S := (IsUnit.submonoid B).comap q
  have hM : ∀ m : M, IsUnit (q (m : S)) := fun m => m.2
  let L : Type := Localization M
  let q' : L →+* B := IsLocalization.lift (M := M) (S := L) hM
  refine ⟨L, inferInstance, algebraMap S L, q', ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    dsimp only at *
    have h1 : (p : L) * IsLocalization.mk' L s m = IsLocalization.mk' L ((p : S) * s) m := by
      rw [IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one (x := (p : S) * s),
        map_mul, map_natCast, mul_assoc]
    rw [h1, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨c, hc⟩ := hx
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨c, hS _ ?_⟩
    rw [← hc]; ring
  ·
    intro b
    obtain ⟨s, rfl⟩ := hq b
    exact ⟨algebraMap S L s, IsLocalization.lift_eq hM s⟩
  ·
    exact RingHom.ext fun s => IsLocalization.lift_eq hM s
  ·
    intro x hx
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    dsimp only at *
    have hspec : q s = q (m : S) * q' (IsLocalization.mk' L s m) :=
      (IsLocalization.lift_mk'_spec (M := M) (S := L) hM s _ m).mp rfl
    have hs : IsUnit (q s) := by rw [hspec]; exact (hM m).mul hx
    have hsM : s ∈ M := hs
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine (IsLocalization.map_units L (⟨s, hsM⟩ : M)).mul ?_
    refine IsUnit.of_mul_eq_one (algebraMap S L (m : S)) ?_
    rw [IsLocalization.mk'_spec, map_one]

end S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit (solution)
