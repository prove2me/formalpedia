-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSpecial_of_forall_isSpecial_map_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/62f15526-9b7a-5adf-bdc4-20b34082734f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_forall_isSpecial_map_away

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace LocalAux

theorem idem_eq_one_of_forall_away {B : Type} [CommRing B] {e : B} {n : ℕ} (g : Fin n → B)
    (hg : Ideal.span (Set.range g) = ⊤)
    (h : ∀ i : Fin n, algebraMap B (Localization.Away (g i)) e = 1) : e = 1 := by
  classical

  have hk : ∀ i : Fin n, ∃ k : ℕ, g i ^ k * (1 - e) = 0 := by
    intro i
    have := h i
    rw [← (algebraMap B (Localization.Away (g i))).map_one,
      IsLocalization.eq_iff_exists (Submonoid.powers (g i))] at this
    obtain ⟨⟨c, ⟨k, rfl⟩⟩, hc⟩ := this
    refine ⟨k, ?_⟩
    have : g i ^ k * e = g i ^ k * 1 := hc
    rw [mul_sub, this, sub_self]
  choose k hk using hk

  have hspan : Ideal.span (Set.range fun i => g i ^ k i) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top (Set.range g) hg (Finset.univ.sup k), Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hle : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    show g i ^ (Finset.univ.sup k) ∈ Ideal.span (Set.range fun i => g i ^ k i)
    rw [hd, pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have h1 : (1 : B) - e ∈ (⊤ : Ideal B) := Submodule.mem_top
  have hann : ∀ x ∈ Ideal.span (Set.range fun i => g i ^ k i), x * (1 - e) = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact hk i
    · exact zero_mul _
    · intro a b _ _ ha hb; rw [add_mul, ha, hb, add_zero]
    · intro r a _ ha; rw [smul_eq_mul, mul_assoc, ha, mul_zero]
  have := hann 1 (by rw [hspan]; exact Submodule.mem_top)
  rw [one_mul, sub_eq_zero] at this
  exact this.symm

end LocalAux

theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B)) (j : Zp2 p →+* B)
    (Y : FormalODModule p B) {n : ℕ} (g : Fin n → B) (hg : Ideal.span (Set.range g) = ⊤)
    (h : ∀ i : Fin n, (Y.map (algebraMap B (Localization.Away (g i)))).IsSpecial
      ((algebraMap B (Localization.Away (g i))).comp j)) :
    Y.IsSpecial j := by
  obtain ⟨e, he, hspec⟩ := CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff p hB j Y
  have h1 : ∀ i : Fin n, algebraMap B (Localization.Away (g i)) e = 1 := fun i => (hspec _ _).mp (h i)
  have he1 : e = 1 := LocalAux.idem_eq_one_of_forall_away g hg h1
  have := (hspec B (RingHom.id B)).mpr (by rw [he1, map_one])
  rwa [FormalODModule.map_id, RingHom.id_comp] at this

end S_CerednikDrinfeld_FormalODModule_isSpecial_of_forall_isSpecial_map_away
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_forall_isSpecial_map_away (solution)
