-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.index_KK_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:44.884152+00:00
-- url     : https://prove2.me/submissions/fe2a83c1-733a-4c1b-aa9a-52d2fa3d2095

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_neg_one_ne_one_int
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_units_int
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_five_mod_four
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_neg_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_closure_units
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_sq_mem_KK
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_JJ_mem_KK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Subgroup
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
private lemma chi4_unitsMap_neg_one_eq_neg_one {N : ℕ} (h : 4 ∣ N) :
    ZMod.χ₄.toUnitHom (ZMod.unitsMap h (-1 : (ZMod N)ˣ)) = -1 := by
  rw [unitsMap_neg_one]
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  first | rfl | decide | simp | (simp; decide)
private lemma chi8_unitsMap_neg_one_eq_one {N : ℕ} (h : 8 ∣ N) :
    ZMod.χ₈.toUnitHom (ZMod.unitsMap h (-1 : (ZMod N)ˣ)) = 1 := by
  rw [unitsMap_neg_one]
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  first | rfl | decide | simp | (simp; decide)
private lemma chi8_unitsMap_u5_eq_neg_one (k : ℕ) (h : 8 ∣ 2 ^ (k + 3)) :
    ZMod.χ₈.toUnitHom (ZMod.unitsMap h (u5 (k + 3))) = -1 := by
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  have h5 : ((ZMod.unitsMap h (u5 (k + 3)) : (ZMod 8)ˣ) : ZMod 8) = 5 := by
    first
      | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)
      | (simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)
      | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h]; rfl)
  rw [h5]
  first | rfl | decide
end ModelEmbedding
open ModelEmbedding
end Formalism.TwoAdicCyclotomicDecomposition
end

set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (k : ℕ) : (KK (k + 3)).index ≤ 8 := by
  have h4 : 4 ∣ 2 ^ (k + 3) := ⟨2 ^ (k + 1), by ring⟩
  have h8 : 8 ∣ 2 ^ (k + 3) := ⟨2 ^ k, by ring⟩
  obtain ⟨c4, hc4a, hc4b⟩ : ∃ c : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ, c (-1) = -1 ∧ c (u5 (k + 3)) = 1 :=
    ⟨ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap h4), chi4_unitsMap_neg_one_eq_neg_one h4, by
      rw [MonoidHom.comp_apply, unitsMap_five_mod_four, map_one]⟩
  obtain ⟨c8, hc8a, hc8b⟩ : ∃ c : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ, c (-1) = 1 ∧ c (u5 (k + 3)) = -1 :=
    ⟨ZMod.χ₈.toUnitHom.comp (ZMod.unitsMap h8), chi8_unitsMap_neg_one_eq_one h8, chi8_unitsMap_u5_eq_neg_one k h8⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : GalL (k + 3) →* ℤˣ × ℤˣ × ℤˣ,
      ∀ g : GalL (k + 3), φ g = (c4 g.1 * g.2.1, c8 g.1, g.2.1 * g.2.2) :=
    ⟨MonoidHom.mk' (fun g => (c4 g.1 * g.2.1, c8 g.1, g.2.1 * g.2.2)) (by
      intro a b
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show c4 (a.1 * b.1) * (a.2.1 * b.2.1) = (c4 a.1 * a.2.1) * (c4 b.1 * b.2.1)
        rw [map_mul, mul_mul_mul_comm]
      · show c8 (a.1 * b.1) = c8 a.1 * c8 b.1
        rw [map_mul]
      · show (a.2.1 * b.2.1) * (a.2.2 * b.2.2) = (a.2.1 * a.2.2) * (b.2.1 * b.2.2)
        rw [mul_mul_mul_comm]), fun g => rfl⟩
  have hker : φ.ker ≤ KK (k + 3) := by
    rintro ⟨u, e1, e2⟩ hg
    rw [MonoidHom.mem_ker, hφ] at hg
    simp only [Prod.mk_eq_one] at hg
    obtain ⟨hg1, hg2, hg3⟩ := hg
    have hu : u ∈ Subgroup.closure {(-1 : (ZMod (2 ^ (k + 3)))ˣ), u5 (k + 3)} := by
      have hc : Subgroup.closure {(-1 : (ZMod (2 ^ (k + 3)))ˣ), u5 (k + 3)} = ⊤ :=
        closure_units (k + 1)
      rw [hc]; exact Subgroup.mem_top u
    obtain ⟨m, n, rfl⟩ := Subgroup.mem_closure_pair.1 hu
    rw [map_mul, map_zpow, map_zpow, hc8a, hc8b, one_zpow, one_mul] at hg2
    rw [map_mul, map_zpow, map_zpow, hc4a, hc4b, one_zpow, mul_one] at hg1
    rcases Int.even_or_odd n with hn | hn
    swap
    · exfalso; rw [hn.neg_one_zpow] at hg2; exact neg_one_ne_one_int hg2
    obtain ⟨r, rfl⟩ := hn
    have hsq : ∀ s : ℤ, (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s) * u5 (k + 3) ^ (r + r),
        (1 : ℤˣ), (1 : ℤˣ)) : GalL (k + 3)) ∈ KK (k + 3) := by
      intro s
      have key : (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s) * u5 (k + 3) ^ (r + r),
          (1 : ℤˣ), (1 : ℤˣ)) : GalL (k + 3)) = ((-1) ^ s * u5 (k + 3) ^ r, 1, 1) ^ 2 := by
        rw [sq, zpow_add, zpow_add]
        simp only [Prod.mk_mul_mk, mul_one]
        rw [mul_mul_mul_comm]
      rw [key]; exact sq_mem_KK _
    rcases Int.even_or_odd m with hm | hm
    · rw [hm.neg_one_zpow, one_mul] at hg1
      subst hg1
      rw [one_mul] at hg3
      subst hg3
      obtain ⟨s, rfl⟩ := hm
      exact hsq s
    · rw [hm.neg_one_zpow, neg_one_mul, neg_eq_iff_eq_neg] at hg1
      subst hg1
      rw [neg_one_mul, neg_eq_iff_eq_neg] at hg3
      subst hg3
      obtain ⟨s, rfl⟩ := hm
      have key2 : (((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (2 * s + 1) * u5 (k + 3) ^ (r + r),
          (-1 : ℤˣ), (-1 : ℤˣ)) : GalL (k + 3)) =
          JJ (k + 3) * ((-1) ^ (s + s) * u5 (k + 3) ^ (r + r), 1, 1) := by
        rw [JJ]
        simp only [Prod.mk_mul_mk, mul_one]
        rw [two_mul, zpow_add_one, mul_comm ((-1 : (ZMod (2 ^ (k + 3)))ˣ) ^ (s + s)) (-1), mul_assoc]
      rw [key2]
      exact (KK (k + 3)).mul_mem (JJ_mem_KK _) (hsq s)
  have hφle : φ.ker.index ≤ 8 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (ℤˣ × ℤˣ × ℤˣ) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 8 := by rw [Nat.card_prod, Nat.card_prod, card_units_int]
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hker)).trans hφle
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
