-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:37.147621+00:00
-- url     : https://prove2.me/submissions/ce385e23-bdb5-40b1-b9e0-818e2ba5b02f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
import Theorems.Thm_Formalism_L2_SG_Pf_LatEx_fi_neg_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution (c1 c2 a : 𝓕) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0) (ha : a ≠ 0) :
    ∃ α β γ δ : E, α ∈ a⁻¹ * c1 ∧ β ∈ a⁻¹ * c2 ∧ γ ∈ a * c2⁻¹ ∧ δ ∈ a * c1⁻¹ ∧
      α * δ - β * γ = 1 := by
  classical
  have hI0 : a⁻¹ * c1 ≠ 0 := mul_ne_zero (inv_ne_zero ha) h1
  have hJ0 : a⁻¹ * c2 ≠ 0 := mul_ne_zero (inv_ne_zero ha) h2
  obtain ⟨s, I0, hs, hIs⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (a⁻¹ * c1)⁻¹
  obtain ⟨t, J0, ht, hJt⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (a⁻¹ * c2)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  have ht' : algebraMap (𝓞 E) E t ≠ 0 := fun h => ht (hinj (by rw [h, map_zero]))
  have hI0c : (I0 : 𝓕) ≠ 0 := right_ne_zero_of_mul (hIs ▸ inv_ne_zero hI0)
  have hJ0c : (J0 : 𝓕) ≠ 0 := right_ne_zero_of_mul (hJt ▸ hJ0)
  have hI0b : I0 ≠ ⊥ := fun h => hI0c (by rw [h]; exact FractionalIdeal.coeIdeal_bot)
  have hIJ : I0 * J0 ≠ 0 := by
    intro h
    apply mul_ne_zero hI0c hJ0c
    rw [← FractionalIdeal.coeIdeal_mul, h]
    exact FractionalIdeal.coeIdeal_bot
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_right : I0 * J0 ≤ J0) hIJ
  have hgJ : g ∈ J0 := hg ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
  have hg' : (I0 : 𝓕) * (J0 : 𝓕) + FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g) = (J0 : 𝓕) := by
    rw [← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_sup, hg]
  have hsum : (I0 : 𝓕) + FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g) * (J0 : 𝓕)⁻¹ = 1 := by
    calc _ = ((I0 : 𝓕) * (J0 : 𝓕) + FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g)) * (J0 : 𝓕)⁻¹ := by
          rw [add_mul, mul_assoc, mul_inv_cancel₀ hJ0c, mul_one]
      _ = 1 := by rw [hg', mul_inv_cancel₀ hJ0c]
  have h1' : (1 : E) ∈ ((I0 : 𝓕) : Submodule (𝓞 E) E) ⊔
      ((FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g) * (J0 : 𝓕)⁻¹ : 𝓕) : Submodule (𝓞 E) E) := by
    rw [← Submodule.add_eq_sup, ← FractionalIdeal.coe_add, hsum]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1'
  obtain ⟨z', hz', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 (FractionalIdeal.mem_coe.1 hz)
  have e1 : algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E s)⁻¹ = 1 := mul_inv_cancel₀ hs'
  have e2 : (algebraMap (𝓞 E) E t)⁻¹ * algebraMap (𝓞 E) E t = 1 := inv_mul_cancel₀ ht'
  refine ⟨algebraMap (𝓞 E) E s, (algebraMap (𝓞 E) E t)⁻¹ * algebraMap (𝓞 E) E g,
    -(algebraMap (𝓞 E) E t * z'), (algebraMap (𝓞 E) E s)⁻¹ * y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← inv_inv (a⁻¹ * c1), hIs, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv,
      FractionalIdeal.mem_singleton_mul]
    exact ⟨1, FractionalIdeal.one_mem_inv_coe_ideal hI0b, (mul_one _).symm⟩
  · rw [hJt, FractionalIdeal.mem_singleton_mul]
    exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨g, hgJ, rfl⟩, rfl⟩
  · apply fi_neg_mem
    rw [show a * c2⁻¹ = (a⁻¹ * c2)⁻¹ by rw [mul_inv, inv_inv], hJt, mul_inv,
      FractionalIdeal.spanSingleton_inv, inv_inv, FractionalIdeal.mem_singleton_mul]
    exact ⟨z', hz', rfl⟩
  · rw [show a * c1⁻¹ = (a⁻¹ * c1)⁻¹ by rw [mul_inv, inv_inv], hIs, FractionalIdeal.mem_singleton_mul]
    exact ⟨y, FractionalIdeal.mem_coe.1 hy, rfl⟩
  · linear_combination hyz + y * e1 + algebraMap (𝓞 E) E g * z' * e2
end Formalism.L2.SG.Pf.LatEx
