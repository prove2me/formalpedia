-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.card_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:59:37.288798+00:00
-- url     : https://prove2.me/submissions/5f01dac5-759b-4a40-9457-0155c1968183

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_card_unitary_reduction
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Cell_muQ_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_map_pow_le_span_sup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_of_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H)
    {j c : ℕ} (hcj : c ≤ j)
    (hu : ∀ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)),
      Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) → IsUnit X.det) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)) //
        Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c)} =
      Nat.card {X' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
          ∃ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)), Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) ∧
            X.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right j c))) = X'} *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ c) // Hq H 𝔭 c * Y + Yᴴ * Hq H 𝔭 c = 0} := by
  obtain ⟨d, hdj, hd⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot h𝔭) j)
  have hfin := finite_quot (K := K) h𝔭 (j + c)
  have hF : IsFixF K F := Fact.out
  have hHc : Hq H 𝔭 c = (Hq H 𝔭 (j + c)).map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left c j))) := by
    ext i l
    rfl
  rw [hHc]
  refine Cell.card_unitary_reduction _ _ (Cell.muQ (K := K) c hdj) ?_ ?_ ?_ ?_ ?_ _ hu
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Cell.muQ_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_of_mul_mem h𝔭 hd ha)
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (map_pow_le_span_sup h𝔭 hd (j + c) ha)
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      refine ⟨Ideal.Quotient.mk _ r, ?_⟩
      rw [Cell.muQ_mk, Ideal.Quotient.eq, ← e]
      have : algebraMap (𝓞 F) (𝓞 K) d * r - (r * algebraMap (𝓞 F) (𝓞 K) d + y) = -y := by ring
      rw [this]
      exact neg_mem hy
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Cell.muQ_mk, Ideal.Quotient.eq] at hy
      have h1 : algebraMap (𝓞 F) (𝓞 K) d * y ∈ extP K 𝔭 ^ j :=
        Ideal.mul_mem_right _ _ ((mem_pow_iff 𝔭 j d).2 hdj)
      have h2 : a = algebraMap (𝓞 F) (𝓞 K) d * y - (algebraMap (𝓞 F) (𝓞 K) d * y - a) := by ring
      rw [h2]
      exact sub_mem h1 (Ideal.pow_le_pow_right (Nat.le_add_right j c) hy)
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [star_mk, Cell.muQ_mk, Cell.muQ_mk, star_mk, star_mul', star_def (algebraMap (𝓞 F) (𝓞 K) d),
      conjO_map hF]
  · intro a y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.factor_mk, ← map_mul, Cell.muQ_mk, Cell.muQ_mk, ← map_mul]
    congr 1
    ring
  · intro y z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Cell.muQ_mk, Cell.muQ_mk, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.pow_le_pow_right (show j + c ≤ j + j by omega)
    rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ ((mem_pow_iff 𝔭 j d).2 hdj))
      (Ideal.mul_mem_right _ _ ((mem_pow_iff 𝔭 j d).2 hdj))
end Formalism.HermitianLattices.Ext.L3.HU
