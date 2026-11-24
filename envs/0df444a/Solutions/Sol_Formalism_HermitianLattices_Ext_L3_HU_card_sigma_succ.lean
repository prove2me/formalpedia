-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.card_sigma_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:16.172085+00:00
-- url     : https://prove2.me/submissions/6a9a126d-b419-44df-9612-8ce3d0541256

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_card_skew_lift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_theta_inv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Hq_conjTranspose
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_skew_value
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_hermSub_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_card_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_surjective


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j) :
    Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) //
        Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = 0} =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) // Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} := by
  have hF : IsFixF K F := Fact.out
  have := finite_quot (K := K) h𝔭 (j + 1)
  have h1 := card_skew_lift (piQ K 𝔭 j) (piQ_surjective 𝔭 j) (piQ_star 𝔭 j) (Hq H 𝔭 (j + 1))
    (Hq_conjTranspose hH 𝔭 (j + 1)) (exists_skew_value hK h𝔭 hH hd hHE hj)
  have hmap : (Hq H 𝔭 (j + 1)).map (piQ K 𝔭 j) = Hq H 𝔭 j := by
    ext a b
    rfl
  rw [hmap] at h1
  obtain ⟨θ, u, hu⟩ := exists_theta_inv hK h𝔭 (j + 1)
  have hst : ∀ a ∈ RingHom.ker (piQ K 𝔭 j), star a ∈ RingHom.ker (piQ K 𝔭 j) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [piQ_star, ha, star_zero]
  have h2 := card_hermSub_sq (r := κ) hst hu
  have h3 : Nat.card (entSub κ κ (RingHom.ker (piQ K 𝔭 j))) =
      (Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2)) ^ 2 := by
    rw [card_entSub, card_ker_piQ hK hF h𝔭, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h3] at h2
  have h4 : Nat.card (hermSub κ (RingHom.ker (piQ K 𝔭 j))) = Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) :=
    Nat.pow_left_injective (n := 2) (by norm_num) h2
  rw [h3, h4] at h1
  have hpos : 0 < Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) := by
    apply pow_pos
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring
end Formalism.HermitianLattices.Ext.L3.HU
