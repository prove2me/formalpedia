-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.inP_jK_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:44.038849+00:00
-- url     : https://prove2.me/submissions/ba33753f-78c3-49c9-82bb-4dafd25a6e6b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : 𝓞 K) :
    InP 𝔭 k (jK a) ↔ a ∈ extP K 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, hzt⟩
    have e1 : z = ι t * a := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hzt, map_mul]
    obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1 : 𝓞 F) i k
    have e0 : (1 : 𝓞 F) - i = y * t := by linear_combination -hyi
    rw [e0, one_pow] at hq
    have e2 : (1 : 𝓞 F) = i ^ k + y * t * q := by linear_combination hq
    have h1 := congrArg ι e2
    simp only [map_one, map_add, map_mul] at h1
    have e3 : a = ι (i ^ k) * a + ι y * ι q * (ι t * a) := by linear_combination a * h1
    rw [e3]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ (by rw [← e1]; exact hz))
    rw [map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
  · intro ha
    exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), a, ha, by simp⟩
end Formalism.HermitianLattices.Ext.L3.HU
