-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.exists_solve_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:38.219539+00:00
-- url     : https://prove2.me/submissions/6c8255bd-4e31-402d-ba76-1e3f8f3087d9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_trace_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_tr_notMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_fill
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_trF_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_trF_spec
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c ≤ k) {z₀ : 𝓞 K} (hz : z₀ ∉ extP K 𝔭 ^ (c + 1)) {s : 𝓞 K}
    (hs : s ∈ extP K 𝔭 ^ k) (hs' : star s - s ∈ extP K 𝔭 ^ (k + 1)) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), z₀ * r + star (z₀ * r) - s ∈ extP K 𝔭 ^ (k + 1) := by
  obtain ⟨a, ha⟩ := exists_trace_one hK hF h𝔭 (k + 1)
  have has : a * s ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ a hs
  have hσ : trF hF (a * s) ∈ 𝔭 ^ k := trF_mem_pow hF 𝔭 k has
  have hσs : ι (trF hF (a * s)) - s ∈ extP K 𝔭 ^ (k + 1) := by
    rw [trF_spec, map_mul]
    have e : a * s + conjO K a * conjO K s - s =
        (a + star a - 1) * s + conjO K a * (star s - s) := by
      rw [idealPowerSpanBounds.star_def, idealPowerSpanBounds.star_def]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hs')
  obtain ⟨b, hb⟩ := exists_tr_notMem hK hF h𝔭 hz
  obtain ⟨r', hr', hfill⟩ := idealPowerSpanBounds.exists_fill h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hb hck hσ
  refine ⟨b * ι r', Ideal.mul_mem_left _ b ((mem_pow_iff 𝔭 (k - c) r').mpr hr'), ?_⟩
  have hlin : trF hF (z₀ * (b * ι r')) = r' * trF hF (b * z₀) := by
    have e : z₀ * (b * ι r') = r' • (b * z₀) := by
      rw [Algebra.smul_def]
      ring
    rw [e, map_smul, smul_eq_mul]
  have hsum : z₀ * (b * ι r') + star (z₀ * (b * ι r')) = ι (r' * trF hF (b * z₀)) := by
    rw [← hlin, trF_spec, idealPowerSpanBounds.star_def]
  rw [hsum]
  have e2 : ι (r' * trF hF (b * z₀)) - s =
      -ι (trF hF (a * s) - trF hF (b * z₀) * r') + (ι (trF hF (a * s)) - s) := by
    simp only [map_sub, map_mul]
    ring
  rw [e2]
  exact Ideal.add_mem _ (neg_mem ((mem_pow_iff 𝔭 (k + 1) _).mpr hfill)) hσs
end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
