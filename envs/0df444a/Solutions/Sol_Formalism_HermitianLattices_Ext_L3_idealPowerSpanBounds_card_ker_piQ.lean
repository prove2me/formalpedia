-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.card_ker_piQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:24.797796+00:00
-- url     : https://prove2.me/submissions/3fffaf8b-fda4-4720-9274-769650e25b53

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_absNorm_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_piQ_surjective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Nat.card (RingHom.ker (piQ K 𝔭 k)) = Ideal.absNorm 𝔭 ^ 2 := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hA := absNorm_extP_pow hK hF h𝔭 (k + 1)
  have hB := absNorm_extP_pow hK hF h𝔭 k
  have hC : Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) =
      Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) :=
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (piQ_surjective (K := K) 𝔭 k)).toEquiv
  have hmul : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) = Nat.card (RingHom.ker (piQ K 𝔭 k)) *
      Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) := by
    first
    | exact Submodule.card_eq_card_quotient_mul_card _
    | (rw [mul_comm]; exact Submodule.card_eq_card_quotient_mul_card _)
    | (rw [mul_comm]; exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup)
    | exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup
  rw [hC, hA, hB] at hmul
  have hN : 0 < Ideal.absNorm 𝔭 ^ (2 * k) :=
    pow_pos (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)) _
  have e : Ideal.absNorm 𝔭 ^ (2 * (k + 1)) = Ideal.absNorm 𝔭 ^ 2 * Ideal.absNorm 𝔭 ^ (2 * k) := by
    ring
  rw [e] at hmul
  exact (Nat.eq_of_mul_eq_mul_right hN hmul).symm
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
