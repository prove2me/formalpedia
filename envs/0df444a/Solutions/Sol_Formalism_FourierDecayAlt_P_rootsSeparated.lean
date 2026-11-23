-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rootsSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:29.108928+00:00
-- url     : https://prove2.me/submissions/1eba0667-8b06-4164-a568-887c9e62f8b9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_roots_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.RootsSeparated := by
  intro K _ _ _ R ψ hD _ s hs Q hQ hQu
  have := hD.t2
  have := hD.artin
  have := hD.red
  have hfin : {ζ : K | ζ ^ s = 1}.Finite := roots_finite s hs 1
  have hT : {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}.Finite := hfin.subset (fun ζ h => h.1)
  have hC : IsCompact (⋃ ζ ∈ {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}, (fun d => (1 - ζ) ^ s * d) '' Q) :=
    hT.isCompact_biUnion (fun ζ _ => hQ.image (continuous_const.mul continuous_id))
  have h0 : (0 : K) ∉ ⋃ ζ ∈ {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}, (fun d => (1 - ζ) ^ s * d) '' Q := by
    intro h
    simp only [Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨ζ, hζ, d, hd, h⟩ := h
    have h1 : (1 - ζ) ^ s = 0 := (hQu d hd).mul_left_eq_zero.1 h
    have h2 : 1 - ζ = 0 := IsNilpotent.eq_zero ⟨s, h1⟩
    exact hζ.2 (sub_eq_zero.1 h2).symm
  refine ⟨(fun w => w ^ s) ⁻¹'
    (⋃ ζ ∈ {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}, (fun d => (1 - ζ) ^ s * d) '' Q)ᶜ, ?_, ?_⟩
  · apply (hC.isClosed.isOpen_compl.preimage (continuous_pow s)).mem_nhds
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    rw [zero_pow (by omega)]
    exact h0
  · intro z z' hz hzz hV
    by_contra hne
    apply hV
    simp only [Set.mem_iUnion, Set.mem_image]
    refine ⟨((z' * z⁻¹ : Kˣ) : K), ⟨?_, ?_⟩, (z : K) ^ s, hz, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← hzz, mul_inv_cancel, Units.val_one]
    · intro h
      apply hne
      have h' : z' * z⁻¹ = 1 := Units.ext (by rw [h, Units.val_one])
      exact (mul_inv_eq_one.1 h').symm
    · rw [← mul_pow, sub_mul, one_mul, ← Units.val_mul, inv_mul_cancel_right]
end Formalism.FourierDecayAlt.P
