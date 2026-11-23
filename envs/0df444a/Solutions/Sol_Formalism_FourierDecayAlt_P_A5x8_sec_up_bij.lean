-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_up_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:15.455071+00:00
-- url     : https://prove2.me/submissions/480096d5-a013-4441-9737-548c03661de3

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_cX_outV
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_cX_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_surj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_int
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) :
    Function.Bijective (fun p : (upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) ×
        (Fin h.1.sum → KR R) =>
      ((sec_upJ h c p.1.out (outV R p.2) : upUniG K (addBlock h 1 c).1.sum) :
        upUniG K (addBlock h 1 c).1.sum ⧸ intSub R (upUniG K (addBlock h 1 c).1.sum))) := by
  have hJint : ∀ (b : upUniG K h.1.sum) (ρ : Fin h.1.sum → K), b ∈ intSub R (upUniG K h.1.sum) →
      (∀ j, ρ j ∈ R) → sec_upJ h c b ρ ∈ intSub R (upUniG K (addBlock h 1 c).1.sum) :=
    fun b ρ hb hρ => (sec_upJ_int R h c b ρ).2 ⟨hb, hρ⟩
  have hone : ∀ x : Fin h.1.sum → K, (sec_m (1 : upUniG K h.1.sum))⁻¹ *ᵥ x = x := by
    intro x
    simp [sec_m]
  refine sec_fib (A := upUniG K h.1.sum) (X := Fin h.1.sum → K)
    (G := upUniG K (addBlock h 1 c).1.sum) (cA := fun a => (a : upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum))) (oA := Quotient.out)
    (fun q => QuotientGroup.out_eq' q) (cX := sec_cX R) (oX := outV R) (sec_cX_outV R)
    (cG := fun g => (g : upUniG K (addBlock h 1 c).1.sum ⧸ intSub R (upUniG K (addBlock h 1 c).1.sum)))
    QuotientGroup.mk_surjective (fun (u : upUniG K h.1.sum) (η : Fin h.1.sum → K) => sec_upJ h c u η) (fun g => sec_upJ_surj h c g) ?_ ?_ ?_
  · intro a x a' x' hq
    obtain ⟨g, hg, e⟩ := (sec_left_eq _ _ _).1 hq
    obtain ⟨b, ρ, rfl⟩ := sec_upJ_surj h c g
    have hbρ := (sec_upJ_int R h c b ρ).1 hg
    rw [sec_upJ_mul] at e
    obtain ⟨e1, -⟩ := sec_upJ_inj h c e
    exact (sec_left_eq _ _ _).2 ⟨b, hbρ.1, e1⟩
  · intro a x x'
    constructor
    · intro hq
      obtain ⟨g, hg, e⟩ := (sec_left_eq _ _ _).1 hq
      obtain ⟨b, ρ, rfl⟩ := sec_upJ_surj h c g
      have hbρ := (sec_upJ_int R h c b ρ).1 hg
      rw [sec_upJ_mul] at e
      obtain ⟨e1, e2⟩ := sec_upJ_inj h c e
      have hb1 : b = 1 := by
        have h3 := congrArg (a⁻¹ * ·) e1
        simpa using h3.symm
      subst hb1
      rw [hone] at e2
      rw [sec_cX_eq]
      intro j
      rw [e2]
      simpa using hbρ.2 j
    · intro hx
      rw [sec_cX_eq] at hx
      apply (sec_left_eq _ _ _).2
      refine ⟨sec_upJ h c 1 (x' - x), hJint 1 _ (one_mem _) hx, ?_⟩
      show sec_upJ h c a x' = sec_upJ h c a x * sec_upJ h c 1 (x' - x)
      rw [sec_upJ_mul, mul_one, hone, sub_add_cancel]
  · intro a a' hq x
    obtain ⟨b, hb, e⟩ := (sec_left_eq _ _ _).1 hq
    refine ⟨(sec_m b)⁻¹ *ᵥ x, ?_⟩
    subst e
    apply (sec_left_eq _ _ _).2
    refine ⟨sec_upJ h c b 0, hJint b 0 hb (fun j => R.zero_mem), ?_⟩
    show sec_upJ h c (a * b) ((sec_m b)⁻¹ *ᵥ x) = sec_upJ h c a x * sec_upJ h c b 0
    rw [sec_upJ_mul, zero_add]
end Formalism.FourierDecayAlt.P.A5x8
