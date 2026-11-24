-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_topWeightSing_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:07.886591+00:00
-- url     : https://prove2.me/submissions/c0faf882-03ec-4327-a8eb-ea2b17ca3431

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_hval_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_stabilizer
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hX : Qr.ExistsSingMax) (hS : Qr.CapSing) : Qr.TopWeightSing := by
  intro V _ _ _ n E m hE hm x hx hw
  refine ⟨hw, fun a b hab => ?_⟩
  by_contra hne
  have hstab := (capelli_stabilizer V n E m hE).1
  have hx' : E a b x ∈ CapSp E m := hstab a b x hx
  have hbot : CapSp E m ≠ ⊥ := fun h => hne (by rw [h] at hx'; exact (Submodule.mem_bot ℂ).1 hx')
  obtain ⟨ν, v, hv, hv0, hhw, hmax⟩ := hX V n E hE (CapSp E m) hstab hbot
  have hν := (hS V n E m hE hbot).2 hm ν v hv hv0 hhw
  have hwt : ∀ c, E c c (E a b x) = (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) • E a b x := by
    intro c
    have h := LinearMap.congr_fun (hE c c a b) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [hw c, map_smul, sub_eq_iff_eq_add] at h
    rw [h, hν c]
    by_cases h1 : c = a
    · subst h1
      have h2 : ¬ (b = c) := fun h => (ne_of_gt hab) h
      have h3 : ¬ (c = b) := fun h => h2 h.symm
      simp only [if_true, if_neg h2, if_neg h3, LinearMap.zero_apply]
      module
    · by_cases h2 : b = c
      · subst h2
        simp only [if_true, if_neg h1, LinearMap.zero_apply]
        module
      · have h3 : ¬ (c = b) := fun h => h2 h.symm
        simp only [if_neg h1, if_neg h2, if_neg h3, LinearMap.zero_apply]
        module
  have h := hmax _ (E a b x) hx' hne hwt
  rw [hval_shift] at h
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.2 (Fin.lt_def.1 hab)
  linarith
end Formalism.FourierDecayAlt.P
