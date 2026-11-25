-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsGA.selfadj_of_central_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:32.428951+00:00
-- url     : https://prove2.me/submissions/5bba9f45-9fcb-4e79-bde8-1a62f3d99a57

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_coeff
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_conjA
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_mul
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MonoidAlgebra
namespace Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
private theorem eq_zero_of_conjA_mul_self_eq_zero (x : MonoidAlgebra ℂ G) (hx : conjA x * x = 0) :
    x = 0 := by
  have h1 := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hx
  simp only [coeff_mul_fin, conjA_coeff, mul_one, MonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h1
  have h2 : ∑ h : G, ((Complex.normSq (x.coeff h⁻¹) : ℝ) : ℂ) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h2
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun h _ => Complex.normSq_nonneg (x.coeff h⁻¹))).mp h2
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have h4 := h3 g⁻¹ (Finset.mem_univ _)
  rw [inv_inv, Complex.normSq_eq_zero] at h4
  simpa using h4
private theorem eq_mul_of_commuting_idempotents_conjA_swap (e f : MonoidAlgebra ℂ G) (hef : conjA e = f)
    (hfe : conjA f = e) (he : e * e = e) (hf : f * f = f) (hc : f * e = e * f) :
    e = e * f := by
  have hx : conjA (e - e * f) * (e - e * f) = 0 := by
    rw [conjA_sub, conjA_mul, hef, hfe]
    have h1 : f * (e * f) = e * f := by rw [← mul_assoc, hc, mul_assoc, hf]
    have h2 : e * f * e = e * f := by rw [mul_assoc, hc, ← mul_assoc, he]
    have h3 : e * f * (e * f) = e * f := by rw [← mul_assoc, h2, mul_assoc, hf]
    rw [sub_mul, mul_sub, mul_sub, h1, h3, h2, hc]
    simp
  exact sub_eq_zero.mp (eq_zero_of_conjA_mul_self_eq_zero _ hx)
end Formalism.L2.SG.Pf.AllRowsGA
end
end

set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.SG.Pf.AllRowsGA
theorem _root_.solution (e : MonoidAlgebra ℂ G) (hid : e * e = e) (hc : ∀ y, e * y = y * e) :
    conjA e = e := by
  have hff : conjA e * conjA e = conjA e := by rw [← conjA_mul, hid]
  have h1 := eq_mul_of_commuting_idempotents_conjA_swap e (conjA e) rfl (conjA_conjA e) hid hff
    (hc (conjA e)).symm
  have h2 := eq_mul_of_commuting_idempotents_conjA_swap (conjA e) e (conjA_conjA e) rfl hff hid
    (hc (conjA e))
  calc conjA e = conjA e * e := h2
    _ = e * conjA e := (hc _).symm
    _ = e := h1.symm
end Formalism.L2.SG.Pf.AllRowsGA
