-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.ratio_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:32.446497+00:00
-- url     : https://prove2.me/submissions/337313b0-c203-43f4-b58c-b2e15f9dba25

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_antitone_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_u_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I
namespace Formalism.FourierDecayAlt.P.Interlace
theorem _root_.solution (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  set g : ℕ → ℝ := fun j => |Y + 1/2 + u j| * |Y + 1/2 + u' j| with hg
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  have hR : |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| =
      g l * ∏ i ∈ Icc 1 (k - 1), g (if i < l then i else i + 1) := by
    rw [abs_mul, abs_prod, abs_prod, ← prod_mul_distrib, ← mul_prod_erase _ _ hl]
    congr 1
    symm
    apply prod_nbij' (fun i => if i < l then i else i + 1) (fun j => if j < l then j else j - 1)
    · intro a ha
      simp only [mem_Icc] at ha
      simp only [mem_erase, mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      simp only [mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      rfl
  rw [hR, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold xpoly
  rw [← prod_pow]
  apply prod_le_prod
  · intro i _; positivity
  · intro i hi
    have hi' := mem_Icc.1 hi
    obtain ⟨a, b, c, d⟩ := h i hi
    simp only [hg]
    split_ifs with hil
    · have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      nlinarith
    · have h1 := hu l i hl1 (by omega) (by omega)
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      nlinarith
end Formalism.FourierDecayAlt.P.Interlace
