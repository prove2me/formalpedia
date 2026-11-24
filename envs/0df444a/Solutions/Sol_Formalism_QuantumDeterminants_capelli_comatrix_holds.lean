-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelli_comatrix_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:52:06.87072+00:00
-- url     : https://prove2.me/submissions/edb51325-03d3-40d6-97e8-2ce1200453c5

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_sum
import Theorems.Thm_Formalism_QuantumDeterminants_io_Tm_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_gl
import Theorems.Thm_Formalism_REAL_qComatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CapComatrix := by
  intro m ε E _ _ f u i l g hf hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hq := LinearMap.congr_fun
    (qComatrix (Module.End ℂ (ioS ε E)) m (ioE ε E) (io_gl ε E) u i l) x
  have hy : ∀ j : Fin (m + 1), IORep (qminorOp (EabV ε) (Fin.succAbove j) (Fin.succAbove i) u
      (Top (EabV ε) (u - (m : ℂ)) j l f))
      (qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x)).1 :=
    fun j => io_qminor_rep _ _ u (io_Tm_rep hx _ j l)
  have hs := io_rep_sum (fun j : Fin (m + 1) => ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)))) hy g hg
  have hc : (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x)) =
      (if i = l then qdet (ioE ε E) u else 0) x := by
    rw [← hq]
    simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.intCast_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Int.cast_smul_eq_zsmul ℂ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  calc (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        qminorOp (EabV ε) (Fin.succAbove j) (Fin.succAbove i) u (Top (EabV ε) (u - (m : ℂ)) j l f) g)
      = ((∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          qminor (ioE ε E) (Fin.succAbove j) (Fin.succAbove i) u (Tm (ioE ε E) (u - (m : ℂ)) j l x) :
          ioS ε E) : IOPt ε → E) ⟨g, hg⟩ := hs
    _ = (((if i = l then qdet (ioE ε E) u else 0) x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩ := by rw [hc]
    _ = if i = l then capelli ε u f g else 0 := by
      split_ifs with h
      · exact (io_qminor_rep id id u hx g hg).symm
      · rfl
end Formalism.QuantumDeterminants
