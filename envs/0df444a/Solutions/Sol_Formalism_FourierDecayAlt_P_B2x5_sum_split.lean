-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:28:27.701914+00:00
-- url     : https://prove2.me/submissions/2659c11f-1833-44b3-8f5a-708dc8e81916

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_first_index_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ p, f p = f (i0 k r') + ∑ j, f (levPos k 1 r' j) + f (iL k r') := by
  have hinj : Function.Injective (levPos k 1 r') := fun a b h => by
    have := congrArg Fin.val h
    rw [lev_val, lev_val] at this
    exact Fin.ext (by omega)
  have h1 : i0 k r' ∉ insert (iL k r') (Finset.univ.image (levPos k 1 r')) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨fun h => ?_, fun j h => ?_⟩
    · have := congrArg Fin.val h
      rw [first_index_val, iL_val] at this
      omega
    · have := congrArg Fin.val h
      rw [first_index_val, lev_val] at this
      omega
  have h2 : iL k r' ∉ Finset.univ.image (levPos k 1 r') := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j h
    have := congrArg Fin.val h
    rw [iL_val, lev_val] at this
    have := j.isLt
    omega
  have huniv : (Finset.univ : Finset (Fin (2 * (1 + r') + k + 1))) =
      insert (i0 k r') (insert (iL k r') (Finset.univ.image (levPos k 1 r'))) := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_and, true_iff]
    have hp := p.isLt
    by_cases h0 : p.val = 0
    · exact Or.inl (Fin.ext h0)
    by_cases hL : p.val = 2 * r' + k + 2
    · exact Or.inr (Or.inl (Fin.ext (by rw [hL, iL_val])))
    · refine Or.inr (Or.inr ⟨⟨p.val - 1, by omega⟩, Fin.ext ?_⟩)
      rw [lev_val]
      show p.val - 1 + 1 = p.val
      omega
  rw [huniv, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_image (by intro a _ b _ h; exact hinj h)]
  ring
end Formalism.FourierDecayAlt.P.B2x5
