-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.emb_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:52:43.895028+00:00
-- url     : https://prove2.me/submissions/55222541-e929-4fd8-8688-4f947bc2af9f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_wI_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
private lemma fin_wI_sub_eq_self (q : Fin (k + 1)) (h : (wI k r q).val - r < k + 1) :
    (⟨(wI k r q).val - r, h⟩ : Fin (k + 1)) = q :=
  Fin.ext (by simp [wI])
private lemma sum_eq_sum_wI_of_eq_zero_off_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p, ¬ mid k r p → f p = 0) :
    ∑ p, f p = ∑ q : Fin (k + 1), f (wI k r q) := by
  have hinj : Function.Injective (wI k r) := fun a b h => by
    simpa [wI, Fin.ext_iff] using h
  calc ∑ p, f p = ∑ p ∈ Finset.univ.map ⟨wI k r, hinj⟩, f p := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro p _ hp
        apply hf
        intro hm
        apply hp
        rw [Finset.mem_map]
        refine ⟨⟨p.val - r, by have := hm.2; omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        have := hm.1
        show r + (p.val - r) = p.val
        omega
    _ = ∑ q : Fin (k + 1), f (wI k r q) := Finset.sum_map _ _ _
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
example (U : Set (Mt k r)) (hU : IsClosed U) : StandardBorelSpace U := hU.measurableSet.standardBorel
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas sgF_meas
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1 Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
theorem _root_.solution (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r (a * b) = embWb k r a * embWb k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ _ _ hi hj, Matrix.mul_apply, sum_eq_sum_wI_of_eq_zero_off_mid]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [emb_mid _ _ _ hi (wI_mid q), emb_mid _ _ _ (wI_mid q) hj]
        simp only [fin_wI_sub_eq_self]
      · intro p hp
        rw [emb_out_col a i p hp, if_neg (fun (h : i = p) => hp (h ▸ hi)), zero_mul]
    · simp [emb_out_col b _ _ hj]
      rw [emb_out_col _ _ _ hj, emb_out_col _ _ _ hj]
  · simp [emb_out_row a _ _ hi]
    rw [emb_out_row _ _ _ hi, emb_out_row _ _ _ hi]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
