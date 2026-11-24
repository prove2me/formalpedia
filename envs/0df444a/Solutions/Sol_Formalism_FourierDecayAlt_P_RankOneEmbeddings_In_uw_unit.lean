-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.uw_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:40:46.050339+00:00
-- url     : https://prove2.me/submissions/e1708c56-9eaa-4fa8-b091-a6bb693ffb8a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
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
private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [Hpk]
      split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
    · intro l _ hl
      have : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
      rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · have hp : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hp⟩]
    · simp only [Hpk]
      split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
    · intro l _ hl
      have : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
      rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution {z : Vc k r} {h : Mat k r} (hh : h ∈ UWset k r z) : IsUnit h.det := by
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hd : (Hpk k r).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h2
  exact hd h2.symm
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
