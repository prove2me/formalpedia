-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.mul_mem_isotropic_unipotent_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:12.958448+00:00
-- url     : https://prove2.me/submissions/04617b73-daef-4561-a37f-56208c8ee788

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_NFOne_sg_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val
attribute [local simp] NFOne.sg_val


section
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
section N2
variable {k r : ℕ}
private theorem mul_mem_n0set {z' : Fin (2 * r + k + 1) → ℂ}
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ N0set k r z') (hh : h ∈ N0set k r z') :
    g * h ∈ N0set k r z' := by
  obtain ⟨gU, gX, gz, gW, gS⟩ := hg
  obtain ⟨hU, hX, hz, hW, hS⟩ := hh

  have col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0 := by
    intro p m hm
    have := congrFun (gX ⟨m.val, hm⟩) p
    simpa [bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val →
      ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) →
      ∀ m, g p m * h m q = if m = q then g p q else 0 := by
    intro p q hp hq m
    have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hm1 : m.val < r
    · rw [col p m hm1, if_neg (fun e => by rw [e] at hp; omega), zero_mul,
        if_neg (fun e => by rw [e] at hm1; omega)]
    · have tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0 := by
        intro hmq
        by_cases e : m = q
        · subst e; simp [hmq]
        · simp [hmq, e]
      by_cases hm2 : m.val ≤ r + k
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · rw [gW p m (by omega) hm2 hp, if_neg (fun e => by rw [e] at hp2; omega), zero_mul,
            if_neg (fun e => by rw [e] at hm2; omega)]
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · exact tail (hS m q hq1 (by omega))
  refine ⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · change (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    change gᴴ * Hpk k r * g = Hpk k r at gU
    change hᴴ * Hpk k r * h = Hpk k r at hU
    rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [Matrix.mul_assoc], gU, hU]
  · rw [← Matrix.mulVec_mulVec, hX, gX]
  · rw [← Matrix.mulVec_mulVec, hz, gz]
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gW p q hq1 hq2 hp
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gS p q hq hp
end N2
end
end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (z' : Fin (2 * r + k + 1) → ℂ) (j1 j2 : ℕ) (V1 V2 : ℕ → Fin (2 * r + k + 1) → ℂ)
    (h1 : (1 + NFOne.Pm k r j1 V1) ∈ N0set k r z') (h2 : (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z') :
    (1 + NFOne.Pm k r j1 V1) * (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z' := by
  exact mul_mem_n0set h1 h2
end Formalism.FourierDecayAlt.P.SignAntidiagonal
