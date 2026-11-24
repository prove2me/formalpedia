-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:27:49.538911+00:00
-- url     : https://prove2.me/submissions/a1059f17-f53e-42c9-8364-92ea831e7cb9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
private theorem gA_H_eI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Hpk, Fin.ext_iff, h1, h2]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem gA_H_esI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Hpk, Fin.ext_iff, h1, h2]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem gA_herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec j) = (Hpk k r *ᵥ v) j := by
  simp only [herm, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [bvec]
  · intro i _ hij
    simp [bvec, hij]
  · intro h
    exact absurd (Finset.mem_univ j) h
private theorem gA_mv_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp [Matrix.mulVec, dotProduct, gA_H_eI]
private theorem gA_mv_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, gA_H_esI]
private theorem gA_inWb_iff (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r v ↔ ∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0 ∧
      herm (Hpk k r) v (bvec (esI k r a)) = 0 := by
  simp only [gA_herm_bvec, gA_mv_eI, gA_mv_esI]
  constructor
  · intro hv a
    have ha := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    exact ⟨hv _ (Or.inr (by omega)), hv _ (Or.inl (by omega))⟩
  · intro h i hi
    have hiv := i.isLt
    rcases hi with hi | hi
    · have e : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
      have := (h ⟨i.val, hi⟩).2
      rwa [e] at this
    · have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i :=
        Fin.ext (show 2 * r + k - (2 * r + k - i.val) = i.val by omega)
      have := (h ⟨2 * r + k - i.val, by omega⟩).1
      rwa [e] at this
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : inWb k r v) : inWb k r (g *ᵥ v) ∧ inWb k r (g⁻¹ *ᵥ v) := by
  have key : ∀ h ∈ Glev k r (Fin.last r), inWb k r (h *ᵥ v) := by
    intro h hh
    rw [gA_inWb_iff]
    intro a
    obtain ⟨h1, h2⟩ := hh.2 a a.isLt
    have hv' := (gA_inWb_iff v).1 hv a
    rw [← h1, ← h2, glev_herm hh, glev_herm hh]
    exact hv'
  obtain ⟨-, hHH, -, -⟩ := hpkFacts k r
  have hdet : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det hHH
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hl := (glev_unit hg).1
  have hinv : g⁻¹ ∈ Glev k r (Fin.last r) := by
    simp only [Glev, Set.mem_ofPred_eq]
    refine ⟨((uHGroup _ (Hpk k r) hdet).2.2 g hg.1).2, fun a ha => ?_⟩
    obtain ⟨h1, h2⟩ := hg.2 a ha
    constructor
    · calc g⁻¹ *ᵥ bvec (eI k r a) = g⁻¹ *ᵥ (g *ᵥ bvec (eI k r a)) := by rw [h1]
        _ = bvec (eI k r a) := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · calc g⁻¹ *ᵥ bvec (esI k r a) = g⁻¹ *ᵥ (g *ᵥ bvec (esI k r a)) := by rw [h2]
        _ = bvec (esI k r a) := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
  exact ⟨key g hg, key g⁻¹ hinv⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
