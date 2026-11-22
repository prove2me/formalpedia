-- Prove2me | solution 1 for Formalism.GM.TM.smith_qp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:24.312831+00:00
-- url     : https://prove2.me/submissions/3f2ba568-6d3e-4b77-9bb3-24964bcde8b4

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M Finset Matrix
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.TM
theorem _root_.solution (hS : SmithZp) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∃ (U V : Matrix (Fin n) (Fin n) ℚ_[p]) (dg : Fin n → ℚ_[p]),
      (∀ x y, ‖U x y‖ ≤ 1) ∧ (∀ x y, ‖V x y‖ ≤ 1) ∧ ‖U.det‖ = 1 ∧ ‖V.det‖ = 1 ∧
        A = U * Matrix.diagonal dg * V := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (∑ x, ∑ y, ‖A x y‖) hp
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hnorm : ∀ x y, ‖(p : ℚ_[p]) ^ k * A x y‖ ≤ 1 := by
    intro x y
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hpk, mul_one]
    have h1 : ‖A x y‖ ≤ ∑ y, ‖A x y‖ :=
      Finset.single_le_sum (f := fun y => ‖A x y‖) (fun _ _ => norm_nonneg _) (mem_univ y)
    have h2 : ∑ y, ‖A x y‖ ≤ ∑ x, ∑ y, ‖A x y‖ :=
      Finset.single_le_sum (f := fun x => ∑ y, ‖A x y‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (mem_univ x)
    linarith
  let A' : Matrix (Fin n) (Fin n) ℤ_[p] := fun x y => ⟨(p : ℚ_[p]) ^ k * A x y, hnorm x y⟩
  obtain ⟨U, V, d, hU, hV, hA⟩ := hS p n A'
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  have hmap : A'.map φ = ((p : ℚ_[p]) ^ k) • A := by
    ext x y; rfl
  have hmap2 : A'.map φ = U.map φ * Matrix.diagonal (fun i => φ (d i)) * V.map φ := by
    rw [hA, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  have hp0 : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine ⟨U.map φ, V.map φ, fun i => ((p : ℚ_[p]) ^ k)⁻¹ * φ (d i), fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
  · exact PadicInt.norm_le_one (U x y)
  · exact PadicInt.norm_le_one (V x y)
  · rw [show U.map φ = φ.mapMatrix U from rfl, ← RingHom.map_det]
    exact (PadicInt.isUnit_iff.mp hU)
  · rw [show V.map φ = φ.mapMatrix V from rfl, ← RingHom.map_det]
    exact (PadicInt.isUnit_iff.mp hV)
  · have : A = ((p : ℚ_[p]) ^ k)⁻¹ • (A'.map φ) := by
      rw [hmap, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    rw [this, hmap2]
    have hd : Matrix.diagonal (fun i => ((p : ℚ_[p]) ^ k)⁻¹ * φ (d i)) =
        ((p : ℚ_[p]) ^ k)⁻¹ • Matrix.diagonal (fun i => φ (d i)) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul]
end Formalism.GM.TM
