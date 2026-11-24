-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.exists_solve_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:51.648247+00:00
-- url     : https://prove2.me/submissions/e9c3844f-c859-48dc-a5fe-ae745a093bbc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_mul_entries_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_fillO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
theorem _root_.solution (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c + 1 ≤ k) {H X : Matrix m m (𝓞 K)} {D : 𝓞 F}
    (hD : H.det = ι D) (hDc : D ∉ 𝔭 ^ (c + 1)) (hX : ∀ i j, (Xᴴ * H * X - H) i j ∈ extP K 𝔭 ^ k)
    {W : Matrix m m (𝓞 K)} (hW : ∀ i j, W i j ∈ extP K 𝔭 ^ k) :
    ∃ Y : Matrix m m (𝓞 K), (∀ i j, Y i j ∈ extP K 𝔭 ^ (k - c)) ∧
      ∀ i j, (Xᴴ * H * Y - W) i j ∈ extP K 𝔭 ^ (k + 1) := by
  have hck' : c ≤ k := by omega
  have hfill := fun i j => exists_fillO (K := K) h𝔭 hDc hck' (hW i j)
  choose V hV hV' using hfill
  obtain ⟨R, hR⟩ : ∃ R : Matrix m m (𝓞 K), R = H.adjugate * Matrix.of V := ⟨_, rfl⟩
  have hRmem : ∀ i j, R i j ∈ extP K 𝔭 ^ (k - c) := by
    intro i j
    rw [hR]
    exact mul_entries_mem _ (fun a b => hV a b) i j
  refine ⟨X * R, fun i j => mul_entries_mem X hRmem i j, ?_⟩
  intro i j
  have e : Xᴴ * H * (X * R) - W = (Xᴴ * H * X - H) * R + (H * R - W) := by
    first
    | noncomm_ring
    | (simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel)
  have e1 : H * R = H.det • Matrix.of V := by
    rw [hR, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
  rw [e, Matrix.add_apply]
  refine Ideal.add_mem _ ?_ ?_
  · rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    have h1 : (Xᴴ * H * X - H) i l * R l j ∈ extP K 𝔭 ^ (k + (k - c)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hX i l) (hRmem l j)
    exact Ideal.pow_le_pow_right (by omega) h1
  · rw [Matrix.sub_apply, e1, Matrix.smul_apply, Matrix.of_apply, hD, smul_eq_mul]
    have h2 := neg_mem (hV' i j)
    rw [neg_sub] at h2
    exact h2
end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
